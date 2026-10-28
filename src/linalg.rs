//! Dense double-double LU with partial pivoting (LAPACK getf2 order), column-major with the leading dimension
//! padded to a multiple of 8 so the trailing update runs on 8-row lane vectors, columns updated in parallel (rayon)
//! for large matrices; the same factorization blocked in plain f64 (LAPACK's right-looking getrf) for
//! mixed-precision use, solves and transpose solves in double-double with either set of factors, solves refined to
//! quad-double (`DDLu::solve_refine_qd`), Gram matrices, and the same unblocked LU in quad-double (`QDLu`) for systems
//! too ill-conditioned for double-double.
use crate::dd::{pow2_near, two_prod, two_sum, DD};
use crate::dv::{self, DotAcc, DV};
use crate::qd::QD;
use crate::qv::QV;
use crate::simd::{self, Kernel, Simd};
use crate::v8::{M8, V8};
use rayon::prelude::*;

#[derive(Clone)]
pub struct DDLu {
    pub n: usize,
    pub ld: usize,
    pub hi: Vec<f64>,
    pub lo: Vec<f64>,
    pub perm: Vec<usize>,
}

#[inline(always)]
pub fn ld_for(n: usize) -> usize {
    n.div_ceil(8) * 8
}

/// a - l t on 8 rows (l, a lane vectors; t scalar), as one DD product added with an error-free sum
#[inline(always)]
fn axpy8<S: Simd>(a: DV<S>, l: DV<S>, nt: DV<S>) -> DV<S> {
    let (p, pe) = dv::two_prod(l.hi, nt.hi);
    let pe = l.hi.fma(nt.lo, pe);
    let pe = l.lo.fma(nt.hi, pe);
    let (s, t) = dv::two_sum(a.hi, p);
    let e = a.lo.add(t.add(pe));
    let (h, lo) = dv::two_sum(s, e);
    DV { hi: h, lo }
}

/// a + l t in double-double, as the LU's updates and solves form it: one double-double product (the hi x hi product
/// exact, the cross terms by FMA, lo x lo dropped) added to a with an error-free sum. Public for code that works on
/// these factors itself (a block LU's solves) and must round as the solves here do.
#[inline(always)]
pub fn dd_axpy(a: DD, l: DD, nt: DD) -> DD {
    let (p, pe) = two_prod(l.hi, nt.hi);
    let pe = l.hi.mul_add(nt.lo, pe);
    let pe = l.lo.mul_add(nt.hi, pe);
    let (s, t) = two_sum(a.hi, p);
    let e = a.lo + (t + pe);
    let (h, lo) = two_sum(s, e);
    DD { hi: h, lo }
}

/// the lanes of rows i0..i0 + 8 that lie in lo..hi
#[inline(always)]
fn rows_in<S: Simd>(i0: usize, lo: usize, hi: usize) -> M8<S> {
    let idx = V8::<S>::from_array(std::array::from_fn(|r| (i0 + r) as f64));
    idx.ge(V8::splat(lo as f64)).and(V8::splat(hi as f64).gt(idx))
}

/// u where m is set, a elsewhere
#[inline(always)]
fn sel_dv<S: Simd>(m: M8<S>, u: DV<S>, a: DV<S>) -> DV<S> {
    DV {
        hi: m.sel(u.hi, a.hi),
        lo: m.sel(u.lo, a.lo),
    }
}

/// b[i] = dd_axpy(b[i], l[i], nt) for i in lo..hi, on the 8-row blocks that meet lo..hi; rows outside keep their value
/// (bitwise the scalar loop). l's low parts are ll, or zero when None. Every slice holds hi rounded up to 8 rows.
#[inline(always)]
fn axpy_rows<S: Simd>(bh: &mut [f64], bl: &mut [f64], lh: &[f64], ll: Option<&[f64]>, lo: usize, hi: usize, nt: DD) {
    let t = DV::<S>::splat(nt);
    let mut i = 8 * (lo / 8);
    while i < hi {
        let a = DV::load(&bh[i..i + 8], &bl[i..i + 8]);
        let l = DV {
            hi: V8::load(&lh[i..i + 8]),
            lo: ll.map_or(V8::zero(), |x| V8::load(&x[i..i + 8])),
        };
        let u = axpy8(a, l, t);
        let u = if i >= lo && i + 8 <= hi {
            u
        } else {
            sel_dv(rows_in::<S>(i, lo, hi), u, a)
        };
        u.store(&mut bh[i..i + 8], &mut bl[i..i + 8]);
        i += 8;
    }
}

/// b[i] = l[i] t + b[i] (one rounding, as `f64::mul_add`) for i in lo..hi, as `axpy_rows` in f64
#[inline(always)]
fn fma_rows<S: Simd>(b: &mut [f64], l: &[f64], lo: usize, hi: usize, t: f64) {
    let tv = V8::<S>::splat(t);
    let mut i = 8 * (lo / 8);
    while i < hi {
        let a = V8::load(&b[i..i + 8]);
        let u = V8::load(&l[i..i + 8]).fma(tv, a);
        let u = if i >= lo && i + 8 <= hi {
            u
        } else {
            rows_in::<S>(i, lo, hi).sel(u, a)
        };
        u.store(&mut b[i..i + 8]);
        i += 8;
    }
}

/// The pivot of column col (rows k..n, col holding n rounded up to 8): the first row with the largest |col[i]| and
/// that value, as the scalar search `if |col[i]| > best` from best = |col[k]| finds them: a NaN never wins, and a NaN
/// at row k leaves k with best NaN. 8 rows at a time, each lane keeping its first maximum; then the largest value
/// over the lanes, at the smallest row.
#[inline(always)]
fn pivot_search<S: Simd>(col: &[f64], k: usize, n: usize) -> (usize, f64) {
    let a = col[k].abs();
    if a.is_nan() {
        return (k, a);
    }
    let none = V8::<S>::splat(-1.0);
    let (mut best, mut at) = (none, V8::<S>::splat(k as f64));
    let mut i = 8 * (k / 8);
    // the row numbers of the block, as f64 (exact), stepped by 8
    let mut idx = V8::<S>::from_array(std::array::from_fn(|r| (i + r) as f64));
    let (step, kv, nv) = (V8::<S>::splat(8.0), V8::<S>::splat(k as f64), V8::<S>::splat(n as f64));
    while i < n {
        let x = V8::load(&col[i..i + 8]).abs();
        let v = if i >= k && i + 8 <= n {
            x
        } else {
            idx.ge(kv).and(nv.gt(idx)).sel(x, none)
        };
        let up = v.gt(best);
        best = up.sel(v, best);
        at = up.sel(idx, at);
        idx = idx.add(step);
        i += 8;
    }
    let (b, x) = (best.to_array(), at.to_array());
    let (mut p, mut m) = (usize::MAX, -1.0f64);
    for r in 0..8 {
        if b[r] > m || (b[r] == m && (x[r] as usize) < p) {
            m = b[r];
            p = x[r] as usize;
        }
    }
    (p, m)
}

/// d[i] = q[i].to_dd(), 8 entries at a time (`QV::to_dv`), the remainder scalar
#[inline(always)]
fn to_dd_lanes<S: Simd>(q: &[QD], d: &mut [DD]) {
    let full = q.len() / 8 * 8;
    for i in (0..full).step_by(8) {
        let v = QV::<S>::from_lanes(q[i..i + 8].try_into().unwrap()).to_dv();
        let (h, l) = (v.hi.to_array(), v.lo.to_array());
        for r in 0..8 {
            d[i + r] = DD { hi: h[r], lo: l[r] };
        }
    }
    for i in full..q.len() {
        d[i] = q[i].to_dd();
    }
}

/// x[i] = x[i] + QD::from_dd(d[i]), 8 entries at a time (`QV + QV`), the remainder scalar
#[inline(always)]
fn add_dd_lanes<S: Simd>(x: &mut [QD], d: &[DD]) {
    let full = x.len() / 8 * 8;
    for i in (0..full).step_by(8) {
        let dv = DV::<S> {
            hi: V8::from_array(std::array::from_fn(|r| d[i + r].hi)),
            lo: V8::from_array(std::array::from_fn(|r| d[i + r].lo)),
        };
        let s = QV::<S>::from_lanes(x[i..i + 8].try_into().unwrap()) + QV::from_dv(dv);
        x[i..i + 8].copy_from_slice(&s.lanes());
    }
    for i in full..x.len() {
        x[i] = x[i] + QD::from_dd(d[i]);
    }
}

/// Blocked LU: matrices at least this large take `factor_blocked`; NB: panel width; CW: columns per parallel task;
/// NC: columns per register tile.
pub const BLOCKED_MIN: usize = 96;
const NB: usize = 32;
const CW: usize = 8;
const NC: usize = 4;
const TR: usize = 2;

/// getf2 on the panel columns j0..j0+jb (slices ph / pl hold just those columns, leading dimension ld): pivot search,
/// row swaps within the panel, scaling, and updates of the later panel columns, as `factor_unblocked` does them,
/// except that updates which cannot change a value are skipped: 8-row blocks whose multipliers are all exactly zero,
/// and columns whose pivot-row entry is exactly zero (a - 0 t and a - l 0 return a; at most the sign of a zero differs).
fn panel_getf2<S: Simd>(
    n: usize,
    ld: usize,
    j0: usize,
    jb: usize,
    ph: &mut [f64],
    pl: &mut [f64],
    perm: &mut [usize],
) -> Result<(), String> {
    S::vectorize(
        #[inline(always)]
        move || {
            let mut mh = vec![0.0f64; ld];
            let mut ml = vec![0.0f64; ld];
            let mut blocks: Vec<usize> = Vec::with_capacity(ld / 8);
            for c in 0..jb {
                let k = j0 + c;
                let ck = c * ld;
                let (p, best) = pivot_search::<S>(&ph[ck..ck + ld], k, n);
                if best == 0.0 || !best.is_finite() {
                    return Err(format!("singular or non-finite pivot at column {k} ({best})"));
                }
                perm[k] = p;
                if p != k {
                    for j in 0..jb {
                        ph.swap(j * ld + k, j * ld + p);
                        pl.swap(j * ld + k, j * ld + p);
                    }
                }
                let inv = DD::ONE
                    / DD {
                        hi: ph[ck + k],
                        lo: pl[ck + k],
                    };
                // the multipliers, 8 rows at a time; zero entries are left as they are
                let iv = DV::<S>::splat(inv);
                let z = V8::<S>::zero();
                let mut i = 8 * ((k + 1) / 8);
                while i < n {
                    let (h, l) = (&mut ph[ck + i..ck + i + 8], &mut pl[ck + i..ck + i + 8]);
                    let x = DV::load(h, l);
                    let m = rows_in::<S>(i, k + 1, n).and(x.hi.eq(z).and(x.lo.eq(z)).not());
                    sel_dv(m, x * iv, x).store(h, l);
                    i += 8;
                }
                if k + 1 == n || c + 1 == jb {
                    continue;
                }
                let r0 = 8 * ((k + 1) / 8);
                blocks.clear();
                let mut i = r0;
                while i < ld {
                    let mut nz = false;
                    for r in i..i + 8 {
                        if r > k && r < n {
                            mh[r] = ph[ck + r];
                            ml[r] = pl[ck + r];
                        } else {
                            mh[r] = 0.0;
                            ml[r] = 0.0;
                        }
                        nz |= mh[r] != 0.0 || ml[r] != 0.0;
                    }
                    if nz {
                        blocks.push(i);
                    }
                    i += 8;
                }
                if blocks.is_empty() {
                    continue;
                }
                let (_, rh) = ph.split_at_mut((c + 1) * ld);
                let (_, rl) = pl.split_at_mut((c + 1) * ld);
                let w = jb - c - 1;
                for (ch, cl) in rh[..w * ld].chunks_mut(ld).zip(rl[..w * ld].chunks_mut(ld)) {
                    if ch[k] == 0.0 && cl[k] == 0.0 {
                        continue;
                    }
                    let nt = DV::<S>::splat(DD { hi: -ch[k], lo: -cl[k] });
                    for &i in &blocks {
                        let a = DV::load(&ch[i..i + 8], &cl[i..i + 8]);
                        let l = DV::load(&mh[i..i + 8], &ml[i..i + 8]);
                        axpy8(a, l, nt).store(&mut ch[i..i + 8], &mut cl[i..i + 8]);
                    }
                }
            }
            Ok(())
        },
    )
}

/// The trailing update of one panel on the given columns (offsets into ch / cl, leading dimension ld) and 8-row blocks
/// (row offsets): entry -= l_ik u_kj for the panel's k in order, with TR row blocks x NC columns in registers.
/// nt[j]: offset of column j's -u values (jb each) in nth / ntl; ph / pl: packed multipliers, [row block][k][lane].
#[allow(clippy::too_many_arguments)]
fn gemm<S: Simd>(
    ld: usize,
    jb: usize,
    ch: &mut [f64],
    cl: &mut [f64],
    cols: &[usize],
    nto: &[usize],
    nth: &[f64],
    ntl: &[f64],
    rows: &[(usize, usize)],
    ph: &[f64],
    pl: &[f64],
) {
    S::vectorize(
        #[inline(always)]
        move || {
            let mut j = 0;
            while j < cols.len() {
                let w = (cols.len() - j).min(NC);
                let mut r = 0;
                while r < rows.len() {
                    let h = (rows.len() - r).min(TR);
                    match (h, w) {
                        (TR, NC) => {
                            tile_rows::<S, TR, NC>(ld, jb, ch, cl, &cols[j..], &nto[j..], nth, ntl, &rows[r..], ph, pl)
                        }
                        (1, NC) => {
                            tile_rows::<S, 1, NC>(ld, jb, ch, cl, &cols[j..], &nto[j..], nth, ntl, &rows[r..], ph, pl)
                        }
                        (TR, _) => {
                            for q in 0..w {
                                tile_rows::<S, TR, 1>(
                                    ld,
                                    jb,
                                    ch,
                                    cl,
                                    &cols[j + q..],
                                    &nto[j + q..],
                                    nth,
                                    ntl,
                                    &rows[r..],
                                    ph,
                                    pl,
                                )
                            }
                        }
                        _ => {
                            for q in 0..w {
                                tile_rows::<S, 1, 1>(
                                    ld,
                                    jb,
                                    ch,
                                    cl,
                                    &cols[j + q..],
                                    &nto[j + q..],
                                    nth,
                                    ntl,
                                    &rows[r..],
                                    ph,
                                    pl,
                                )
                            }
                        }
                    }
                    r += h;
                }
                j += w;
            }
        },
    )
}

#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn tile_rows<S: Simd, const R: usize, const W: usize>(
    ld: usize,
    jb: usize,
    ch: &mut [f64],
    cl: &mut [f64],
    cols: &[usize],
    nto: &[usize],
    nth: &[f64],
    ntl: &[f64],
    rows: &[(usize, usize)],
    ph: &[f64],
    pl: &[f64],
) {
    let _ = ld;
    let mut acc = [[DV::<S>::zero(); W]; R];
    for r in 0..R {
        let i = rows[r].0;
        for q in 0..W {
            let o = cols[q] + i;
            acc[r][q] = DV::load(&ch[o..o + 8], &cl[o..o + 8]);
        }
    }
    for c in 0..jb {
        let mut l = [DV::zero(); R];
        for r in 0..R {
            let pb = rows[r].1 + c * 8;
            l[r] = DV::load(&ph[pb..pb + 8], &pl[pb..pb + 8]);
        }
        for q in 0..W {
            let nt = DV::splat(DD {
                hi: nth[nto[q] + c],
                lo: ntl[nto[q] + c],
            });
            for r in 0..R {
                acc[r][q] = axpy8(acc[r][q], l[r], nt);
            }
        }
    }
    for r in 0..R {
        let i = rows[r].0;
        for q in 0..W {
            let o = cols[q] + i;
            acc[r][q].store(&mut ch[o..o + 8], &mut cl[o..o + 8]);
        }
    }
}

impl DDLu {
    /// Factor the n x n matrix given column-major with leading dimension ld (ld % 8 == 0, padding rows zero).
    /// par: work in parallel (rayon's current pool). Large matrices take the blocked path (`factor_blocked`), which
    /// gives bitwise the same factors as the unblocked one.
    pub fn factor(n: usize, ld: usize, hi: Vec<f64>, lo: Vec<f64>, par: bool) -> Result<DDLu, String> {
        if n >= BLOCKED_MIN {
            Self::factor_blocked(n, ld, hi, lo, par)
        } else {
            Self::factor_unblocked(n, ld, hi, lo, par)
        }
    }

    /// LAPACK getf2 order: for each column k, pivot, scale, and update all trailing columns (in parallel if par).
    pub fn factor_unblocked(n: usize, ld: usize, hi: Vec<f64>, lo: Vec<f64>, par: bool) -> Result<DDLu, String> {
        simd::dispatch(FactorUnblocked { n, ld, hi, lo, par })
    }

    fn factor_unblocked_on<S: Simd>(
        n: usize,
        ld: usize,
        mut hi: Vec<f64>,
        mut lo: Vec<f64>,
        par: bool,
    ) -> Result<DDLu, String> {
        S::vectorize(
            #[inline(always)]
            move || {
                assert!(ld.is_multiple_of(8) && ld >= n && hi.len() >= ld * n && lo.len() >= ld * n);
                let mut perm = vec![0usize; n];
                let mut mh = vec![0.0f64; ld];
                let mut ml = vec![0.0f64; ld];
                for k in 0..n {
                    let ck = k * ld;
                    let (p, best) = pivot_search::<S>(&hi[ck..ck + ld], k, n);
                    if best == 0.0 || !best.is_finite() {
                        return Err(format!("singular or non-finite pivot at column {k} ({best})"));
                    }
                    perm[k] = p;
                    if p != k {
                        for j in 0..n {
                            hi.swap(j * ld + k, j * ld + p);
                            lo.swap(j * ld + k, j * ld + p);
                        }
                    }
                    let inv = DD::ONE
                        / DD {
                            hi: hi[ck + k],
                            lo: lo[ck + k],
                        };
                    let iv = DV::<S>::splat(inv);
                    let mut i = 8 * ((k + 1) / 8);
                    while i < n {
                        let (h, l) = (&mut hi[ck + i..ck + i + 8], &mut lo[ck + i..ck + i + 8]);
                        let x = DV::load(h, l);
                        sel_dv(rows_in::<S>(i, k + 1, n), x * iv, x).store(h, l);
                        i += 8;
                    }
                    if k + 1 == n {
                        break;
                    }
                    let r0 = 8 * ((k + 1) / 8);
                    for i in r0..ld {
                        if i > k && i < n {
                            mh[i] = hi[ck + i];
                            ml[i] = lo[ck + i];
                        } else {
                            mh[i] = 0.0;
                            ml[i] = 0.0;
                        }
                    }
                    let (_, rh) = hi.split_at_mut((k + 1) * ld);
                    let (_, rl) = lo.split_at_mut((k + 1) * ld);
                    let ncols = n - k - 1;
                    let upd = |(ch, cl): (&mut [f64], &mut [f64])| {
                        S::vectorize(
                            #[inline(always)]
                            || {
                                let nt = DV::<S>::splat(DD { hi: -ch[k], lo: -cl[k] });
                                let mut i = r0;
                                while i < ld {
                                    let a = DV::load(&ch[i..i + 8], &cl[i..i + 8]);
                                    let l = DV::load(&mh[i..i + 8], &ml[i..i + 8]);
                                    axpy8(a, l, nt).store(&mut ch[i..i + 8], &mut cl[i..i + 8]);
                                    i += 8;
                                }
                            },
                        )
                    };
                    if par && ncols * (ld - r0) > 32768 {
                        rh[..ncols * ld]
                            .par_chunks_mut(ld)
                            .zip(rl[..ncols * ld].par_chunks_mut(ld))
                            .for_each(upd);
                    } else {
                        rh[..ncols * ld]
                            .chunks_mut(ld)
                            .zip(rl[..ncols * ld].chunks_mut(ld))
                            .for_each(upd);
                    }
                }
                Ok(DDLu { n, ld, hi, lo, perm })
            },
        )
    }

    /// Blocked right-looking LU (panel width NB) that applies to every entry the operations of `factor_unblocked`, in
    /// the same order, except those that cannot change a value: updates with an exactly zero multiplier block (8 rows)
    /// or an exactly zero pivot-row entry (a - 0 t and a - l 0 return a; at most the sign of a zero differs). The
    /// factors and pivots are therefore identical in value to getf2's (bitwise apart from the signs of zeros), and the
    /// zero blocks of the multiple-shooting Jacobian cost nothing. Per panel of columns j0..je:
    ///  1. the panel is factored as in getf2 (pivot search, row swaps and updates restricted to the panel);
    ///  2. every column left of the panel gets the panel's row swaps, in order;
    ///  3. every column right of the panel gets the swaps, then the panel's updates k = j0, j0 + 1, ... in order:
    ///     rows above je one k at a time (a unit-lower triangular solve), rows below je on register tiles with the
    ///     k loop innermost, so each entry is loaded and stored once per panel instead of once per k (getf2 sweeps the
    ///     whole trailing matrix through memory for every k).
    ///
    /// Step 3 runs in parallel over chunks of CW columns when par.
    pub fn factor_blocked(n: usize, ld: usize, hi: Vec<f64>, lo: Vec<f64>, par: bool) -> Result<DDLu, String> {
        simd::dispatch(FactorBlocked { n, ld, hi, lo, par })
    }

    fn factor_blocked_on<S: Simd>(
        n: usize,
        ld: usize,
        mut hi: Vec<f64>,
        mut lo: Vec<f64>,
        par: bool,
    ) -> Result<DDLu, String> {
        S::vectorize(
            #[inline(always)]
            move || {
                assert!(ld.is_multiple_of(8) && ld >= n && hi.len() >= ld * n && lo.len() >= ld * n);
                let mut perm = vec![0usize; n];
                let mut j0 = 0;
                while j0 < n {
                    let jb = NB.min(n - j0);
                    let je = j0 + jb;
                    let (left_h, rest_h) = hi.split_at_mut(j0 * ld);
                    let (left_l, rest_l) = lo.split_at_mut(j0 * ld);
                    let (pan_h, right_h) = rest_h.split_at_mut(jb * ld);
                    let (pan_l, right_l) = rest_l.split_at_mut(jb * ld);
                    panel_getf2::<S>(n, ld, j0, jb, pan_h, pan_l, &mut perm)?;
                    let pv = &perm[j0..je];
                    // 2. swaps left of the panel
                    for (ch, cl) in left_h.chunks_mut(ld).zip(left_l.chunks_mut(ld)) {
                        for (c, &p) in pv.iter().enumerate() {
                            if p != j0 + c {
                                ch.swap(j0 + c, p);
                                cl.swap(j0 + c, p);
                            }
                        }
                    }
                    if je == n {
                        break;
                    }
                    // 3. multipliers: rows j0..je for the triangular part (zero for rows <= k, as getf2's mh), rows je..ld
                    //    packed as [row block][k][lane] for the tiles (zero for padding rows >= n)
                    let pan_h: &[f64] = pan_h;
                    let pan_l: &[f64] = pan_l;
                    let mut th = vec![0.0f64; jb * jb];
                    let mut tl = vec![0.0f64; jb * jb];
                    for c in 0..jb {
                        for i in j0 + c + 1..je.min(n) {
                            th[c * jb + i - j0] = pan_h[c * ld + i];
                            tl[c * jb + i - j0] = pan_l[c * ld + i];
                        }
                    }
                    let nrb = (ld - je) / 8;
                    let mut ph = vec![0.0f64; nrb * jb * 8];
                    let mut pl = vec![0.0f64; nrb * jb * 8];
                    // row blocks with a nonzero multiplier: (row offset, packed offset)
                    let mut rows: Vec<(usize, usize)> = Vec::with_capacity(nrb);
                    for rb in 0..nrb {
                        let mut nz = false;
                        for c in 0..jb {
                            for r in 0..8 {
                                let i = je + rb * 8 + r;
                                if i < n {
                                    let (x, y) = (pan_h[c * ld + i], pan_l[c * ld + i]);
                                    ph[(rb * jb + c) * 8 + r] = x;
                                    pl[(rb * jb + c) * 8 + r] = y;
                                    nz |= x != 0.0 || y != 0.0;
                                }
                            }
                        }
                        if nz {
                            rows.push((je + rb * 8, rb * jb * 8));
                        }
                    }
                    let ncols = n - je;
                    let task = |(ch, cl): (&mut [f64], &mut [f64])| {
                        S::vectorize(
                            #[inline(always)]
                            || {
                                let w = ch.len() / ld;
                                // nt[j]: -(entry (j0 + c, column j)) as read at step k = j0 + c (as getf2 reads it)
                                let mut nth = vec![0.0f64; w * jb];
                                let mut ntl = vec![0.0f64; w * jb];
                                let mut cols: Vec<usize> = Vec::with_capacity(w);
                                let mut nto: Vec<usize> = Vec::with_capacity(w);
                                for j in 0..w {
                                    let (h, l) = (&mut ch[j * ld..(j + 1) * ld], &mut cl[j * ld..(j + 1) * ld]);
                                    for (c, &p) in pv.iter().enumerate() {
                                        if p != j0 + c {
                                            h.swap(j0 + c, p);
                                            l.swap(j0 + c, p);
                                        }
                                    }
                                    // a column that is zero on the panel's rows stays zero there (U12 = 0) and gets no update
                                    if h[j0..je].iter().all(|&x| x == 0.0) && l[j0..je].iter().all(|&x| x == 0.0) {
                                        continue;
                                    }
                                    for c in 0..jb {
                                        let k = j0 + c;
                                        let (a, b) = (-h[k], -l[k]);
                                        nth[j * jb + c] = a;
                                        ntl[j * jb + c] = b;
                                        if a == 0.0 && b == 0.0 {
                                            continue;
                                        }
                                        let nt = DV::<S>::splat(DD { hi: a, lo: b });
                                        let mut i = 8 * ((k + 1) / 8);
                                        while i < je {
                                            let x = DV::load(&h[i..i + 8], &l[i..i + 8]);
                                            let m = DV::load(
                                                &th[c * jb + i - j0..c * jb + i - j0 + 8],
                                                &tl[c * jb + i - j0..c * jb + i - j0 + 8],
                                            );
                                            axpy8(x, m, nt).store(&mut h[i..i + 8], &mut l[i..i + 8]);
                                            i += 8;
                                        }
                                    }
                                    if nth[j * jb..(j + 1) * jb].iter().any(|&x| x != 0.0)
                                        || ntl[j * jb..(j + 1) * jb].iter().any(|&x| x != 0.0)
                                    {
                                        cols.push(j * ld);
                                        nto.push(j * jb);
                                    }
                                }
                                if !rows.is_empty() {
                                    gemm::<S>(ld, jb, ch, cl, &cols, &nto, &nth, &ntl, &rows, &ph, &pl);
                                }
                            },
                        )
                    };
                    let (rh, rl) = (&mut right_h[..ncols * ld], &mut right_l[..ncols * ld]);
                    if par && ncols * (ld - j0) > 16384 {
                        rh.par_chunks_mut(CW * ld)
                            .zip(rl.par_chunks_mut(CW * ld))
                            .for_each(task);
                    } else {
                        rh.chunks_mut(CW * ld).zip(rl.chunks_mut(CW * ld)).for_each(task);
                    }
                    j0 = je;
                }
                Ok(DDLu { n, ld, hi, lo, perm })
            },
        )
    }

    /// Solve A x = b (transpose: A^T x = b) for nrhs right-hand sides at once, b row-major (nrhs, n) as (hi, lo),
    /// in place. Eight right-hand sides share each lane vector, and the groups of eight run in parallel when par.
    /// Each lane does exactly the operations of `solve` / `solve_t`, so every row of the result is bitwise the
    /// single right-hand-side solve.
    pub fn solve_many(&self, bh: &mut [f64], bl: &mut [f64], nrhs: usize, transpose: bool, par: bool) {
        simd::dispatch(SolveMany {
            lu: self,
            bh,
            bl,
            nrhs,
            transpose,
            par,
        })
    }

    fn solve_many_on<S: Simd>(&self, bh: &mut [f64], bl: &mut [f64], nrhs: usize, transpose: bool, par: bool) {
        S::vectorize(
            #[inline(always)]
            move || {
                let n = self.n;
                assert!(bh.len() >= nrhs * n && bl.len() >= nrhs * n);
                let ng = nrhs.div_ceil(8);
                let (bh0, bl0): (&[f64], &[f64]) = (bh, bl);
                let rg = self.col_ranges();
                let rg = &rg;
                let group = |g: usize| -> Vec<DV<S>> {
                    S::vectorize(
                        #[inline(always)]
                        || {
                            let live = (nrhs - 8 * g).min(8);
                            let mut v = vec![DV::<S>::zero(); n];
                            let mut h = [0.0f64; 8];
                            let mut l = [0.0f64; 8];
                            for (i, vi) in v.iter_mut().enumerate() {
                                for r in 0..live {
                                    h[r] = bh0[(8 * g + r) * n + i];
                                    l[r] = bl0[(8 * g + r) * n + i];
                                }
                                *vi = DV {
                                    hi: V8::from_array(h),
                                    lo: V8::from_array(l),
                                };
                            }
                            if transpose {
                                self.solve_t_dv(&mut v, rg);
                            } else {
                                self.solve_dv(&mut v, rg);
                            }
                            v
                        },
                    )
                };
                let out: Vec<Vec<DV<S>>> = if par && ng > 1 {
                    (0..ng).into_par_iter().map(group).collect()
                } else {
                    (0..ng).map(group).collect()
                };
                for (g, v) in out.iter().enumerate() {
                    let live = (nrhs - 8 * g).min(8);
                    for (i, vi) in v.iter().enumerate() {
                        let (h, l) = (vi.hi.to_array(), vi.lo.to_array());
                        for r in 0..live {
                            bh[(8 * g + r) * n + i] = h[r];
                            bl[(8 * g + r) * n + i] = l[r];
                        }
                    }
                }
            },
        )
    }

    /// For each column of the factors, the first and one past the last row holding a nonzero entry. Entries outside
    /// are exact zeros, whose updates (a - 0 t = a) the lane solves skip; the rest run in the scalar solves' order.
    fn col_ranges(&self) -> Vec<(usize, usize)> {
        (0..self.n)
            .map(|k| {
                let (h, l) = (
                    &self.hi[k * self.ld..k * self.ld + self.n],
                    &self.lo[k * self.ld..k * self.ld + self.n],
                );
                let nz = |i: &usize| h[*i] != 0.0 || l[*i] != 0.0;
                let a = (0..self.n).find(nz).unwrap_or(k);
                let b = (0..self.n).rev().find(nz).map_or(k + 1, |i| i + 1);
                (a, b)
            })
            .collect()
    }

    /// `solve` lane by lane (padding lanes hold zeros and stay zero).
    fn solve_dv<S: Simd>(&self, b: &mut [DV<S>], rg: &[(usize, usize)]) {
        S::vectorize(
            #[inline(always)]
            move || {
                let n = self.n;
                for k in 0..n {
                    let p = self.perm[k];
                    if p != k {
                        b.swap(k, p);
                    }
                }
                for k in 0..n {
                    let nt = -b[k];
                    // the lanes whose -y_k has a nonzero leading part; the scalar solve skips the others
                    let live = nt.hi.ne(V8::zero());
                    if live.bits() == 0 {
                        continue;
                    }
                    let all = live.bits() == 0xff;
                    let col = k * self.ld;
                    for i in (k + 1).max(rg[k].0)..rg[k].1.max(k + 1) {
                        let u = axpy8(
                            b[i],
                            DV::splat(DD {
                                hi: self.hi[col + i],
                                lo: self.lo[col + i],
                            }),
                            nt,
                        );
                        b[i] = if all { u } else { sel_dv(live, u, b[i]) };
                    }
                }
                for k in (0..n).rev() {
                    let q = b[k] / DV::splat(self.at(k, k));
                    b[k] = q;
                    let nt = -q;
                    let col = k * self.ld;
                    for i in rg[k].0.min(k)..rg[k].1.min(k) {
                        b[i] = axpy8(
                            b[i],
                            DV::splat(DD {
                                hi: self.hi[col + i],
                                lo: self.lo[col + i],
                            }),
                            nt,
                        );
                    }
                }
            },
        )
    }

    /// `solve_t` lane by lane.
    fn solve_t_dv<S: Simd>(&self, b: &mut [DV<S>], rg: &[(usize, usize)]) {
        S::vectorize(
            #[inline(always)]
            move || {
                let n = self.n;
                let mut nb = vec![DV::<S>::zero(); n];
                for k in 0..n {
                    let col = k * self.ld;
                    let mut acc = b[k];
                    for i in rg[k].0.min(k)..rg[k].1.min(k) {
                        acc = axpy8(
                            acc,
                            DV::splat(DD {
                                hi: self.hi[col + i],
                                lo: self.lo[col + i],
                            }),
                            nb[i],
                        );
                    }
                    b[k] = acc / DV::splat(self.at(k, k));
                    nb[k] = -b[k];
                }
                for k in (0..n).rev() {
                    let col = k * self.ld;
                    let mut acc = b[k];
                    for i in (k + 1).max(rg[k].0)..rg[k].1.max(k + 1) {
                        acc = axpy8(
                            acc,
                            DV::splat(DD {
                                hi: self.hi[col + i],
                                lo: self.lo[col + i],
                            }),
                            nb[i],
                        );
                    }
                    b[k] = acc;
                    nb[k] = -acc;
                }
                for k in (0..n).rev() {
                    let p = self.perm[k];
                    if p != k {
                        b.swap(k, p);
                    }
                }
            },
        )
    }

    #[inline(always)]
    fn at(&self, i: usize, j: usize) -> DD {
        DD {
            hi: self.hi[j * self.ld + i],
            lo: self.lo[j * self.ld + i],
        }
    }

    /// Solve A x = b in place (b: n values): the row swaps, L y = b column by column (skipping columns whose y_k is
    /// zero), then U x = y, each column's update of the rows below (or above) 8 rows at a time on the backend
    /// `simd::dispatch` picks, every entry with the operations and order of the scalar loops.
    pub fn solve(&self, b: &mut [DD]) {
        simd::dispatch(Solve { lu: self, b })
    }

    fn solve_on<S: Simd>(&self, b: &mut [DD]) {
        S::vectorize(
            #[inline(always)]
            move || {
                let (n, ld) = (self.n, self.ld);
                assert!(b.len() >= n);
                for k in 0..n {
                    let p = self.perm[k];
                    if p != k {
                        b.swap(k, p);
                    }
                }
                let (mut bh, mut bl) = (vec![0.0f64; ld], vec![0.0f64; ld]);
                for i in 0..n {
                    bh[i] = b[i].hi;
                    bl[i] = b[i].lo;
                }
                for k in 0..n {
                    let nt = -DD { hi: bh[k], lo: bl[k] };
                    if nt.hi == 0.0 {
                        continue;
                    }
                    let col = k * ld..(k + 1) * ld;
                    axpy_rows::<S>(
                        &mut bh,
                        &mut bl,
                        &self.hi[col.clone()],
                        Some(&self.lo[col]),
                        k + 1,
                        n,
                        nt,
                    );
                }
                for k in (0..n).rev() {
                    let q = DD { hi: bh[k], lo: bl[k] } / self.at(k, k);
                    (bh[k], bl[k]) = (q.hi, q.lo);
                    let col = k * ld..(k + 1) * ld;
                    axpy_rows::<S>(&mut bh, &mut bl, &self.hi[col.clone()], Some(&self.lo[col]), 0, k, -q);
                }
                for i in 0..n {
                    b[i] = DD { hi: bh[i], lo: bl[i] };
                }
            },
        )
    }

    /// x with A x = b to quad-double accuracy, by iterative refinement with the residual in quad-double (Moler, J.
    /// ACM 14 (1967) 316, doi:10.1145/321386.321394). This is the LU of A or of a double-double approximation of
    /// it (A rounded, or A at a nearby point); `resid(x, r)` writes r = b - A x in quad-double for the caller's own
    /// A and b. x starts as the solve of b rounded to double-double, and each of the `steps` steps adds the solve of
    /// r rounded to double-double, the sum in quad-double: with the LU of A to double-double each step multiplies
    /// the error by about cond(A) 2^-104, so two steps reach quad-double where cond(A) is below about 10^10.
    /// The conversions and sums run 8 entries at a time on `QV` lanes (`QV::to_dv`, `QV + QV`), bitwise the scalar
    /// `QD::to_dd` and `QD + QD`.
    pub fn solve_refine_qd(&self, b: &[QD], steps: usize, resid: impl FnMut(&[QD], &mut [QD])) -> Vec<QD> {
        simd::dispatch(RefineQd {
            lu: self,
            b,
            steps,
            resid,
        })
    }

    fn solve_refine_qd_on<S: Simd>(&self, b: &[QD], steps: usize, mut resid: impl FnMut(&[QD], &mut [QD])) -> Vec<QD> {
        S::vectorize(
            #[inline(always)]
            move || {
                let n = self.n;
                assert_eq!(b.len(), n, "solve_refine_qd: b must have n entries");
                let mut d = vec![DD::ZERO; n];
                to_dd_lanes::<S>(b, &mut d);
                self.solve_on::<S>(&mut d);
                let mut x: Vec<QD> = d.iter().map(|&v| QD::from_dd(v)).collect();
                let mut r = vec![QD::ZERO; n];
                for _ in 0..steps {
                    resid(&x, &mut r);
                    to_dd_lanes::<S>(&r, &mut d);
                    self.solve_on::<S>(&mut d);
                    add_dd_lanes::<S>(&mut x, &d);
                }
                x
            },
        )
    }

    /// Solve A^T y = b in place. With P A = L U (P the recorded row swaps): U^T w = b, L^T v = w, y = P^T v.
    pub fn solve_t(&self, b: &mut [DD]) {
        let n = self.n;
        for k in 0..n {
            let mut acc = b[k];
            for i in 0..k {
                acc = dd_axpy(acc, self.at(i, k), -b[i]);
            }
            b[k] = acc / self.at(k, k);
        }
        for k in (0..n).rev() {
            let mut acc = b[k];
            for i in k + 1..n {
                acc = dd_axpy(acc, self.at(i, k), -b[i]);
            }
            b[k] = acc;
        }
        for k in (0..n).rev() {
            let p = self.perm[k];
            if p != k {
                b.swap(k, p);
            }
        }
    }

    /// Solve A x = b in plain f64 with the hi parts of the factors (an f64 LU of A, accurate to about one ulp of its
    /// entries), for the f64 lanes of the mixed-precision Jacobian.
    pub fn solve_hi(&self, b: &mut [f64]) {
        simd::dispatch(SolveHi { lu: self, b })
    }

    fn solve_hi_on<S: Simd>(&self, b: &mut [f64]) {
        S::vectorize(
            #[inline(always)]
            move || {
                let (n, ld) = (self.n, self.ld);
                assert!(b.len() >= n);
                for k in 0..n {
                    let p = self.perm[k];
                    if p != k {
                        b.swap(k, p);
                    }
                }
                let mut v = vec![0.0f64; ld];
                v[..n].copy_from_slice(&b[..n]);
                for k in 0..n {
                    let nt = -v[k];
                    if nt == 0.0 {
                        continue;
                    }
                    fma_rows::<S>(&mut v, &self.hi[k * ld..(k + 1) * ld], k + 1, n, nt);
                }
                for k in (0..n).rev() {
                    v[k] /= self.hi[k * ld + k];
                    let nt = -v[k];
                    fma_rows::<S>(&mut v, &self.hi[k * ld..(k + 1) * ld], 0, k, nt);
                }
                b[..n].copy_from_slice(&v[..n]);
            },
        )
    }

    /// (sign, ln|det|) of the factored matrix: product of the pivots u_kk, sign flipped per row interchange.
    pub fn logdet(&self) -> (f64, f64) {
        let mut sign = 1.0f64;
        let mut la = 0.0f64;
        for k in 0..self.n {
            let u = self.at(k, k);
            let v = u.hi + u.lo;
            if v < 0.0 {
                sign = -sign;
            }
            la += v.abs().ln();
            if self.perm[k] != k {
                sign = -sign;
            }
        }
        (sign, la)
    }

    /// min and max |u_kk| (hi parts)
    pub fn pivot_range(&self) -> (f64, f64) {
        let mut lo = f64::INFINITY;
        let mut hi = 0.0f64;
        for k in 0..self.n {
            let v = self.hi[k * self.ld + k].abs();
            lo = lo.min(v);
            hi = hi.max(v);
        }
        (lo, hi)
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The same blocked LU in plain f64, for the mixed-precision Newton step (an f64 Jacobian)
// ---------------------------------------------------------------------------------------------------------------

/// `panel_getf2` in f64 (one array; multipliers by the pivot's reciprocal, as LAPACK's dgetf2).
fn panel_getf2_f64<S: Simd>(
    n: usize,
    ld: usize,
    j0: usize,
    jb: usize,
    pa: &mut [f64],
    perm: &mut [usize],
) -> Result<(), String> {
    S::vectorize(
        #[inline(always)]
        move || {
            let mut m = vec![0.0f64; ld];
            let mut blocks: Vec<usize> = Vec::with_capacity(ld / 8);
            for c in 0..jb {
                let k = j0 + c;
                let ck = c * ld;
                let (p, best) = pivot_search::<S>(&pa[ck..ck + ld], k, n);
                if best == 0.0 || !best.is_finite() {
                    return Err(format!("singular or non-finite pivot at column {k} ({best})"));
                }
                perm[k] = p;
                if p != k {
                    for j in 0..jb {
                        pa.swap(j * ld + k, j * ld + p);
                    }
                }
                let inv = V8::<S>::splat(1.0 / pa[ck + k]);
                let mut i = 8 * ((k + 1) / 8);
                while i < n {
                    let x = V8::load(&pa[ck + i..ck + i + 8]);
                    rows_in::<S>(i, k + 1, n)
                        .sel(x.mul(inv), x)
                        .store(&mut pa[ck + i..ck + i + 8]);
                    i += 8;
                }
                if k + 1 == n || c + 1 == jb {
                    continue;
                }
                let r0 = 8 * ((k + 1) / 8);
                blocks.clear();
                let mut i = r0;
                while i < ld {
                    let mut nz = false;
                    for r in i..i + 8 {
                        m[r] = if r > k && r < n { pa[ck + r] } else { 0.0 };
                        nz |= m[r] != 0.0;
                    }
                    if nz {
                        blocks.push(i);
                    }
                    i += 8;
                }
                if blocks.is_empty() {
                    continue;
                }
                let (_, ra) = pa.split_at_mut((c + 1) * ld);
                let w = jb - c - 1;
                for ch in ra[..w * ld].chunks_mut(ld) {
                    if ch[k] == 0.0 {
                        continue;
                    }
                    let nt = V8::<S>::splat(-ch[k]);
                    for &i in &blocks {
                        V8::load(&m[i..i + 8])
                            .fma(nt, V8::load(&ch[i..i + 8]))
                            .store(&mut ch[i..i + 8]);
                    }
                }
            }
            Ok(())
        },
    )
}

#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn tile_rows_f64<S: Simd, const R: usize, const W: usize>(
    ch: &mut [f64],
    cols: &[usize],
    nto: &[usize],
    nt: &[f64],
    rows: &[(usize, usize)],
    pk: &[f64],
    jb: usize,
) {
    let mut acc = [[V8::<S>::zero(); W]; R];
    for r in 0..R {
        for q in 0..W {
            let o = cols[q] + rows[r].0;
            acc[r][q] = V8::load(&ch[o..o + 8]);
        }
    }
    for c in 0..jb {
        let mut l = [V8::zero(); R];
        for r in 0..R {
            let pb = rows[r].1 + c * 8;
            l[r] = V8::load(&pk[pb..pb + 8]);
        }
        for q in 0..W {
            let t = V8::splat(nt[nto[q] + c]);
            for r in 0..R {
                acc[r][q] = l[r].fma(t, acc[r][q]);
            }
        }
    }
    for r in 0..R {
        for q in 0..W {
            let o = cols[q] + rows[r].0;
            acc[r][q].store(&mut ch[o..o + 8]);
        }
    }
}

/// `gemm` in f64 (4 row blocks x NC columns per register tile)
fn gemm_f64<S: Simd>(
    jb: usize,
    ch: &mut [f64],
    cols: &[usize],
    nto: &[usize],
    nt: &[f64],
    rows: &[(usize, usize)],
    pk: &[f64],
) {
    const TR64: usize = 4;
    S::vectorize(
        #[inline(always)]
        move || {
            let mut j = 0;
            while j < cols.len() {
                let w = (cols.len() - j).min(NC);
                let mut r = 0;
                while r < rows.len() {
                    let h = (rows.len() - r).min(TR64);
                    if w == NC && h == TR64 {
                        tile_rows_f64::<S, TR64, NC>(ch, &cols[j..], &nto[j..], nt, &rows[r..], pk, jb);
                    } else {
                        for q in 0..w {
                            for rr in 0..h {
                                tile_rows_f64::<S, 1, 1>(
                                    ch,
                                    &cols[j + q..],
                                    &nto[j + q..],
                                    nt,
                                    &rows[r + rr..],
                                    pk,
                                    jb,
                                );
                            }
                        }
                    }
                    r += h;
                }
                j += w;
            }
        },
    )
}

impl DDLu {
    /// The blocked LU of `factor_blocked` (the same panels, row swaps, skipped zero blocks and register tiles) in plain
    /// f64 on an f64 matrix: an f64 LU with partial pivoting (backward stable: L U = P (A + E), |E| of the order of
    /// n eps |L| |U|), stored with lo = 0 so that the double-double solves (solve, solve_t, solve_many, chord) use these
    /// factors as they are. For the mixed-precision Newton step, whose Jacobian is f64 to begin with.
    pub fn factor_f64(n: usize, ld: usize, a: Vec<f64>, par: bool) -> Result<DDLu, String> {
        simd::dispatch(FactorF64 { n, ld, a, par })
    }

    fn factor_f64_on<S: Simd>(n: usize, ld: usize, mut a: Vec<f64>, par: bool) -> Result<DDLu, String> {
        S::vectorize(
            #[inline(always)]
            move || {
                assert!(ld.is_multiple_of(8) && ld >= n && a.len() >= ld * n);
                let mut perm = vec![0usize; n];
                let mut j0 = 0;
                while j0 < n {
                    let jb = NB.min(n - j0);
                    let je = j0 + jb;
                    let (left, rest) = a.split_at_mut(j0 * ld);
                    let (pan, right) = rest.split_at_mut(jb * ld);
                    panel_getf2_f64::<S>(n, ld, j0, jb, pan, &mut perm)?;
                    let pv = &perm[j0..je];
                    for ch in left.chunks_mut(ld) {
                        for (c, &p) in pv.iter().enumerate() {
                            if p != j0 + c {
                                ch.swap(j0 + c, p);
                            }
                        }
                    }
                    if je == n {
                        break;
                    }
                    let pan: &[f64] = pan;
                    let mut tri = vec![0.0f64; jb * jb];
                    for c in 0..jb {
                        for i in j0 + c + 1..je.min(n) {
                            tri[c * jb + i - j0] = pan[c * ld + i];
                        }
                    }
                    let nrb = (ld - je) / 8;
                    let mut pk = vec![0.0f64; nrb * jb * 8];
                    let mut rows: Vec<(usize, usize)> = Vec::with_capacity(nrb);
                    for rb in 0..nrb {
                        let mut nz = false;
                        for c in 0..jb {
                            for r in 0..8 {
                                let i = je + rb * 8 + r;
                                if i < n {
                                    let x = pan[c * ld + i];
                                    pk[(rb * jb + c) * 8 + r] = x;
                                    nz |= x != 0.0;
                                }
                            }
                        }
                        if nz {
                            rows.push((je + rb * 8, rb * jb * 8));
                        }
                    }
                    let ncols = n - je;
                    let task = |ch: &mut [f64]| {
                        S::vectorize(
                            #[inline(always)]
                            || {
                                let w = ch.len() / ld;
                                let mut nt = vec![0.0f64; w * jb];
                                let mut cols: Vec<usize> = Vec::with_capacity(w);
                                let mut nto: Vec<usize> = Vec::with_capacity(w);
                                for j in 0..w {
                                    let h = &mut ch[j * ld..(j + 1) * ld];
                                    for (c, &p) in pv.iter().enumerate() {
                                        if p != j0 + c {
                                            h.swap(j0 + c, p);
                                        }
                                    }
                                    if h[j0..je].iter().all(|&x| x == 0.0) {
                                        continue;
                                    }
                                    for c in 0..jb {
                                        let k = j0 + c;
                                        let t = -h[k];
                                        nt[j * jb + c] = t;
                                        if t == 0.0 {
                                            continue;
                                        }
                                        let tv = V8::<S>::splat(t);
                                        let mut i = 8 * ((k + 1) / 8);
                                        while i < je {
                                            let mv = V8::load(&tri[c * jb + i - j0..c * jb + i - j0 + 8]);
                                            mv.fma(tv, V8::load(&h[i..i + 8])).store(&mut h[i..i + 8]);
                                            i += 8;
                                        }
                                    }
                                    if nt[j * jb..(j + 1) * jb].iter().any(|&x| x != 0.0) {
                                        cols.push(j * ld);
                                        nto.push(j * jb);
                                    }
                                }
                                if !rows.is_empty() {
                                    gemm_f64::<S>(jb, ch, &cols, &nto, &nt, &rows, &pk);
                                }
                            },
                        )
                    };
                    let r = &mut right[..ncols * ld];
                    if par && ncols * (ld - j0) > 16384 {
                        r.par_chunks_mut(CW * ld).for_each(task);
                    } else {
                        r.chunks_mut(CW * ld).for_each(task);
                    }
                    j0 = je;
                }
                let lo = vec![0.0; a.len()];
                Ok(DDLu { n, ld, hi: a, lo, perm })
            },
        )
    }
}

/// Partial-pivoting LU, in place, of the first `np` columns of an `nr` x `ncol` f64 matrix: the step of a block
/// (staircase) LU that factors one group of columns and passes the Schur complement on to the next, where the square
/// [`DDLu::factor_f64`] does not apply.
///
/// `a` is column-major with leading dimension `ld` (a multiple of 8, at least `nr`), with rows `nr..ld` zero.
/// Afterwards rows `0..np` of the first `np` columns hold U11 and the rows below them the multipliers L21 (unit lower
/// triangular L11 above them); rows `0..np` of the columns `np..ncol` hold U12, and rows `np..nr` of those columns the
/// Schur complement A22 - L21 U12. `perm[k]` (`k < np`) is the row swapped with row `k` at step `k`, and every swap is
/// applied to all `ncol` columns. The panels, row swaps, skipped zero blocks, register tiles and parallel column
/// chunks are those of `factor_f64`, on the backend [`simd::dispatch`] picks, bitwise the same on every backend. The
/// triangular update inside a panel runs row by row from the pivot down, where `factor_f64` uses aligned 8-row
/// blocks, which can turn a -0 above the pivot into +0: with `nr = ncol = np` the factors equal `factor_f64`'s except
/// possibly in the sign of zero entries.
pub fn lu_rect_f64(
    nr: usize,
    ncol: usize,
    np: usize,
    ld: usize,
    a: &mut [f64],
    perm: &mut [usize],
    par: bool,
) -> Result<(), String> {
    simd::dispatch(LuRectF64 {
        nr,
        ncol,
        np,
        ld,
        a,
        perm,
        par,
    })
}

fn lu_rect_f64_on<S: Simd>(
    nr: usize,
    ncol: usize,
    np: usize,
    ld: usize,
    a: &mut [f64],
    perm: &mut [usize],
    par: bool,
) -> Result<(), String> {
    S::vectorize(
        #[inline(always)]
        move || {
            assert!(
                ld.is_multiple_of(8) && ld >= nr && np <= nr && np <= ncol && a.len() >= ld * ncol && perm.len() >= np
            );
            let mut j0 = 0;
            while j0 < np {
                let jb = NB.min(np - j0);
                let je = j0 + jb;
                let (left, rest) = a.split_at_mut(j0 * ld);
                let (pan, right) = rest.split_at_mut(jb * ld);
                panel_getf2_f64::<S>(nr, ld, j0, jb, pan, perm)?;
                let pv = &perm[j0..je];
                for ch in left.chunks_mut(ld) {
                    for (c, &p) in pv.iter().enumerate() {
                        if p != j0 + c {
                            ch.swap(j0 + c, p);
                        }
                    }
                }
                if je == ncol {
                    break;
                }
                let pan: &[f64] = pan;
                // the multipliers packed by 8-row blocks from the aligned row r0 below je for the tiles (zero for rows
                // < je, which the triangular update takes from the panel, and for rows >= nr)
                let r0 = 8 * (je / 8);
                let nrb = (ld - r0) / 8;
                let mut pk = vec![0.0f64; nrb * jb * 8];
                let mut rows: Vec<(usize, usize)> = Vec::with_capacity(nrb);
                for rb in 0..nrb {
                    let mut nz = false;
                    for c in 0..jb {
                        for r in 0..8 {
                            let i = r0 + rb * 8 + r;
                            if i >= je && i < nr {
                                let x = pan[c * ld + i];
                                pk[(rb * jb + c) * 8 + r] = x;
                                nz |= x != 0.0;
                            }
                        }
                    }
                    if nz {
                        rows.push((r0 + rb * 8, rb * jb * 8));
                    }
                }
                let task = |ch: &mut [f64]| {
                    S::vectorize(
                        #[inline(always)]
                        || {
                            let w = ch.len() / ld;
                            let mut nt = vec![0.0f64; w * jb];
                            let mut cols: Vec<usize> = Vec::with_capacity(w);
                            let mut nto: Vec<usize> = Vec::with_capacity(w);
                            for j in 0..w {
                                let h = &mut ch[j * ld..(j + 1) * ld];
                                for (c, &p) in pv.iter().enumerate() {
                                    if p != j0 + c {
                                        h.swap(j0 + c, p);
                                    }
                                }
                                if h[j0..je].iter().all(|&x| x == 0.0) {
                                    continue;
                                }
                                for c in 0..jb {
                                    let k = j0 + c;
                                    let t = -h[k];
                                    nt[j * jb + c] = t;
                                    if t == 0.0 {
                                        continue;
                                    }
                                    fma_rows::<S>(h, &pan[c * ld..(c + 1) * ld], k + 1, je, t);
                                }
                                if nt[j * jb..(j + 1) * jb].iter().any(|&x| x != 0.0) {
                                    cols.push(j * ld);
                                    nto.push(j * jb);
                                }
                            }
                            if !rows.is_empty() {
                                gemm_f64::<S>(jb, ch, &cols, &nto, &nt, &rows, &pk);
                            }
                        },
                    )
                };
                let ncr = ncol - je;
                let r = &mut right[..ncr * ld];
                if par && ncr * (ld - j0) > 16384 {
                    r.par_chunks_mut(CW * ld).for_each(task);
                } else {
                    r.chunks_mut(CW * ld).for_each(task);
                }
                j0 = je;
            }
            Ok(())
        },
    )
}

/// Gram matrix G = J^T J and g = J^T b for a column-major J (n x n, leading dimension ld): G column-major with
/// leading dimension ld (only what LU needs; G is symmetric and filled completely).
pub fn gram(n: usize, ld: usize, jh: &[f64], jl: &[f64], bh: &[f64], bl: &[f64]) -> (Vec<f64>, Vec<f64>, Vec<DD>) {
    simd::dispatch(Gram { n, ld, jh, jl, bh, bl })
}

fn gram_on<S: Simd>(
    n: usize,
    ld: usize,
    jh: &[f64],
    jl: &[f64],
    bh: &[f64],
    bl: &[f64],
) -> (Vec<f64>, Vec<f64>, Vec<DD>) {
    let dot = |a: usize, bh2: &[f64], bl2: &[f64]| -> DD {
        S::vectorize(
            #[inline(always)]
            || {
                let mut acc = dv::DotAcc::<S>::zero();
                let mut i = 0;
                while i < ld {
                    let x = DV::load(&jh[a * ld + i..a * ld + i + 8], &jl[a * ld + i..a * ld + i + 8]);
                    let y = DV::load(&bh2[i..i + 8], &bl2[i..i + 8]);
                    acc = acc.add_prod(x, y);
                    i += 8;
                }
                let v = acc.finish();
                let (h, l) = (v.hi.to_array(), v.lo.to_array());
                let mut s = DD::ZERO;
                for k in 0..8 {
                    s = s + DD { hi: h[k], lo: l[k] };
                }
                s
            },
        )
    };
    let cols: Vec<Vec<DD>> = (0..n)
        .into_par_iter()
        .map(|c| {
            (0..=c)
                .map(|r| dot(r, &jh[c * ld..c * ld + ld], &jl[c * ld..c * ld + ld]))
                .collect()
        })
        .collect();
    let mut gh = vec![0.0; ld * n];
    let mut gl = vec![0.0; ld * n];
    for c in 0..n {
        for r in 0..=c {
            let v = cols[c][r];
            gh[c * ld + r] = v.hi;
            gl[c * ld + r] = v.lo;
            gh[r * ld + c] = v.hi;
            gl[r * ld + c] = v.lo;
        }
    }
    let mut bpad_h = vec![0.0; ld];
    let mut bpad_l = vec![0.0; ld];
    bpad_h[..n].copy_from_slice(&bh[..n]);
    bpad_l[..n].copy_from_slice(&bl[..n]);
    let g: Vec<DD> = (0..n).into_par_iter().map(|c| dot(c, &bpad_h, &bpad_l)).collect();
    (gh, gl, g)
}

// The public entry points as kernels, so that `simd::dispatch` runs them on the best backend the CPU has.

struct FactorUnblocked {
    n: usize,
    ld: usize,
    hi: Vec<f64>,
    lo: Vec<f64>,
    par: bool,
}

impl Kernel for FactorUnblocked {
    type Output = Result<DDLu, String>;
    #[inline(always)]
    fn run<S: Simd>(self) -> Self::Output {
        DDLu::factor_unblocked_on::<S>(self.n, self.ld, self.hi, self.lo, self.par)
    }
}

struct FactorBlocked {
    n: usize,
    ld: usize,
    hi: Vec<f64>,
    lo: Vec<f64>,
    par: bool,
}

impl Kernel for FactorBlocked {
    type Output = Result<DDLu, String>;
    #[inline(always)]
    fn run<S: Simd>(self) -> Self::Output {
        DDLu::factor_blocked_on::<S>(self.n, self.ld, self.hi, self.lo, self.par)
    }
}

struct FactorF64 {
    n: usize,
    ld: usize,
    a: Vec<f64>,
    par: bool,
}

impl Kernel for FactorF64 {
    type Output = Result<DDLu, String>;
    #[inline(always)]
    fn run<S: Simd>(self) -> Self::Output {
        DDLu::factor_f64_on::<S>(self.n, self.ld, self.a, self.par)
    }
}

struct LuRectF64<'a> {
    nr: usize,
    ncol: usize,
    np: usize,
    ld: usize,
    a: &'a mut [f64],
    perm: &'a mut [usize],
    par: bool,
}

impl Kernel for LuRectF64<'_> {
    type Output = Result<(), String>;
    #[inline(always)]
    fn run<S: Simd>(self) -> Self::Output {
        lu_rect_f64_on::<S>(self.nr, self.ncol, self.np, self.ld, self.a, self.perm, self.par)
    }
}

struct SolveMany<'a> {
    lu: &'a DDLu,
    bh: &'a mut [f64],
    bl: &'a mut [f64],
    nrhs: usize,
    transpose: bool,
    par: bool,
}

impl Kernel for SolveMany<'_> {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        self.lu
            .solve_many_on::<S>(self.bh, self.bl, self.nrhs, self.transpose, self.par)
    }
}

struct Solve<'a> {
    lu: &'a DDLu,
    b: &'a mut [DD],
}

impl Kernel for Solve<'_> {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        self.lu.solve_on::<S>(self.b)
    }
}

struct RefineQd<'a, F> {
    lu: &'a DDLu,
    b: &'a [QD],
    steps: usize,
    resid: F,
}

impl<F: FnMut(&[QD], &mut [QD])> Kernel for RefineQd<'_, F> {
    type Output = Vec<QD>;
    #[inline(always)]
    fn run<S: Simd>(self) -> Vec<QD> {
        self.lu.solve_refine_qd_on::<S>(self.b, self.steps, self.resid)
    }
}

struct SolveHi<'a> {
    lu: &'a DDLu,
    b: &'a mut [f64],
}

impl Kernel for SolveHi<'_> {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        self.lu.solve_hi_on::<S>(self.b)
    }
}

struct StairSolve<'a> {
    lu: &'a StaircaseLu,
    b: &'a mut [DD],
}

impl Kernel for StairSolve<'_> {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        self.lu.solve_on::<S>(self.b)
    }
}

struct StairSolveMany<'a> {
    lu: &'a StaircaseLu,
    bh: &'a mut [f64],
    bl: &'a mut [f64],
    nrhs: usize,
    transpose: bool,
    par: bool,
}

impl Kernel for StairSolveMany<'_> {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        self.lu
            .solve_many_on::<S>(self.bh, self.bl, self.nrhs, self.transpose, self.par)
    }
}

struct Gram<'a> {
    n: usize,
    ld: usize,
    jh: &'a [f64],
    jl: &'a [f64],
    bh: &'a [f64],
    bl: &'a [f64],
}

impl Kernel for Gram<'_> {
    type Output = (Vec<f64>, Vec<f64>, Vec<DD>);
    #[inline(always)]
    fn run<S: Simd>(self) -> Self::Output {
        gram_on::<S>(self.n, self.ld, self.jh, self.jl, self.bh, self.bl)
    }
}

// ---------------------------------------------------------------------------------------------------------------
// staircase (almost block diagonal) systems with one global parameter
// ---------------------------------------------------------------------------------------------------------------
//
// The Newton system of multiple shooting (or collocation) for a boundary-value problem with one unknown parameter,
// factored without forming the dense matrix. The unknowns z (n of them) are column groups g_0..g_S, contiguous ranges
// of z, and one parameter z[iparam]; the rows are row blocks r_0..r_{S-1}, contiguous ranges of rows, and one more row
// row0. Row block s depends on g_s, g_{s+1} and the parameter; row0 on g_0 only (a normalization or phase condition).
// The parameter enters every row block, so the factorization works on an augmented system with one copy p_s of it in
// each group from g_1 on (ColumnGroup::param) and link rows p_{s-1} - p_s = 0. Row block s then touches g_s and g_{s+1}
// only, and Gaussian elimination with partial pivoting runs in steps: step s factors the columns of g_s, its pivot
// candidates being the rows left over from step s - 1 (zero outside g_s), the extra row (row0 at s = 0, the link row
// after) and row block s, and passes the rows it does not pivot on, now holding the Schur complement on g_{s+1}, to
// step s + 1; the last step is a square LU on g_S. This is partial pivoting on the augmented matrix in this row and
// column order (rows below a step never hold the step's columns), so it has that algorithm's stability, and the fill
// stays inside the steps (the almost-block-diagonal solvers of de Boor and Weiss, ACM TOMS 6 (1980) 80,
// doi:10.1145/355873.355880, and Diaz, Fairweather and Keast, ACM TOMS 9 (1983) 358, doi:10.1145/356044.356053, factor
// the same structure with alternate row and column pivoting). Stored per step: L and U11 (rows x pivot columns) and U12
// (pivot rows x next group), f64; each step is `lu_rect_f64`.
//
// The solves are in double-double with the f64 factors, as DDLu's solves with an f64 factorization. With E the copy of
// the parameter into every p_s and S the selection of the non-link rows, J = S J_aug E, so J^-1 = P J_aug^-1 S^T and
// J^-T = S J_aug^-T P^T for any P with P E = I; P reads the parameter from its first copy.

/// A column group of a `StaircaseLu`'s augmented system: a copy of the parameter first if `param`, then the unknowns
/// z[zoff..zoff + zlen].
#[derive(Clone, Copy, Debug)]
pub struct ColumnGroup {
    pub param: bool,
    pub zoff: usize,
    pub zlen: usize,
}

impl ColumnGroup {
    pub fn len(&self) -> usize {
        self.zlen + self.param as usize
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// One elimination step: rows 0..nc carried from the previous step, row nc the extra row (row0 or a link row), rows
/// nc + 1..nr the residual rows roff..roff + rlen; np pivot columns (this step's group), nrc right columns (the next).
struct Step {
    nc: usize,
    nr: usize,
    np: usize,
    nrc: usize,
    ld: usize,
    /// ld x np, column-major: U11 on and above the diagonal, the multipliers of L below (rows up to nr)
    l: Vec<f64>,
    /// np x nrc, column-major with leading dimension ldu = ld_for(np) (zero below row np): U12
    u12: Vec<f64>,
    ldu: usize,
    perm: Vec<usize>,
    roff: usize,
    rlen: usize,
}

/// The factors of a staircase system (see `StaircaseLu::factor`).
pub struct StaircaseLu {
    /// size of the original system (z)
    pub n: usize,
    groups: Vec<ColumnGroup>,
    steps: Vec<Step>,
    /// index of the group whose parameter copy is read as the parameter, and the parameter's index in z
    gparam: usize,
    iparam: usize,
    /// row0's index in the original rows
    irow0: usize,
    /// seconds spent in fill (building the blocks) and in the factorization
    pub t_fill: f64,
    pub t_factor: f64,
}

/// Deliberate breakage of `StaircaseLu::factor_control`, for checks that must be able to fail: `Pivot` scales one
/// pivot of the middle step by 1 + 1e-6; `Link` replaces the link rows by p_s = 0 (the copies are no longer tied to
/// the parameter).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StaircaseControl {
    None,
    Pivot,
    Link,
}

#[inline(always)]
fn f64dd(x: f64) -> DD {
    DD { hi: x, lo: 0.0 }
}

impl StaircaseLu {
    /// Build and factor. groups: g_0..g_S (g_0 without a parameter copy); `rblocks[s]` (s < S): the rows (offset,
    /// count) of row block s; irow0: row0's index; iparam: the parameter's index in z. fill(s, w, ld, r0) writes row
    /// block s into rows r0..r0 + rlen of the step's ld x (np + nrc) column-major array w (columns: g_s, then
    /// g_{s+1}, each with its parameter copy first if it has one; the parameter's column of row block s is g_{s+1}'s
    /// copy), and for s = 0 also row0 at row r0 - 1; the array is zero elsewhere. The link rows are written here.
    /// Steps are factored in order, each in parallel over column chunks when par. A layout whose column groups with
    /// the parameter, or row blocks with row0, do not cover 0..n exactly once is an error.
    pub fn factor<F>(
        n: usize,
        groups: Vec<ColumnGroup>,
        rblocks: &[(usize, usize)],
        irow0: usize,
        iparam: usize,
        fill: F,
        par: bool,
    ) -> Result<StaircaseLu, String>
    where
        F: FnMut(usize, &mut [f64], usize, usize) -> Result<(), String>,
    {
        Self::factor_control(n, groups, rblocks, irow0, iparam, fill, par, StaircaseControl::None)
    }

    /// `factor` with a deliberate breakage (`StaircaseControl`), for checks that must be able to fail.
    #[allow(clippy::too_many_arguments)]
    pub fn factor_control<F>(
        n: usize,
        groups: Vec<ColumnGroup>,
        rblocks: &[(usize, usize)],
        irow0: usize,
        iparam: usize,
        mut fill: F,
        par: bool,
        control: StaircaseControl,
    ) -> Result<StaircaseLu, String>
    where
        F: FnMut(usize, &mut [f64], usize, usize) -> Result<(), String>,
    {
        let ns = groups.len();
        if ns < 2 || rblocks.len() != ns - 1 || groups[0].param {
            return Err("staircase LU: bad layout".into());
        }
        let gparam = groups
            .iter()
            .position(|g| g.param)
            .ok_or("staircase LU: no parameter copy")?;
        // the column groups with the parameter, and the row blocks with row0, must each cover 0..n exactly once
        let cols = groups.iter().map(|g| (g.zoff, g.zlen)).chain([(iparam, 1)]);
        let rows = rblocks.iter().copied().chain([(irow0, 1)]);
        for (what, parts) in [
            ("column groups and the parameter", cols.collect::<Vec<_>>()),
            ("row blocks and row0", rows.collect()),
        ] {
            let mut seen = vec![false; n];
            for (off, len) in parts {
                if off.checked_add(len).is_none_or(|e| e > n) {
                    return Err(format!("staircase LU: {what}: [{off}, {off} + {len}) outside 0..{n}"));
                }
                if seen[off..off + len].iter().any(|&x| x) {
                    return Err(format!("staircase LU: {what} overlap in [{off}, {off} + {len})"));
                }
                seen[off..off + len].fill(true);
            }
            if let Some(i) = seen.iter().position(|&x| !x) {
                return Err(format!("staircase LU: {what} leave index {i} uncovered"));
            }
        }
        let mut steps: Vec<Step> = Vec::with_capacity(ns);
        // carried rows: (count, column-major nc x np of the coming step, leading dimension nc)
        let mut carry: Vec<f64> = Vec::new();
        let mut nc = 0usize;
        let (mut t_fill, mut t_factor) = (0.0f64, 0.0f64);
        for s in 0..ns {
            let np = groups[s].len();
            let nrc = if s + 1 < ns { groups[s + 1].len() } else { 0 };
            let (roff, rlen) = if s + 1 < ns { rblocks[s] } else { (0, 0) };
            let nnew = if s + 1 < ns { 1 + rlen } else { 0 };
            let nr = nc + nnew;
            if nr < np {
                return Err(format!("staircase LU: step {s} has {nr} rows for {np} pivots"));
            }
            if s + 1 == ns && nr != np {
                return Err(format!("staircase LU: last step not square ({nr} x {np})"));
            }
            let ld = ld_for(nr);
            let ncol = np + nrc;
            let mut w = vec![0.0f64; ld * ncol];
            for c in 0..np {
                w[c * ld..c * ld + nc].copy_from_slice(&carry[c * nc..(c + 1) * nc]);
            }
            if s + 1 < ns {
                if s > 0 {
                    // link row p_{s-1} - p_s = 0 (both groups start with their parameter copy)
                    if !(groups[s].param && groups[s + 1].param) {
                        return Err("staircase LU: a link row needs parameter copies on both sides".into());
                    }
                    if control != StaircaseControl::Link {
                        w[nc] = 1.0;
                    }
                    w[np * ld + nc] = -1.0;
                }
                let t = std::time::Instant::now();
                fill(s, &mut w, ld, nc + 1)?;
                t_fill += t.elapsed().as_secs_f64();
            }
            let mut perm = vec![0usize; np];
            let t = std::time::Instant::now();
            lu_rect_f64(nr, ncol, np, ld, &mut w, &mut perm, par)?;
            t_factor += t.elapsed().as_secs_f64();
            if control == StaircaseControl::Pivot && s == ns / 2 {
                let k = np / 2;
                w[k * ld + k] *= 1.0 + 1e-6;
            }
            // U12 (rows 0..np of the right columns) and the next carry (rows np..nr of the right columns)
            let ldu = ld_for(np);
            let mut u12 = vec![0.0f64; ldu * nrc];
            let nc2 = nr - np;
            let mut carry2 = vec![0.0f64; nc2 * nrc];
            for c in 0..nrc {
                let col = &w[(np + c) * ld..(np + c) * ld + nr];
                u12[c * ldu..c * ldu + np].copy_from_slice(&col[..np]);
                carry2[c * nc2..(c + 1) * nc2].copy_from_slice(&col[np..nr]);
            }
            w.truncate(ld * np);
            w.shrink_to_fit();
            steps.push(Step {
                nc,
                nr,
                np,
                nrc,
                ld,
                l: w,
                u12,
                ldu,
                perm,
                roff,
                rlen,
            });
            carry = carry2;
            nc = nc2;
        }
        Ok(StaircaseLu {
            n,
            groups,
            steps,
            gparam,
            iparam,
            irow0,
            t_fill,
            t_factor,
        })
    }

    /// bytes held by the factors
    pub fn bytes(&self) -> usize {
        self.steps
            .iter()
            .map(|s| 8 * (s.l.len() + s.u12.len()) + 8 * s.perm.len())
            .sum()
    }

    #[inline(always)]
    fn lu(st: &Step, i: usize, k: usize) -> f64 {
        st.l[k * st.ld + i]
    }

    /// min and max |u_kk| over all steps
    pub fn pivot_range(&self) -> (f64, f64) {
        let mut lo = f64::INFINITY;
        let mut hi = 0.0f64;
        for st in &self.steps {
            for k in 0..st.np {
                let v = Self::lu(st, k, k).abs();
                lo = lo.min(v);
                hi = hi.max(v);
            }
        }
        (lo, hi)
    }

    /// Solve J x = b in place (b: n values in the original row order in, the unknowns z out). Each column's update
    /// runs 8 rows at a time on the backend `simd::dispatch` picks, every entry with the operations and order of the
    /// scalar loops.
    pub fn solve(&self, b: &mut [DD]) {
        simd::dispatch(StairSolve { lu: self, b })
    }

    fn solve_on<S: Simd>(&self, b: &mut [DD]) {
        S::vectorize(
            #[inline(always)]
            move || {
                assert_eq!(b.len(), self.n);
                let ns = self.steps.len();
                let mut carry: Vec<DD> = Vec::new();
                let mut ys: Vec<Vec<DD>> = Vec::with_capacity(ns);
                for (s, st) in self.steps.iter().enumerate() {
                    let mut v = carry;
                    if s + 1 < ns {
                        v.push(if s == 0 { b[self.irow0] } else { DD::ZERO });
                        v.extend_from_slice(&b[st.roff..st.roff + st.rlen]);
                    }
                    debug_assert_eq!(v.len(), st.nr);
                    for k in 0..st.np {
                        let p = st.perm[k];
                        if p != k {
                            v.swap(k, p);
                        }
                    }
                    let (mut vh, mut vl) = split(&v, st.ld);
                    for k in 0..st.np {
                        let nt = -DD { hi: vh[k], lo: vl[k] };
                        if nt.hi == 0.0 {
                            continue;
                        }
                        let col = &st.l[k * st.ld..(k + 1) * st.ld];
                        axpy_rows::<S>(&mut vh, &mut vl, col, None, k + 1, st.nr, nt);
                    }
                    join(&mut v, &vh, &vl);
                    carry = v.split_off(st.np);
                    ys.push(v);
                }
                let mut xr: Vec<DD> = Vec::new();
                let mut xs: Vec<Vec<DD>> = vec![Vec::new(); ns];
                for s in (0..ns).rev() {
                    let st = &self.steps[s];
                    let mut y = std::mem::take(&mut ys[s]);
                    let (mut yh, mut yl) = split(&y, st.ldu);
                    for j in (0..st.nrc).rev() {
                        let nt = -xr[j];
                        if nt.hi == 0.0 {
                            continue;
                        }
                        let col = &st.u12[j * st.ldu..(j + 1) * st.ldu];
                        axpy_rows::<S>(&mut yh, &mut yl, col, None, 0, st.np, nt);
                    }
                    for k in (0..st.np).rev() {
                        let q = DD { hi: yh[k], lo: yl[k] } / f64dd(Self::lu(st, k, k));
                        (yh[k], yl[k]) = (q.hi, q.lo);
                        let col = &st.l[k * st.ld..(k + 1) * st.ld];
                        axpy_rows::<S>(&mut yh, &mut yl, col, None, 0, k, -q);
                    }
                    join(&mut y, &yh, &yl);
                    xr = y.clone();
                    xs[s] = y;
                }
                for (s, g) in self.groups.iter().enumerate() {
                    let o = g.param as usize;
                    b[g.zoff..g.zoff + g.zlen].copy_from_slice(&xs[s][o..o + g.zlen]);
                    if s == self.gparam {
                        b[self.iparam] = xs[s][0];
                    }
                }
            },
        )
    }

    /// Solve J^T y = b in place (b: n values indexed by the unknowns in, by the residual rows out).
    pub fn solve_t(&self, b: &mut [DD]) {
        assert_eq!(b.len(), self.n);
        let ns = self.steps.len();
        // U^T w = P^T-placed b, forward over the groups
        let mut ws: Vec<Vec<DD>> = Vec::with_capacity(ns);
        for (s, g) in self.groups.iter().enumerate() {
            let st = &self.steps[s];
            let mut v: Vec<DD> = Vec::with_capacity(st.np);
            if g.param {
                v.push(if s == self.gparam { b[self.iparam] } else { DD::ZERO });
            }
            v.extend_from_slice(&b[g.zoff..g.zoff + g.zlen]);
            if s > 0 {
                let sp = &self.steps[s - 1];
                let wp = &ws[s - 1];
                for c in 0..st.np {
                    let mut acc = v[c];
                    let col = &sp.u12[c * sp.ldu..c * sp.ldu + sp.np];
                    for i in 0..sp.np {
                        acc = dd_axpy(acc, f64dd(col[i]), -wp[i]);
                    }
                    v[c] = acc;
                }
            }
            for k in 0..st.np {
                let mut acc = v[k];
                let col = &st.l[k * st.ld..k * st.ld + k];
                for i in 0..k {
                    acc = dd_axpy(acc, f64dd(col[i]), -v[i]);
                }
                v[k] = acc / f64dd(Self::lu(st, k, k));
            }
            ws.push(v);
        }
        // L^T and P^T, backward over the steps; each step's leading entries are the adjoint of the rows it carried in
        let mut adj: Vec<DD> = Vec::new();
        let mut out = vec![DD::ZERO; self.n];
        for s in (0..ns).rev() {
            let st = &self.steps[s];
            let mut v = std::mem::take(&mut ws[s]);
            v.extend_from_slice(&adj);
            debug_assert_eq!(v.len(), st.nr);
            for k in (0..st.np).rev() {
                let mut acc = v[k];
                let col = &st.l[k * st.ld..k * st.ld + st.nr];
                for i in k + 1..st.nr {
                    acc = dd_axpy(acc, f64dd(col[i]), -v[i]);
                }
                v[k] = acc;
            }
            for k in (0..st.np).rev() {
                let p = st.perm[k];
                if p != k {
                    v.swap(k, p);
                }
            }
            if s + 1 < ns {
                if s == 0 {
                    out[self.irow0] = v[st.nc];
                }
                out[st.roff..st.roff + st.rlen].copy_from_slice(&v[st.nc + 1..st.nr]);
            }
            v.truncate(st.nc);
            adj = v;
        }
        b.copy_from_slice(&out);
    }

    /// Several right-hand sides, row-major (nrhs, n) as (hi, lo), in place; each row bitwise as solve / solve_t
    /// gives it. Eight right-hand sides share each lane vector (`solve_dv`, `solve_t_dv`), and the groups of eight run
    /// in parallel when par.
    pub fn solve_many(&self, bh: &mut [f64], bl: &mut [f64], nrhs: usize, transpose: bool, par: bool) {
        simd::dispatch(StairSolveMany {
            lu: self,
            bh,
            bl,
            nrhs,
            transpose,
            par,
        })
    }

    fn solve_many_on<S: Simd>(&self, bh: &mut [f64], bl: &mut [f64], nrhs: usize, transpose: bool, par: bool) {
        S::vectorize(
            #[inline(always)]
            move || {
                let n = self.n;
                assert!(bh.len() >= nrhs * n && bl.len() >= nrhs * n);
                let ng = nrhs.div_ceil(8);
                let (bh0, bl0): (&[f64], &[f64]) = (bh, bl);
                let group = |g: usize| -> Vec<DV<S>> {
                    S::vectorize(
                        #[inline(always)]
                        || {
                            let live = (nrhs - 8 * g).min(8);
                            let mut v = vec![DV::<S>::zero(); n];
                            let mut h = [0.0f64; 8];
                            let mut l = [0.0f64; 8];
                            for (i, vi) in v.iter_mut().enumerate() {
                                for r in 0..live {
                                    h[r] = bh0[(8 * g + r) * n + i];
                                    l[r] = bl0[(8 * g + r) * n + i];
                                }
                                *vi = DV {
                                    hi: V8::from_array(h),
                                    lo: V8::from_array(l),
                                };
                            }
                            if transpose {
                                self.solve_t_dv(&mut v);
                            } else {
                                self.solve_dv(&mut v);
                            }
                            v
                        },
                    )
                };
                let out: Vec<Vec<DV<S>>> = if par && ng > 1 {
                    (0..ng).into_par_iter().map(group).collect()
                } else {
                    (0..ng).map(group).collect()
                };
                for (g, v) in out.iter().enumerate() {
                    let live = (nrhs - 8 * g).min(8);
                    for (i, vi) in v.iter().enumerate() {
                        let (h, l) = (vi.hi.to_array(), vi.lo.to_array());
                        for r in 0..live {
                            bh[(8 * g + r) * n + i] = h[r];
                            bl[(8 * g + r) * n + i] = l[r];
                        }
                    }
                }
            },
        )
    }

    /// `solve` lane by lane: each lane a right-hand side (padding lanes hold zeros and stay zero). The scalar solve
    /// skips a column whose -y_k has a zero leading part; here those lanes keep their values.
    fn solve_dv<S: Simd>(&self, b: &mut [DV<S>]) {
        S::vectorize(
            #[inline(always)]
            move || {
                let ns = self.steps.len();
                let z = V8::<S>::zero();
                let l8 = |x: f64| DV::<S> {
                    hi: V8::splat(x),
                    lo: z,
                };
                let mut carry: Vec<DV<S>> = Vec::new();
                let mut ys: Vec<Vec<DV<S>>> = Vec::with_capacity(ns);
                for (s, st) in self.steps.iter().enumerate() {
                    let mut v = carry;
                    if s + 1 < ns {
                        v.push(if s == 0 { b[self.irow0] } else { DV::zero() });
                        v.extend_from_slice(&b[st.roff..st.roff + st.rlen]);
                    }
                    for k in 0..st.np {
                        let p = st.perm[k];
                        if p != k {
                            v.swap(k, p);
                        }
                    }
                    for k in 0..st.np {
                        let nt = -v[k];
                        let m = nt.hi.eq(z).not();
                        if m.bits() == 0 {
                            continue;
                        }
                        let col = &st.l[k * st.ld..k * st.ld + st.nr];
                        for i in k + 1..st.nr {
                            v[i] = sel_dv(m, axpy8(v[i], l8(col[i]), nt), v[i]);
                        }
                    }
                    carry = v.split_off(st.np);
                    ys.push(v);
                }
                let mut xr: Vec<DV<S>> = Vec::new();
                let mut xs: Vec<Vec<DV<S>>> = vec![Vec::new(); ns];
                for s in (0..ns).rev() {
                    let st = &self.steps[s];
                    let mut y = std::mem::take(&mut ys[s]);
                    for j in (0..st.nrc).rev() {
                        let nt = -xr[j];
                        let m = nt.hi.eq(z).not();
                        if m.bits() == 0 {
                            continue;
                        }
                        let col = &st.u12[j * st.ldu..j * st.ldu + st.np];
                        for i in 0..st.np {
                            y[i] = sel_dv(m, axpy8(y[i], l8(col[i]), nt), y[i]);
                        }
                    }
                    for k in (0..st.np).rev() {
                        y[k] = y[k] / l8(Self::lu(st, k, k));
                        let nt = -y[k];
                        let col = &st.l[k * st.ld..k * st.ld + k];
                        for i in 0..k {
                            y[i] = axpy8(y[i], l8(col[i]), nt);
                        }
                    }
                    xr = y.clone();
                    xs[s] = y;
                }
                for (s, g) in self.groups.iter().enumerate() {
                    let o = g.param as usize;
                    b[g.zoff..g.zoff + g.zlen].copy_from_slice(&xs[s][o..o + g.zlen]);
                    if s == self.gparam {
                        b[self.iparam] = xs[s][0];
                    }
                }
            },
        )
    }

    /// `solve_t` lane by lane.
    fn solve_t_dv<S: Simd>(&self, b: &mut [DV<S>]) {
        S::vectorize(
            #[inline(always)]
            move || {
                let ns = self.steps.len();
                let z = V8::<S>::zero();
                let l8 = |x: f64| DV::<S> {
                    hi: V8::splat(x),
                    lo: z,
                };
                let mut ws: Vec<Vec<DV<S>>> = Vec::with_capacity(ns);
                for (s, g) in self.groups.iter().enumerate() {
                    let st = &self.steps[s];
                    let mut v: Vec<DV<S>> = Vec::with_capacity(st.np);
                    if g.param {
                        v.push(if s == self.gparam { b[self.iparam] } else { DV::zero() });
                    }
                    v.extend_from_slice(&b[g.zoff..g.zoff + g.zlen]);
                    if s > 0 {
                        let sp = &self.steps[s - 1];
                        let nw: Vec<DV<S>> = ws[s - 1].iter().map(|&w| -w).collect();
                        for c in 0..st.np {
                            let mut acc = v[c];
                            let col = &sp.u12[c * sp.ldu..c * sp.ldu + sp.np];
                            for i in 0..sp.np {
                                acc = axpy8(acc, l8(col[i]), nw[i]);
                            }
                            v[c] = acc;
                        }
                    }
                    for k in 0..st.np {
                        let mut acc = v[k];
                        let col = &st.l[k * st.ld..k * st.ld + k];
                        for i in 0..k {
                            acc = axpy8(acc, l8(col[i]), -v[i]);
                        }
                        v[k] = acc / l8(Self::lu(st, k, k));
                    }
                    ws.push(v);
                }
                let mut adj: Vec<DV<S>> = Vec::new();
                let mut out = vec![DV::<S>::zero(); self.n];
                for s in (0..ns).rev() {
                    let st = &self.steps[s];
                    let mut v = std::mem::take(&mut ws[s]);
                    v.extend_from_slice(&adj);
                    for k in (0..st.np).rev() {
                        let mut acc = v[k];
                        let col = &st.l[k * st.ld..k * st.ld + st.nr];
                        for i in k + 1..st.nr {
                            acc = axpy8(acc, l8(col[i]), -v[i]);
                        }
                        v[k] = acc;
                    }
                    for k in (0..st.np).rev() {
                        let p = st.perm[k];
                        if p != k {
                            v.swap(k, p);
                        }
                    }
                    if s + 1 < ns {
                        if s == 0 {
                            out[self.irow0] = v[st.nc];
                        }
                        out[st.roff..st.roff + st.rlen].copy_from_slice(&v[st.nc + 1..st.nr]);
                    }
                    v.truncate(st.nc);
                    adj = v;
                }
                b.copy_from_slice(&out);
            },
        )
    }
}

/// x's parts as two arrays of len (at least x.len(), zero after)
#[inline(always)]
fn split(x: &[DD], len: usize) -> (Vec<f64>, Vec<f64>) {
    let (mut h, mut l) = (vec![0.0f64; len], vec![0.0f64; len]);
    for (i, v) in x.iter().enumerate() {
        h[i] = v.hi;
        l[i] = v.lo;
    }
    (h, l)
}

/// x from the arrays h and l
#[inline(always)]
fn join(x: &mut [DD], h: &[f64], l: &[f64]) {
    for (i, v) in x.iter_mut().enumerate() {
        *v = DD { hi: h[i], lo: l[i] };
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Dense quad-double LU
// ---------------------------------------------------------------------------------------------------------------

/// Deliberate breakage of `QDLu::factor_control`, for the controls of its accuracy tests.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QdLuControl {
    None,
    /// every trailing update rounded to double-double (its two lower parts dropped)
    UpdateDd,
}

/// Dense quad-double LU with partial pivoting (LAPACK getf2 order, as `DDLu::factor_unblocked`), column-major with
/// the leading dimension a multiple of 8 and each entry's four parts in four arrays, so that the multipliers and the
/// trailing update run on 8-row `QV` lanes; the trailing columns are updated in parallel (rayon) for large matrices.
/// For systems whose condition number nears 2^104, where a double-double solve has no correct digit: a solve's error
/// is about cond(A) 2^-209 (backward stability of partial pivoting; Higham, Accuracy and Stability of Numerical
/// Algorithms, 2nd ed., SIAM 2002, ch. 9). An update with an exactly zero multiplier block (8 rows) or an exactly zero
/// pivot-row entry is skipped (it cannot change a value), so the zero blocks of a sparse matrix cost nothing.
#[derive(Clone)]
pub struct QDLu {
    pub n: usize,
    pub ld: usize,
    /// part q of entry (i, j) of L (unit, below the diagonal) and U (on and above it) at c[q][j * ld + i]
    pub c: [Vec<f64>; 4],
    pub perm: Vec<usize>,
}

/// one column's four parts, as the parallel update zips them
type Cols4<'a> = (((&'a mut [f64], &'a mut [f64]), &'a mut [f64]), &'a mut [f64]);

#[inline(always)]
fn load_qv<S: Simd>(c: [&[f64]; 4], i: usize) -> QV<S> {
    QV::load(&c[0][i..i + 8], &c[1][i..i + 8], &c[2][i..i + 8], &c[3][i..i + 8])
}

#[inline(always)]
fn sel_qv<S: Simd>(m: M8<S>, u: QV<S>, a: QV<S>) -> QV<S> {
    QV {
        c: std::array::from_fn(|q| m.sel(u.c[q], a.c[q])),
    }
}

/// b[i] += l[i] t for i in lo..hi, on the 8-row blocks that meet lo..hi; rows outside keep their value. Blocks of l
/// that are exactly zero are skipped. Every slice holds hi rounded up to 8 rows.
#[inline(always)]
fn qd_axpy_rows<S: Simd>(b: [&mut [f64]; 4], l: [&[f64]; 4], lo: usize, hi: usize, t: QD, ctl: QdLuControl) {
    let tv = QV::<S>::splat(t);
    let [b0, b1, b2, b3] = b;
    let mut i = 8 * (lo / 8);
    while i < hi {
        if l[0][i..i + 8].iter().any(|&v| v != 0.0) {
            let a = QV::<S>::load(&b0[i..i + 8], &b1[i..i + 8], &b2[i..i + 8], &b3[i..i + 8]);
            let mut r = a + load_qv::<S>(l, i) * tv;
            if ctl == QdLuControl::UpdateDd {
                r = QV::from_dv(r.to_dv());
            }
            let r = sel_qv(rows_in::<S>(i, lo, hi), r, a);
            r.store(
                &mut b0[i..i + 8],
                &mut b1[i..i + 8],
                &mut b2[i..i + 8],
                &mut b3[i..i + 8],
            );
        }
        i += 8;
    }
}

impl QDLu {
    /// Factor the n x n matrix given column-major with leading dimension ld (ld % 8 == 0, padding rows zero), part q
    /// of entry (i, j) at c[q][j * ld + i]. par: update the trailing columns in parallel (rayon's current pool).
    pub fn factor(n: usize, ld: usize, c: [Vec<f64>; 4], par: bool) -> Result<QDLu, String> {
        Self::factor_control(n, ld, c, par, QdLuControl::None)
    }

    /// `factor` with a control (`QdLuControl`; None is `factor`)
    pub fn factor_control(n: usize, ld: usize, c: [Vec<f64>; 4], par: bool, ctl: QdLuControl) -> Result<QDLu, String> {
        simd::dispatch(FactorQd { n, ld, c, par, ctl })
    }

    fn factor_on<S: Simd>(
        n: usize,
        ld: usize,
        mut c: [Vec<f64>; 4],
        par: bool,
        ctl: QdLuControl,
    ) -> Result<QDLu, String> {
        S::vectorize(
            #[inline(always)]
            move || {
                assert!(ld.is_multiple_of(8) && ld >= n && c.iter().all(|p| p.len() >= ld * n));
                let mut perm = vec![0usize; n];
                let mut m: [Vec<f64>; 4] = std::array::from_fn(|_| vec![0.0f64; ld]);
                for k in 0..n {
                    let ck = k * ld;
                    let (p, best) = pivot_search::<S>(&c[0][ck..ck + ld], k, n);
                    if best == 0.0 || !best.is_finite() {
                        return Err(format!("singular or non-finite pivot at column {k} ({best})"));
                    }
                    perm[k] = p;
                    if p != k {
                        for j in 0..n {
                            for part in c.iter_mut() {
                                part.swap(j * ld + k, j * ld + p);
                            }
                        }
                    }
                    let piv = QV::<S>::splat(QD {
                        x: std::array::from_fn(|q| c[q][ck + k]),
                    });
                    // the multipliers l_ik = a_ik / a_kk, rows k + 1..n
                    let mut i = 8 * ((k + 1) / 8);
                    while i < n {
                        let x = load_qv::<S>([&c[0], &c[1], &c[2], &c[3]], ck + i);
                        let y = sel_qv(rows_in::<S>(i, k + 1, n), x / piv, x);
                        let [c0, c1, c2, c3] = &mut c;
                        let o = ck + i;
                        y.store(
                            &mut c0[o..o + 8],
                            &mut c1[o..o + 8],
                            &mut c2[o..o + 8],
                            &mut c3[o..o + 8],
                        );
                        i += 8;
                    }
                    if k + 1 == n {
                        break;
                    }
                    let r0 = 8 * ((k + 1) / 8);
                    for q in 0..4 {
                        for i in r0..ld {
                            m[q][i] = if i > k && i < n { c[q][ck + i] } else { 0.0 };
                        }
                    }
                    let ncols = n - k - 1;
                    let [c0, c1, c2, c3] = &mut c;
                    let (r0s, r1s, r2s, r3s) = (
                        &mut c0[(k + 1) * ld..(k + 1 + ncols) * ld],
                        &mut c1[(k + 1) * ld..(k + 1 + ncols) * ld],
                        &mut c2[(k + 1) * ld..(k + 1 + ncols) * ld],
                        &mut c3[(k + 1) * ld..(k + 1 + ncols) * ld],
                    );
                    let ml = [&m[0][..], &m[1][..], &m[2][..], &m[3][..]];
                    let upd = |(((a0, a1), a2), a3): Cols4| {
                        S::vectorize(
                            #[inline(always)]
                            || {
                                if a0[k] == 0.0 {
                                    return;
                                }
                                let nt = -QD {
                                    x: [a0[k], a1[k], a2[k], a3[k]],
                                };
                                qd_axpy_rows::<S>([a0, a1, a2, a3], ml, k + 1, n, nt, ctl);
                            },
                        )
                    };
                    if par && ncols * (ld - r0) > 4096 {
                        r0s.par_chunks_mut(ld)
                            .zip(r1s.par_chunks_mut(ld))
                            .zip(r2s.par_chunks_mut(ld))
                            .zip(r3s.par_chunks_mut(ld))
                            .for_each(upd);
                    } else {
                        r0s.chunks_mut(ld)
                            .zip(r1s.chunks_mut(ld))
                            .zip(r2s.chunks_mut(ld))
                            .zip(r3s.chunks_mut(ld))
                            .for_each(upd);
                    }
                }
                Ok(QDLu { n, ld, c, perm })
            },
        )
    }

    /// entry (i, j) of the factors
    #[inline(always)]
    pub fn at(&self, i: usize, j: usize) -> QD {
        let o = j * self.ld + i;
        QD {
            x: std::array::from_fn(|q| self.c[q][o]),
        }
    }

    fn col(&self, k: usize) -> [&[f64]; 4] {
        let r = k * self.ld..(k + 1) * self.ld;
        std::array::from_fn(|q| &self.c[q][r.clone()])
    }

    /// Solve A x = b in place (b: n values): the row swaps, L y = b column by column (skipping columns whose y_k is
    /// zero), then U x = y, each column's update 8 rows at a time on the backend `simd::dispatch` picks.
    pub fn solve(&self, b: &mut [QD]) {
        simd::dispatch(SolveQd { lu: self, b })
    }

    fn solve_on<S: Simd>(&self, b: &mut [QD]) {
        S::vectorize(
            #[inline(always)]
            move || {
                let (n, ld) = (self.n, self.ld);
                assert!(b.len() >= n);
                for k in 0..n {
                    let p = self.perm[k];
                    if p != k {
                        b.swap(k, p);
                    }
                }
                let mut v: [Vec<f64>; 4] = std::array::from_fn(|q| {
                    let mut a = vec![0.0f64; ld];
                    for i in 0..n {
                        a[i] = b[i].x[q];
                    }
                    a
                });
                let get = |v: &[Vec<f64>; 4], i: usize| QD {
                    x: std::array::from_fn(|q| v[q][i]),
                };
                for k in 0..n {
                    let t = -get(&v, k);
                    if t.x[0] == 0.0 {
                        continue;
                    }
                    let [v0, v1, v2, v3] = &mut v;
                    qd_axpy_rows::<S>([v0, v1, v2, v3], self.col(k), k + 1, n, t, QdLuControl::None);
                }
                for k in (0..n).rev() {
                    let q = get(&v, k) / self.at(k, k);
                    for p in 0..4 {
                        v[p][k] = q.x[p];
                    }
                    if q.x[0] != 0.0 {
                        let [v0, v1, v2, v3] = &mut v;
                        qd_axpy_rows::<S>([v0, v1, v2, v3], self.col(k), 0, k, -q, QdLuControl::None);
                    }
                }
                for i in 0..n {
                    b[i] = get(&v, i);
                }
            },
        )
    }

    /// Solve A^T y = b in place. With P A = L U (P the recorded row swaps): U^T w = b, L^T v = w, y = P^T v.
    pub fn solve_t(&self, b: &mut [QD]) {
        let n = self.n;
        for k in 0..n {
            let mut acc = b[k];
            for i in 0..k {
                acc = acc - self.at(i, k) * b[i];
            }
            b[k] = acc / self.at(k, k);
        }
        for k in (0..n).rev() {
            let mut acc = b[k];
            for i in k + 1..n {
                acc = acc - self.at(i, k) * b[i];
            }
            b[k] = acc;
        }
        for k in (0..n).rev() {
            let p = self.perm[k];
            if p != k {
                b.swap(k, p);
            }
        }
    }

    /// min and max |u_kk| (leading parts)
    pub fn pivot_range(&self) -> (f64, f64) {
        let mut lo = f64::INFINITY;
        let mut hi = 0.0f64;
        for k in 0..self.n {
            let v = self.c[0][k * self.ld + k].abs();
            lo = lo.min(v);
            hi = hi.max(v);
        }
        (lo, hi)
    }
}

struct FactorQd {
    n: usize,
    ld: usize,
    c: [Vec<f64>; 4],
    par: bool,
    ctl: QdLuControl,
}

impl Kernel for FactorQd {
    type Output = Result<QDLu, String>;
    #[inline(always)]
    fn run<S: Simd>(self) -> Self::Output {
        QDLu::factor_on::<S>(self.n, self.ld, self.c, self.par, self.ctl)
    }
}

struct SolveQd<'a> {
    lu: &'a QDLu,
    b: &'a mut [QD],
}

impl Kernel for SolveQd<'_> {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        self.lu.solve_on::<S>(self.b)
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The determinant of a complex double-double matrix
// ---------------------------------------------------------------------------------------------------------------

/// ln|det| and arg det (in (-pi, pi]) of the complex n x n matrix with real parts rh + rl and imaginary parts
/// ih + il (column-major, leading dimension ld, ld % 8 == 0, padding rows zero), by LU with partial pivoting in
/// getf2 order: the pivot of column k is its entry of largest modulus on or below the diagonal, the column below it
/// is scaled by 1 / u_kk = conj(u_kk) / |u_kk|^2, and the trailing columns are updated on 8-row lane vectors (the
/// real and the imaginary part of a - l t each through the dot accumulator; in parallel over the columns when par).
/// ln|det| and arg det are the sums of ln|u_kk| and arg u_kk in f64, the pivots rounded to f64 first, plus pi per
/// row interchange; the factors are not kept. Also returns min and max |u_kk|. For a real matrix `DDLu::logdet`
/// gives the sign and ln|det|.
#[allow(clippy::type_complexity)]
pub fn clu_logdet(
    n: usize,
    ld: usize,
    rh: Vec<f64>,
    rl: Vec<f64>,
    ih: Vec<f64>,
    il: Vec<f64>,
    par: bool,
) -> Result<(f64, f64, f64, f64), String> {
    simd::dispatch(CluLogdet {
        n,
        ld,
        rh,
        rl,
        ih,
        il,
        par,
    })
}

#[allow(clippy::type_complexity)]
fn clu_logdet_on<S: Simd>(
    n: usize,
    ld: usize,
    mut rh: Vec<f64>,
    mut rl: Vec<f64>,
    mut ih: Vec<f64>,
    mut il: Vec<f64>,
    par: bool,
) -> Result<(f64, f64, f64, f64), String> {
    S::vectorize(
        #[inline(always)]
        move || {
            assert!(ld.is_multiple_of(8) && ld >= n);
            assert!(rh.len() >= ld * n && rl.len() >= ld * n && ih.len() >= ld * n && il.len() >= ld * n);
            let at = |h: &[f64], l: &[f64], i: usize| DD { hi: h[i], lo: l[i] };
            let mut la = 0.0f64;
            let mut arg = 0.0f64;
            let mut pmin = f64::INFINITY;
            let mut pmax = 0.0f64;
            let mut lrh = vec![0.0f64; ld];
            let mut lrl = vec![0.0f64; ld];
            let mut lih = vec![0.0f64; ld];
            let mut lil = vec![0.0f64; ld];
            for k in 0..n {
                let ck = k * ld;
                let mut p = k;
                let mut best = -1.0f64;
                for i in k..n {
                    let v = rh[ck + i].hypot(ih[ck + i]);
                    if v > best {
                        best = v;
                        p = i;
                    }
                }
                // a NaN diagonal entry is a non-finite pivot (as `pivot_search`); a column of NaN leaves best at -1
                // (a NaN modulus never replaces it, so best is never NaN itself)
                if rh[ck + k].hypot(ih[ck + k]).is_nan() || best <= 0.0 || !best.is_finite() {
                    return Err(format!("singular or non-finite pivot at column {k} ({best})"));
                }
                if p != k {
                    for j in 0..n {
                        rh.swap(j * ld + k, j * ld + p);
                        rl.swap(j * ld + k, j * ld + p);
                        ih.swap(j * ld + k, j * ld + p);
                        il.swap(j * ld + k, j * ld + p);
                    }
                    arg += std::f64::consts::PI;
                }
                let ur = at(&rh, &rl, ck + k);
                let ui = at(&ih, &il, ck + k);
                let mag = (ur.hi + ur.lo).hypot(ui.hi + ui.lo);
                // the pivot's lo parts can be NaN with finite hi parts
                if mag <= 0.0 || !mag.is_finite() {
                    return Err(format!("singular or non-finite pivot at column {k} ({mag})"));
                }
                // |u| and its phase to f64 are all ln|u| and arg u need
                la += mag.ln();
                arg += (ui.hi + ui.lo).atan2(ur.hi + ur.lo);
                pmin = pmin.min(mag);
                pmax = pmax.max(mag);
                if k + 1 == n {
                    break;
                }
                // The multipliers a_ik / u with u and every a_ik scaled by the same power of two (exact) to bring u
                // to order one: 1/u_s = conj(u_s) / |u_s|^2 then neither overflows nor underflows for any pivot,
                // and a_ik,s / u_s is a_ik / u, which can only overflow when the multiplier itself does (a
                // subnormal pivot under an ordinary entry). The quotients' significands are those of the unscaled
                // formula, so the factors are bitwise the same wherever that one stays in range.
                let isc = 1.0 / pow2_near(mag.clamp(f64::MIN_POSITIVE, 2f64.powi(1022)));
                let (us_r, us_i) = (ur.mul_pwr2(isc), ui.mul_pwr2(isc));
                let den = us_r * us_r + us_i * us_i;
                let vr = us_r / den;
                let vi = -(us_i / den);
                for i in k + 1..n {
                    let ar = at(&rh, &rl, ck + i).mul_pwr2(isc);
                    let ai = at(&ih, &il, ck + i).mul_pwr2(isc);
                    let xr = ar * vr - ai * vi;
                    let xi = ar * vi + ai * vr;
                    rh[ck + i] = xr.hi;
                    rl[ck + i] = xr.lo;
                    ih[ck + i] = xi.hi;
                    il[ck + i] = xi.lo;
                }
                let r0 = 8 * ((k + 1) / 8);
                for i in r0..ld {
                    if i > k && i < n {
                        lrh[i] = rh[ck + i];
                        lrl[i] = rl[ck + i];
                        lih[i] = ih[ck + i];
                        lil[i] = il[ck + i];
                    } else {
                        lrh[i] = 0.0;
                        lrl[i] = 0.0;
                        lih[i] = 0.0;
                        lil[i] = 0.0;
                    }
                }
                let ncols = n - k - 1;
                let (_, arh) = rh.split_at_mut((k + 1) * ld);
                let (_, arl) = rl.split_at_mut((k + 1) * ld);
                let (_, aih) = ih.split_at_mut((k + 1) * ld);
                let (_, ail) = il.split_at_mut((k + 1) * ld);
                let upd = |(((ch, cl), dh), dl): (((&mut [f64], &mut [f64]), &mut [f64]), &mut [f64])| {
                    S::vectorize(
                        #[inline(always)]
                        || {
                            let tr = DD { hi: ch[k], lo: cl[k] };
                            let ti = DD { hi: dh[k], lo: dl[k] };
                            if tr.hi == 0.0 && ti.hi == 0.0 {
                                return;
                            }
                            let ntr = DV::<S>::splat(-tr);
                            let nti = DV::<S>::splat(-ti);
                            let pti = DV::<S>::splat(ti);
                            let mut i = r0;
                            while i < ld {
                                let ar = DV::<S>::load(&ch[i..i + 8], &cl[i..i + 8]);
                                let ai = DV::<S>::load(&dh[i..i + 8], &dl[i..i + 8]);
                                let lr = DV::<S>::load(&lrh[i..i + 8], &lrl[i..i + 8]);
                                let li = DV::<S>::load(&lih[i..i + 8], &lil[i..i + 8]);
                                // a -= l t:  re: ar - lr tr + li ti,  im: ai - lr ti - li tr
                                let nr = DotAcc::<S>::zero().add(ar).add_prod(lr, ntr).add_prod(li, pti).finish();
                                let ni = DotAcc::<S>::zero().add(ai).add_prod(lr, nti).add_prod(li, ntr).finish();
                                nr.store(&mut ch[i..i + 8], &mut cl[i..i + 8]);
                                ni.store(&mut dh[i..i + 8], &mut dl[i..i + 8]);
                                i += 8;
                            }
                        },
                    )
                };
                if par && ncols * (ld - r0) > 32768 {
                    arh[..ncols * ld]
                        .par_chunks_mut(ld)
                        .zip(arl[..ncols * ld].par_chunks_mut(ld))
                        .zip(aih[..ncols * ld].par_chunks_mut(ld))
                        .zip(ail[..ncols * ld].par_chunks_mut(ld))
                        .for_each(upd);
                } else {
                    arh[..ncols * ld]
                        .chunks_mut(ld)
                        .zip(arl[..ncols * ld].chunks_mut(ld))
                        .zip(aih[..ncols * ld].chunks_mut(ld))
                        .zip(ail[..ncols * ld].chunks_mut(ld))
                        .for_each(upd);
                }
            }
            let two_pi = 2.0 * std::f64::consts::PI;
            let mut a = arg.rem_euclid(two_pi);
            if a > std::f64::consts::PI {
                a -= two_pi;
            }
            Ok((la, a, pmin, pmax))
        },
    )
}

struct CluLogdet {
    n: usize,
    ld: usize,
    rh: Vec<f64>,
    rl: Vec<f64>,
    ih: Vec<f64>,
    il: Vec<f64>,
    par: bool,
}

impl Kernel for CluLogdet {
    type Output = Result<(f64, f64, f64, f64), String>;
    #[inline(always)]
    fn run<S: Simd>(self) -> Self::Output {
        clu_logdet_on::<S>(self.n, self.ld, self.rh, self.rl, self.ih, self.il, self.par)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// deterministic pseudo-random normalized DD matrix, column-major, leading dimension ld_for(n), padding zero
    pub fn mat_pub(n: usize, seed: u64) -> (usize, Vec<f64>, Vec<f64>) {
        mat(n, seed)
    }

    fn mat(n: usize, seed: u64) -> (usize, Vec<f64>, Vec<f64>) {
        let ld = ld_for(n);
        let mut s = seed;
        let mut rnd = || {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            ((s >> 11) as f64) / ((1u64 << 53) as f64) - 0.5
        };
        let mut h = vec![0.0; ld * n];
        let mut l = vec![0.0; ld * n];
        for c in 0..n {
            for r in 0..n {
                let a = rnd() + if r == c { 0.3 } else { 0.0 };
                let b = a * 1e-17 * rnd();
                let (x, y) = two_sum(a, b);
                h[c * ld + r] = x;
                l[c * ld + r] = y;
            }
        }
        (ld, h, l)
    }

    /// block-sparse like the multiple-shooting Jacobian: blocks of size bs on the diagonal and the first block
    /// superdiagonal, a dense last column and row
    fn sparse(n: usize, bs: usize, seed: u64) -> (usize, Vec<f64>, Vec<f64>) {
        let (ld, mut h, mut l) = mat(n, seed);
        for c in 0..n {
            for r in 0..n {
                let (br, bc) = (r / bs, c / bs);
                if !(br == bc || bc == br + 1 || c == n - 1 || r == n - 1) {
                    h[c * ld + r] = 0.0;
                    l[c * ld + r] = 0.0;
                }
            }
        }
        (ld, h, l)
    }

    /// equal as numbers (signed zeros may differ); returns the number of entries whose bits differ
    fn same(a: &[f64], b: &[f64], what: &str) -> usize {
        assert_eq!(a.len(), b.len());
        let mut d = 0;
        for (i, (x, y)) in a.iter().zip(b).enumerate() {
            assert!(x == y, "{what}: entry {i}: {x:e} vs {y:e}");
            d += (x.to_bits() != y.to_bits()) as usize;
        }
        d
    }

    #[test]
    #[allow(clippy::type_complexity)]
    fn blocked_lu_matches_getf2() {
        let cases: Vec<(usize, Vec<f64>, Vec<f64>, usize, &str)> =
            [(96, 1), (97, 2), (130, 3), (200, 4), (257, 5), (333, 6)]
                .iter()
                .map(|&(n, s)| {
                    let (ld, h, l) = mat(n, s);
                    (n, h, l, ld, "dense")
                })
                .chain([(161, 7, 20), (300, 8, 37), (453, 9, 56)].iter().map(|&(n, s, bs)| {
                    let (ld, h, l) = sparse(n, bs, s);
                    (n, h, l, ld, "sparse")
                }))
                .collect();
        for (n, h, l, ld, kind) in cases {
            let a = DDLu::factor_unblocked(n, ld, h.clone(), l.clone(), false).unwrap();
            for par in [false, true] {
                let b = DDLu::factor_blocked(n, ld, h.clone(), l.clone(), par).unwrap();
                assert_eq!(a.perm, b.perm, "perm n={n}");
                let d = same(&a.hi, &b.hi, "hi") + same(&a.lo, &b.lo, "lo");
                eprintln!("{kind} n={n} par={par}: equal; {d} zero entries differ in sign");
            }
        }
    }

    /// the f64 LU (factor_f64) of an f64 matrix: the dd solve with its factors agrees with the dd LU's solution to
    /// f64 accuracy; a perturbed factorization (one pivot scaled by 1 + 1e-6) must fail the check
    #[test]
    fn f64_lu_solves() {
        let check = |n: usize, h: &Vec<f64>, ld: usize, mutate: bool| -> f64 {
            let mut lu = DDLu::factor_f64(n, ld, h.clone(), true).unwrap();
            if mutate {
                let i = ld * (n / 2) + n / 2;
                lu.hi[i] *= 1.0 + 1e-6;
            }
            let dd = DDLu::factor(n, ld, h.clone(), vec![0.0; h.len()], false).unwrap();
            let mut x: Vec<DD> = (0..n).map(|i| DD::from_f64(((i * 37) % 11) as f64 - 5.0)).collect();
            let mut y = x.clone();
            lu.solve(&mut x);
            dd.solve(&mut y);
            let xm = y.iter().map(|v| v.hi.abs()).fold(0.0, f64::max);
            x.iter().zip(&y).map(|(a, b)| (a.hi - b.hi).abs()).fold(0.0, f64::max) / xm
        };
        for (n, sp) in [(90, false), (157, false), (300, true), (453, true)] {
            let (ld, h, _) = if sp { sparse(n, 37, 11) } else { mat(n, 12) };
            let d = check(n, &h, ld, false);
            let dm = check(n, &h, ld, true);
            eprintln!("n {n} sparse {sp}: f64 LU vs dd LU solution {d:.1e}; with a perturbed pivot {dm:.1e}");
            assert!(d < 1e-10, "f64 LU solve differs by {d:e}");
            assert!(dm > 1e-8, "the perturbed factorization is not detected ({dm:e})");
        }
    }

    #[test]
    fn solve_many_is_bitwise_solve() {
        for sp in [false, true] {
            let n = 157;
            let (ld, h, l) = if sp { sparse(n, 20, 9) } else { mat(n, 9) };
            let lu = DDLu::factor(n, ld, h, l, false).unwrap();
            let k = 13;
            let mut s = 7u64;
            let mut bh = vec![0.0; k * n];
            for v in bh.iter_mut() {
                s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                *v = ((s >> 11) as f64) / ((1u64 << 53) as f64) - 0.5;
            }
            bh[3 * n + 5] = 0.0; // a zero entry exercises the skipped update in solve
            let bl = vec![0.0; k * n];
            for transpose in [false, true] {
                for par in [false, true] {
                    let (mut xh, mut xl) = (bh.clone(), bl.clone());
                    lu.solve_many(&mut xh, &mut xl, k, transpose, par);
                    for r in 0..k {
                        let mut b: Vec<DD> = (0..n)
                            .map(|i| DD {
                                hi: bh[r * n + i],
                                lo: bl[r * n + i],
                            })
                            .collect();
                        if transpose {
                            lu.solve_t(&mut b);
                        } else {
                            lu.solve(&mut b);
                        }
                        for i in 0..n {
                            assert_eq!(
                                b[i].hi.to_bits(),
                                xh[r * n + i].to_bits(),
                                "rhs {r} row {i} t={transpose}"
                            );
                            assert_eq!(
                                b[i].lo.to_bits(),
                                xl[r * n + i].to_bits(),
                                "rhs {r} row {i} t={transpose}"
                            );
                        }
                    }
                }
            }
        }
    }

    /// lu_rect_f64 with every column pivoted (nr = ncol = np) is factor_f64: the same pivots, and the same factors
    /// except possibly in the sign of zero entries (see lu_rect_f64)
    #[test]
    fn rect_lu_square_is_factor_f64() {
        for (n, sp) in [(37, false), (96, false), (157, true), (300, true)] {
            let (ld, h, _) = if sp { sparse(n, 20, 21) } else { mat(n, 22) };
            let f = DDLu::factor_f64(n, ld, h.clone(), false).unwrap();
            for par in [false, true] {
                let mut a = h.clone();
                let mut perm = vec![0usize; n];
                lu_rect_f64(n, n, n, ld, &mut a, &mut perm, par).unwrap();
                assert_eq!(perm, f.perm, "perm n={n}");
                let d = same(&f.hi, &a, "factors");
                eprintln!("n {n} sparse {sp} par {par}: equal to factor_f64; {d} zero entries differ in sign");
            }
        }
    }

    /// max |P A - L U| / max |A| over the nr x ncol matrix, with L U for the rectangular factorization: L = (unit L11;
    /// L21) on the first np columns, U = (U11 U12) on the first np rows, and the Schur complement S added in rows
    /// np..nr of the columns np.. (the products in double-double, so the check measures the factorization's error only)
    #[allow(clippy::too_many_arguments)]
    fn rect_residual(nr: usize, ncol: usize, np: usize, ld: usize, a0: &[f64], f: &[f64], perm: &[usize]) -> f64 {
        let mut pa = a0.to_vec();
        for k in 0..np {
            if perm[k] != k {
                for j in 0..ncol {
                    pa.swap(j * ld + k, j * ld + perm[k]);
                }
            }
        }
        let (mut err, mut amax) = (0.0f64, 0.0f64);
        for j in 0..ncol {
            for i in 0..nr {
                let mut s = DD::ZERO;
                for k in 0..np.min(i + 1).min(if j < np { j + 1 } else { np }) {
                    let l = if k == i { 1.0 } else { f[k * ld + i] };
                    s = dd_axpy(s, DD::from_f64(l), DD::from_f64(f[j * ld + k]));
                }
                if i >= np && j >= np {
                    s = s + DD::from_f64(f[j * ld + i]);
                }
                err = err.max((s - DD::from_f64(pa[j * ld + i])).to_f64().abs());
                amax = amax.max(pa[j * ld + i].abs());
            }
        }
        err / amax
    }

    /// lu_rect_f64 on rectangular matrices (np below, at and off multiples of 8 and of the panel width; tall without
    /// trailing columns; dense and block sparse): P A = L U + S to f64 rounding. Control: one multiplier off by a
    /// relative 1e-6 must fail the check.
    #[test]
    fn rect_lu_factors() {
        for (nr, ncol, np, bs) in [
            (40, 60, 24, 0),
            (100, 130, 37, 0),
            (77, 77, 50, 0),
            (64, 64, 64, 0),
            (90, 40, 40, 0),
            (161, 200, 70, 20),
            (200, 233, 96, 30),
        ] {
            let ld = ld_for(nr);
            let n = nr.max(ncol);
            let (sld, h, _) = if bs > 0 { sparse(n, bs, 31) } else { mat(n, 32) };
            let mut a0 = vec![0.0; ld * ncol];
            for j in 0..ncol {
                for i in 0..nr {
                    a0[j * ld + i] = h[j * sld + i];
                }
            }
            for par in [false, true] {
                let mut f = a0.clone();
                let mut perm = vec![0usize; np];
                lu_rect_f64(nr, ncol, np, ld, &mut f, &mut perm, par).unwrap();
                let e = rect_residual(nr, ncol, np, ld, &a0, &f, &perm);
                let mut g = f.clone();
                // the largest multiplier (below the diagonal of the pivoted columns; sparse ones are mostly zero)
                let m = (0..np)
                    .flat_map(|c| (c + 1..nr).map(move |i| c * ld + i))
                    .max_by(|&x, &y| f[x].abs().total_cmp(&f[y].abs()))
                    .unwrap();
                g[m] *= 1.0 + 1e-6;
                let em = rect_residual(nr, ncol, np, ld, &a0, &g, &perm);
                eprintln!(
                    "nr {nr} ncol {ncol} np {np} sparse {} par {par}: residual {e:.1e}; control {em:.1e}",
                    bs > 0
                );
                assert!(e < 1e-13, "P A - L U - S = {e:e}");
                assert!(em > 1e-12, "the perturbed multiplier is not detected ({em:e})");
            }
        }
    }

    /// everything `linalg` dispatches, on one backend, its results flattened
    #[derive(Clone)]
    struct OnBackend {
        n: usize,
        ld: usize,
        h: Vec<f64>,
        l: Vec<f64>,
    }

    impl Kernel for OnBackend {
        type Output = Vec<f64>;
        #[inline(always)]
        fn run<S: Simd>(self) -> Vec<f64> {
            let (n, ld, k) = (self.n, self.ld, 11);
            let u = DDLu::factor_unblocked_on::<S>(n, ld, self.h.clone(), self.l.clone(), true).unwrap();
            let b = DDLu::factor_blocked_on::<S>(n, ld, self.h.clone(), self.l.clone(), true).unwrap();
            let f = DDLu::factor_f64_on::<S>(n, ld, self.h.clone(), true).unwrap();
            let (mut xh, mut xl) = (self.h[..k * n].to_vec(), self.l[..k * n].to_vec());
            b.solve_many_on::<S>(&mut xh, &mut xl, k, false, true);
            let (gh, gl, g) = gram_on::<S>(n, ld, &self.h, &self.l, &self.h[..ld], &self.l[..ld]);
            let g: Vec<f64> = g.iter().flat_map(|d| [d.hi, d.lo]).collect();
            // rectangular: the first 70 columns pivoted (not a multiple of 8), the rest updated
            let (mut r, mut perm) = (self.h.clone(), vec![0usize; 70]);
            lu_rect_f64_on::<S>(n, n, 70, ld, &mut r, &mut perm, true).unwrap();
            let perm: Vec<f64> = perm.iter().map(|&p| p as f64).collect();
            // the single right-hand-side solves, with zeros and negative zeros in b
            let rhs = |n: usize| -> Vec<DD> {
                (0..n)
                    .map(|i| match i % 5 {
                        0 => DD::ZERO,
                        3 => DD { hi: -0.0, lo: 0.0 },
                        _ => DD {
                            hi: self.h[i * 3 % self.h.len()],
                            lo: self.l[i * 7 % self.l.len()],
                        },
                    })
                    .collect()
            };
            let parts = |x: &[DD]| -> Vec<f64> { x.iter().flat_map(|d| [d.hi, d.lo]).collect() };
            let mut x1 = rhs(n);
            u.solve_on::<S>(&mut x1);
            let mut x2 = rhs(n);
            f.solve_on::<S>(&mut x2);
            let mut x3: Vec<f64> = rhs(n).iter().map(|d| d.hi).collect();
            f.solve_hi_on::<S>(&mut x3);
            // the staircase solves, single and 8 lanes at a time
            let st = stair(4, 3);
            let sn = st.n;
            let mut y1 = rhs(sn);
            st.solve_on::<S>(&mut y1);
            let kk = 11;
            let bb: Vec<DD> = (0..kk).flat_map(|_| rhs(sn)).collect();
            let mut ys = Vec::new();
            for t in [false, true] {
                let mut bh: Vec<f64> = bb.iter().map(|d| d.hi).collect();
                let mut bl: Vec<f64> = bb.iter().map(|d| d.lo).collect();
                st.solve_many_on::<S>(&mut bh, &mut bl, kk, t, true);
                ys.push(bh);
                ys.push(bl);
            }
            [
                u.hi,
                u.lo,
                b.hi,
                b.lo,
                f.hi,
                xh,
                xl,
                gh,
                gl,
                g,
                r,
                perm,
                parts(&x1),
                parts(&x2),
                x3,
                parts(&y1),
                ys.concat(),
            ]
            .concat()
        }
    }

    /// a staircase LU with column groups a, b (k of them), a (b = 2 a), each row block filled with deterministic
    /// pseudo-random entries
    fn stair(a: usize, k: usize) -> StaircaseLu {
        let b = 2 * a;
        let n = 2 * a + k * b + 1;
        let mut groups = vec![ColumnGroup {
            param: false,
            zoff: 0,
            zlen: a,
        }];
        for t in 1..=k + 1 {
            groups.push(ColumnGroup {
                param: true,
                zoff: a + (t - 1) * b,
                zlen: if t == k + 1 { a } else { b },
            });
        }
        let rblocks: Vec<(usize, usize)> = (0..=k).map(|blk| (blk * b, b)).collect();
        let gs = groups.clone();
        let fill = |s: usize, w: &mut [f64], wld: usize, r0: usize| -> Result<(), String> {
            let ncol = gs[s].len() + gs[s + 1].len();
            let x = |i: usize, c: usize| (((s * 131 + i * 31 + c * 17) % 97) as f64 - 48.0) / 48.0;
            for c in 0..ncol {
                for i in 0..b {
                    w[c * wld + r0 + i] = x(i, c);
                }
                if s == 0 && c < gs[0].len() {
                    w[c * wld + r0 - 1] = x(99, c) + 0.7;
                }
            }
            Ok(())
        };
        StaircaseLu::factor(n, groups, &rblocks, n - 1, n - 1, fill, false).unwrap()
    }

    // The scalar loops the lane code replaced, as references: each lane version must give their bits.

    fn pivot_ref(col: &[f64], k: usize, n: usize) -> (usize, f64) {
        let (mut p, mut best) = (k, col[k].abs());
        for i in k + 1..n {
            let v = col[i].abs();
            if v > best {
                best = v;
                p = i;
            }
        }
        (p, best)
    }

    fn solve_ref(lu: &DDLu, b: &mut [DD]) {
        let n = lu.n;
        for k in 0..n {
            let p = lu.perm[k];
            if p != k {
                b.swap(k, p);
            }
        }
        for k in 0..n {
            let nt = -b[k];
            if nt.hi == 0.0 {
                continue;
            }
            for i in k + 1..n {
                b[i] = dd_axpy(b[i], lu.at(i, k), nt);
            }
        }
        for k in (0..n).rev() {
            b[k] = b[k] / lu.at(k, k);
            let nt = -b[k];
            for i in 0..k {
                b[i] = dd_axpy(b[i], lu.at(i, k), nt);
            }
        }
    }

    fn refine_ref(lu: &DDLu, b: &[QD], steps: usize, mut resid: impl FnMut(&[QD], &mut [QD])) -> Vec<QD> {
        let mut d: Vec<DD> = b.iter().map(|v| v.to_dd()).collect();
        solve_ref(lu, &mut d);
        let mut x: Vec<QD> = d.iter().map(|&v| QD::from_dd(v)).collect();
        let mut r = vec![QD::ZERO; lu.n];
        for _ in 0..steps {
            resid(&x, &mut r);
            for (di, ri) in d.iter_mut().zip(&r) {
                *di = ri.to_dd();
            }
            solve_ref(lu, &mut d);
            for (xi, di) in x.iter_mut().zip(&d) {
                *xi = *xi + QD::from_dd(*di);
            }
        }
        x
    }

    fn solve_hi_ref(lu: &DDLu, b: &mut [f64]) {
        let (n, ld) = (lu.n, lu.ld);
        for k in 0..n {
            let p = lu.perm[k];
            if p != k {
                b.swap(k, p);
            }
        }
        for k in 0..n {
            let nt = -b[k];
            if nt == 0.0 {
                continue;
            }
            for i in k + 1..n {
                b[i] = lu.hi[k * ld + i].mul_add(nt, b[i]);
            }
        }
        for k in (0..n).rev() {
            b[k] /= lu.hi[k * ld + k];
            let nt = -b[k];
            for i in 0..k {
                b[i] = lu.hi[k * ld + i].mul_add(nt, b[i]);
            }
        }
    }

    fn stair_solve_ref(lu: &StaircaseLu, b: &mut [DD]) {
        let ns = lu.steps.len();
        let mut carry: Vec<DD> = Vec::new();
        let mut ys: Vec<Vec<DD>> = Vec::new();
        for (s, st) in lu.steps.iter().enumerate() {
            let mut v = carry;
            if s + 1 < ns {
                v.push(if s == 0 { b[lu.irow0] } else { DD::ZERO });
                v.extend_from_slice(&b[st.roff..st.roff + st.rlen]);
            }
            for k in 0..st.np {
                let p = st.perm[k];
                if p != k {
                    v.swap(k, p);
                }
            }
            for k in 0..st.np {
                let nt = -v[k];
                if nt.hi == 0.0 {
                    continue;
                }
                for i in k + 1..st.nr {
                    v[i] = dd_axpy(v[i], f64dd(StaircaseLu::lu(st, i, k)), nt);
                }
            }
            carry = v.split_off(st.np);
            ys.push(v);
        }
        let mut xr: Vec<DD> = Vec::new();
        let mut xs: Vec<Vec<DD>> = vec![Vec::new(); ns];
        for s in (0..ns).rev() {
            let st = &lu.steps[s];
            let mut y = std::mem::take(&mut ys[s]);
            for j in (0..st.nrc).rev() {
                let nt = -xr[j];
                if nt.hi == 0.0 {
                    continue;
                }
                for i in 0..st.np {
                    y[i] = dd_axpy(y[i], f64dd(st.u12[j * st.ldu + i]), nt);
                }
            }
            for k in (0..st.np).rev() {
                y[k] = y[k] / f64dd(StaircaseLu::lu(st, k, k));
                let nt = -y[k];
                for i in 0..k {
                    y[i] = dd_axpy(y[i], f64dd(StaircaseLu::lu(st, i, k)), nt);
                }
            }
            xr = y.clone();
            xs[s] = y;
        }
        for (s, g) in lu.groups.iter().enumerate() {
            let o = g.param as usize;
            b[g.zoff..g.zoff + g.zlen].copy_from_slice(&xs[s][o..o + g.zlen]);
            if s == lu.gparam {
                b[lu.iparam] = xs[s][0];
            }
        }
    }

    #[derive(Clone)]
    struct LanesMatchScalar;

    impl Kernel for LanesMatchScalar {
        type Output = ();
        #[inline(always)]
        fn run<S: Simd>(self) {
            let mut r = 0x9e37_79b9_7f4a_7c15u64;
            let mut next = move || {
                r ^= r << 13;
                r ^= r >> 7;
                r ^= r << 17;
                r
            };
            // pivot search: random magnitudes with ties, signed zeros, infinities and NaNs, every k and n
            let pick = |x: u64| match x % 9 {
                0 => 0.0,
                1 => -0.0,
                2 => 1.0,
                3 => -1.0,
                4 => f64::NAN,
                5 => f64::INFINITY,
                _ => ((x >> 8) % 1000) as f64 / 100.0 - 5.0,
            };
            let mut ties = 0;
            for _ in 0..3000 {
                let n = 1 + (next() % 40) as usize;
                let k = (next() % n as u64) as usize;
                let col: Vec<f64> = (0..ld_for(n)).map(|_| pick(next())).collect();
                let (p, b) = pivot_search::<S>(&col, k, n);
                let (q, c) = pivot_ref(&col, k, n);
                assert!(
                    p == q && b.to_bits() == c.to_bits(),
                    "{}: pivot {p} {b} vs {q} {c}",
                    S::NAME
                );
                // the last row with the largest value, which the lanes must not pick
                ties += (k..n).rev().find(|&i| col[i].abs() == c).is_some_and(|i| i != q) as usize;
            }
            assert!(
                ties > 100,
                "control: too few ties ({ties}) to tell the first maximum from the last"
            );
            // axpy_rows and fma_rows against the scalar loops, every range in 0..40
            for _ in 0..2000 {
                let len = 40;
                let (lo, hi) = {
                    let a = (next() % 41) as usize;
                    let b = (next() % 41) as usize;
                    (a.min(b), a.max(b))
                };
                // finite values, with negative zeros
                let v = |x: u64| {
                    let y = if x.is_multiple_of(7) { -0.0 } else { pick(x) };
                    if y.is_finite() {
                        y
                    } else {
                        2.5
                    }
                };
                let bh: Vec<f64> = (0..len).map(|_| v(next())).collect();
                let bl: Vec<f64> = bh.iter().map(|x| x * 1e-17).collect();
                let lh: Vec<f64> = (0..len).map(|_| v(next())).collect();
                let ll: Vec<f64> = lh.iter().map(|x| x * -1e-17).collect();
                let nt = DD::new(v(next()), 0.0);
                let (mut gh, mut gl) = (bh.clone(), bl.clone());
                axpy_rows::<S>(&mut gh, &mut gl, &lh, Some(&ll), lo, hi, nt);
                let mut g1 = bh.clone();
                fma_rows::<S>(&mut g1, &lh, lo, hi, nt.hi);
                for i in 0..len {
                    let (w, w1) = if i >= lo && i < hi {
                        (
                            dd_axpy(DD { hi: bh[i], lo: bl[i] }, DD { hi: lh[i], lo: ll[i] }, nt),
                            lh[i].mul_add(nt.hi, bh[i]),
                        )
                    } else {
                        (DD { hi: bh[i], lo: bl[i] }, bh[i])
                    };
                    assert!(
                        gh[i].to_bits() == w.hi.to_bits() && gl[i].to_bits() == w.lo.to_bits(),
                        "{}: axpy_rows {lo}..{hi} row {i}",
                        S::NAME
                    );
                    assert_eq!(
                        g1[i].to_bits(),
                        w1.to_bits(),
                        "{}: fma_rows {lo}..{hi} row {i}",
                        S::NAME
                    );
                }
            }
            // the solves
            for (n, seed) in [(1usize, 1u64), (7, 2), (8, 3), (9, 4), (33, 5), (100, 6)] {
                let (ld, mut h, mut l) = mat(n, seed);
                for i in (0..ld * n).step_by(5) {
                    (h[i], l[i]) = if i % 2 == 0 { (0.0, 0.0) } else { (-0.0, 0.0) };
                }
                for j in 0..n {
                    h[j * ld + j] += 4.0;
                }
                let lu = DDLu::factor_unblocked_on::<S>(n, ld, h, l, false).unwrap();
                let b: Vec<DD> = (0..n)
                    .map(|i| match i % 4 {
                        0 => DD::ZERO,
                        1 => DD { hi: -0.0, lo: 0.0 },
                        _ => DD::new(lu.hi[i] + 0.5, 1e-18),
                    })
                    .collect();
                let (mut x, mut y) = (b.clone(), b.clone());
                lu.solve_on::<S>(&mut x);
                solve_ref(&lu, &mut y);
                for i in 0..n {
                    assert!(
                        x[i].hi.to_bits() == y[i].hi.to_bits() && x[i].lo.to_bits() == y[i].lo.to_bits(),
                        "{}: solve n {n} row {i}",
                        S::NAME
                    );
                }
                // the refinement to quad-double, with a residual that is not the true one (any function will do)
                let bq: Vec<QD> = b.iter().map(|&v| QD::from_dd(v).add_f(1e-20)).collect();
                let resid = |x: &[QD], r: &mut [QD]| {
                    for i in 0..x.len() {
                        r[i] = bq[i] - x[i].mul_f(0.75);
                    }
                };
                let x = lu.solve_refine_qd_on::<S>(&bq, 3, resid);
                let y = refine_ref(&lu, &bq, 3, resid);
                for i in 0..n {
                    assert!(
                        x[i].x
                            .iter()
                            .zip(y[i].x.iter())
                            .all(|(p, q)| p.to_bits() == q.to_bits()),
                        "{}: solve_refine_qd n {n} row {i}",
                        S::NAME
                    );
                }
                let mut x: Vec<f64> = b.iter().map(|d| d.hi).collect();
                let mut y = x.clone();
                lu.solve_hi_on::<S>(&mut x);
                solve_hi_ref(&lu, &mut y);
                assert_eq!(bits_differ(&x, &y), 0, "{}: solve_hi n {n}", S::NAME);
            }
            for (a, k) in [(2usize, 1usize), (4, 3), (5, 6)] {
                let st = stair(a, k);
                let n = st.n;
                let b: Vec<DD> = (0..n)
                    .map(|i| match i % 4 {
                        0 => DD::ZERO,
                        1 => DD { hi: -0.0, lo: 0.0 },
                        _ => DD::new((i % 13) as f64 - 6.0, 1e-18),
                    })
                    .collect();
                let (mut x, mut y) = (b.clone(), b.clone());
                st.solve_on::<S>(&mut x);
                stair_solve_ref(&st, &mut y);
                for i in 0..n {
                    assert!(
                        x[i].hi.to_bits() == y[i].hi.to_bits() && x[i].lo.to_bits() == y[i].lo.to_bits(),
                        "{}: staircase solve a {a} k {k} row {i}",
                        S::NAME
                    );
                }
            }
        }
    }

    /// The lane code (pivot search, row updates, the single solves, the quad-double refinement) gives the scalar loops'
    /// bits on every backend.
    /// Control: the pivot inputs have ties, so a search that took the last maximum would fail.
    #[test]
    fn lane_code_matches_the_scalar_loops() {
        simd::for_each_available(LanesMatchScalar);
    }

    /// Control for the solve references: a solve whose update rounds the product to f64 first differs from them.
    #[test]
    fn control_rounded_update_differs() {
        let (n, seed) = (20, 9);
        let (ld, h, l) = mat(n, seed);
        let lu = DDLu::factor(n, ld, h, l, false).unwrap();
        let b: Vec<DD> = (0..n).map(|i| DD::new(i as f64 - 9.5, 1e-18)).collect();
        let mut y = b.clone();
        solve_ref(&lu, &mut y);
        let mut z = b.clone();
        for k in 0..n {
            let p = lu.perm[k];
            if p != k {
                z.swap(k, p);
            }
        }
        for k in 0..n {
            let nt = -z[k];
            for i in k + 1..n {
                z[i] = z[i] + DD::from_f64(lu.at(i, k).hi * nt.hi);
            }
        }
        for k in (0..n).rev() {
            z[k] = z[k] / lu.at(k, k);
            let nt = -z[k];
            for i in 0..k {
                z[i] = z[i] + DD::from_f64(lu.at(i, k).hi * nt.hi);
            }
        }
        assert!((0..n).any(|i| z[i].hi.to_bits() != y[i].hi.to_bits() || z[i].lo.to_bits() != y[i].lo.to_bits()));
    }

    fn bits_differ(a: &[f64], b: &[f64]) -> usize {
        assert_eq!(a.len(), b.len());
        a.iter().zip(b).filter(|(x, y)| x.to_bits() != y.to_bits()).count()
    }

    /// The factors, the solutions (dense and staircase, one and many right-hand sides) and the Gram matrix are bitwise
    /// the same on every backend this CPU runs.
    #[test]
    fn every_backend_gives_the_same_bits() {
        let n = 157;
        let (ld, h, l) = sparse(n, 20, 5);
        let ran = simd::for_each_available(OnBackend { n, ld, h, l });
        let (first, want) = (ran[0].0, &ran[0].1);
        for (name, got) in &ran[1..] {
            assert_eq!(bits_differ(want, got), 0, "{name} against {first}");
        }
        // control: one flipped low bit is caught by the same comparison
        let mut wrong = want.clone();
        let m = want.len() / 2;
        wrong[m] = f64::from_bits(wrong[m].to_bits() ^ 1);
        assert_eq!(bits_differ(want, &wrong), 1);
        println!(
            "linalg bitwise the same on {:?}",
            ran.iter().map(|r| r.0).collect::<Vec<_>>()
        );
    }
}

#[cfg(test)]
mod bench {
    use super::*;
    use std::time::Instant;

    /// cargo test --release --lib bench_lu -- --ignored --nocapture   (env N, T)
    #[test]
    #[ignore]
    fn bench_lu() {
        let n: usize = std::env::var("N").ok().and_then(|v| v.parse().ok()).unwrap_or(1153);
        let t: usize = std::env::var("T").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
        let (n, ld, h, l) = match std::env::var("FILE") {
            Ok(f) => {
                let b = std::fs::read(f).unwrap();
                let v: Vec<f64> = b.chunks(8).map(|c| f64::from_le_bytes(c.try_into().unwrap())).collect();
                let n = v[0] as usize;
                let ld = ld_for(n);
                (n, ld, v[1..1 + ld * n].to_vec(), v[1 + ld * n..1 + 2 * ld * n].to_vec())
            }
            Err(_) => {
                let (ld, h, l) = super::tests::mat_pub(n, 3);
                (n, ld, h, l)
            }
        };
        let reps: usize = std::env::var("REPS").ok().and_then(|v| v.parse().ok()).unwrap_or(3);
        let pool = rayon::ThreadPoolBuilder::new().num_threads(t).build().unwrap();
        let (mut t1, mut t2, mut t3, mut t4) = (1e9f64, 1e9f64, 1e9f64, 1e9f64);
        for _ in 0..reps {
            let t0 = Instant::now();
            let a = pool.install(|| DDLu::factor_unblocked(n, ld, h.clone(), l.clone(), true).unwrap());
            t1 = t1.min(t0.elapsed().as_secs_f64());
            let t0 = Instant::now();
            let b = pool.install(|| DDLu::factor_blocked(n, ld, h.clone(), l.clone(), true).unwrap());
            t2 = t2.min(t0.elapsed().as_secs_f64());
            assert_eq!(a.hi, b.hi);
            assert_eq!(a.lo, b.lo);
            let k = 24;
            let rhs: Vec<f64> = (0..k * n).map(|i| ((i * 7919) % 1000) as f64 / 1000.0 - 0.5).collect();
            let t0 = Instant::now();
            for r in 0..k {
                let mut v: Vec<DD> = (0..n)
                    .map(|i| DD {
                        hi: rhs[r * n + i],
                        lo: 0.0,
                    })
                    .collect();
                b.solve_t(&mut v);
                b.solve(&mut v);
            }
            t3 = t3.min(t0.elapsed().as_secs_f64());
            let t0 = Instant::now();
            let (mut xh, mut xl) = (rhs.clone(), vec![0.0; k * n]);
            pool.install(|| b.solve_many(&mut xh, &mut xl, k, true, true));
            let mut xl2 = vec![0.0; k * n];
            pool.install(|| b.solve_many(&mut xh, &mut xl2, k, false, true));
            t4 = t4.min(t0.elapsed().as_secs_f64());
        }
        {
            println!("n {n} threads {t}: getf2 {t1:.3}s  blocked {t2:.3}s  ({:.2}x)   24 x (solve_t + solve): {t3:.3}s  solve_many: {t4:.4}s ({:.0}x)",
                     t1 / t2, t3 / t4);
        }
    }
}
