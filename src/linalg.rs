//! Dense double-double LU with partial pivoting (LAPACK getf2 order), column-major with the leading dimension
//! padded to a multiple of 8 so the trailing update runs on 8-row lane vectors, columns updated in parallel (rayon)
//! for large matrices; the same factorization blocked in plain f64 (LAPACK's right-looking getrf) for
//! mixed-precision use, solves and transpose solves in double-double with either set of factors, and Gram matrices.
use crate::dd::{two_prod, two_sum, DD};
use crate::dv;
use crate::native::DV;
use crate::native::V8;
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
fn axpy8(a: DV, l: DV, nt: DV) -> DV {
    let (p, pe) = dv::two_prod(l.hi, nt.hi);
    let pe = l.hi.fma(nt.lo, pe);
    let pe = l.lo.fma(nt.hi, pe);
    let (s, t) = dv::two_sum(a.hi, p);
    let e = a.lo.add(t.add(pe));
    let (h, lo) = dv::two_sum(s, e);
    DV { hi: h, lo }
}

#[inline(always)]
fn dd_axpy(a: DD, l: DD, nt: DD) -> DD {
    let (p, pe) = two_prod(l.hi, nt.hi);
    let pe = l.hi.mul_add(nt.lo, pe);
    let pe = l.lo.mul_add(nt.hi, pe);
    let (s, t) = two_sum(a.hi, p);
    let e = a.lo + (t + pe);
    let (h, lo) = two_sum(s, e);
    DD { hi: h, lo }
}

/// Blocked LU: matrices at least this large take `factor_blocked`; NB: panel width; CW: columns per parallel task;
/// NC: columns per register tile.
pub const BLOCKED_MIN: usize = 96;
const NB: usize = 32;
const CW: usize = 8;
const NC: usize = 4;
const TR: usize = 2;

/// Scalar negation of every lane (-x, as DD's Neg: keeps signed zeros as the scalar solve has them).
#[inline(always)]
fn neg_lanes(v: DV) -> DV {
    let (h, l) = (v.hi.to_array(), v.lo.to_array());
    DV {
        hi: V8::from_array(h.map(|x| -x)),
        lo: V8::from_array(l.map(|x| -x)),
    }
}

/// Scalar DD division of every lane by d.
#[inline(always)]
fn div_lanes(v: DV, d: DD) -> DV {
    let (h, l) = (v.hi.to_array(), v.lo.to_array());
    let mut qh = [0.0f64; 8];
    let mut ql = [0.0f64; 8];
    for r in 0..8 {
        let q = DD { hi: h[r], lo: l[r] } / d;
        qh[r] = q.hi;
        ql[r] = q.lo;
    }
    DV {
        hi: V8::from_array(qh),
        lo: V8::from_array(ql),
    }
}

/// u, except the lanes r with z[r] == 0, which keep old (the scalar solve skips those updates).
#[inline(always)]
fn keep_lanes(u: DV, old: DV, z: &[f64; 8]) -> DV {
    let (mut uh, mut ul) = (u.hi.to_array(), u.lo.to_array());
    let (oh, ol) = (old.hi.to_array(), old.lo.to_array());
    for r in 0..8 {
        if z[r] == 0.0 {
            uh[r] = oh[r];
            ul[r] = ol[r];
        }
    }
    DV {
        hi: V8::from_array(uh),
        lo: V8::from_array(ul),
    }
}

/// getf2 on the panel columns j0..j0+jb (slices ph / pl hold just those columns, leading dimension ld): pivot search,
/// row swaps within the panel, scaling, and updates of the later panel columns, as `factor_unblocked` does them,
/// except that updates which cannot change a value are skipped: 8-row blocks whose multipliers are all exactly zero,
/// and columns whose pivot-row entry is exactly zero (a - 0 t and a - l 0 return a; at most the sign of a zero differs).
fn panel_getf2(
    n: usize,
    ld: usize,
    j0: usize,
    jb: usize,
    ph: &mut [f64],
    pl: &mut [f64],
    perm: &mut [usize],
) -> Result<(), String> {
    let mut mh = vec![0.0f64; ld];
    let mut ml = vec![0.0f64; ld];
    let mut blocks: Vec<usize> = Vec::with_capacity(ld / 8);
    for c in 0..jb {
        let k = j0 + c;
        let ck = c * ld;
        let mut p = k;
        let mut best = ph[ck + k].abs();
        for i in k + 1..n {
            let v = ph[ck + i].abs();
            if v > best {
                best = v;
                p = i;
            }
        }
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
        for i in k + 1..n {
            if ph[ck + i] == 0.0 && pl[ck + i] == 0.0 {
                continue;
            }
            let v = DD {
                hi: ph[ck + i],
                lo: pl[ck + i],
            } * inv;
            ph[ck + i] = v.hi;
            pl[ck + i] = v.lo;
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
            let nt = DV::splat(DD { hi: -ch[k], lo: -cl[k] });
            for &i in &blocks {
                let a = DV::load(&ch[i..i + 8], &cl[i..i + 8]);
                let l = DV::load(&mh[i..i + 8], &ml[i..i + 8]);
                axpy8(a, l, nt).store(&mut ch[i..i + 8], &mut cl[i..i + 8]);
            }
        }
    }
    Ok(())
}

/// The trailing update of one panel on the given columns (offsets into ch / cl, leading dimension ld) and 8-row blocks
/// (row offsets): entry -= l_ik u_kj for the panel's k in order, with TR row blocks x NC columns in registers.
/// nt[j]: offset of column j's -u values (jb each) in nth / ntl; ph / pl: packed multipliers, [row block][k][lane].
#[allow(clippy::too_many_arguments)]
fn gemm(
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
    let mut j = 0;
    while j < cols.len() {
        let w = (cols.len() - j).min(NC);
        let mut r = 0;
        while r < rows.len() {
            let h = (rows.len() - r).min(TR);
            match (h, w) {
                (TR, NC) => tile_rows::<TR, NC>(ld, jb, ch, cl, &cols[j..], &nto[j..], nth, ntl, &rows[r..], ph, pl),
                (1, NC) => tile_rows::<1, NC>(ld, jb, ch, cl, &cols[j..], &nto[j..], nth, ntl, &rows[r..], ph, pl),
                (TR, _) => {
                    for q in 0..w {
                        tile_rows::<TR, 1>(
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
                        tile_rows::<1, 1>(
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
}

#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn tile_rows<const R: usize, const W: usize>(
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
    let mut acc = [[DV::zero(); W]; R];
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
    pub fn factor_unblocked(
        n: usize,
        ld: usize,
        mut hi: Vec<f64>,
        mut lo: Vec<f64>,
        par: bool,
    ) -> Result<DDLu, String> {
        assert!(ld.is_multiple_of(8) && ld >= n && hi.len() >= ld * n && lo.len() >= ld * n);
        let mut perm = vec![0usize; n];
        let mut mh = vec![0.0f64; ld];
        let mut ml = vec![0.0f64; ld];
        for k in 0..n {
            let ck = k * ld;
            let mut p = k;
            let mut best = hi[ck + k].abs();
            for i in k + 1..n {
                let v = hi[ck + i].abs();
                if v > best {
                    best = v;
                    p = i;
                }
            }
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
            for i in k + 1..n {
                let v = DD {
                    hi: hi[ck + i],
                    lo: lo[ck + i],
                } * inv;
                hi[ck + i] = v.hi;
                lo[ck + i] = v.lo;
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
                let nt = DV::splat(DD { hi: -ch[k], lo: -cl[k] });
                let mut i = r0;
                while i < ld {
                    let a = DV::load(&ch[i..i + 8], &cl[i..i + 8]);
                    let l = DV::load(&mh[i..i + 8], &ml[i..i + 8]);
                    axpy8(a, l, nt).store(&mut ch[i..i + 8], &mut cl[i..i + 8]);
                    i += 8;
                }
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
    pub fn factor_blocked(n: usize, ld: usize, mut hi: Vec<f64>, mut lo: Vec<f64>, par: bool) -> Result<DDLu, String> {
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
            panel_getf2(n, ld, j0, jb, pan_h, pan_l, &mut perm)?;
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
                        let nt = DV::splat(DD { hi: a, lo: b });
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
                    gemm(ld, jb, ch, cl, &cols, &nto, &nth, &ntl, &rows, &ph, &pl);
                }
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
    }

    /// Solve A x = b (transpose: A^T x = b) for nrhs right-hand sides at once, b row-major (nrhs, n) as (hi, lo),
    /// in place. Eight right-hand sides share each lane vector, and the groups of eight run in parallel when par.
    /// Each lane does exactly the operations of `solve` / `solve_t`, so every row of the result is bitwise the
    /// single right-hand-side solve.
    pub fn solve_many(&self, bh: &mut [f64], bl: &mut [f64], nrhs: usize, transpose: bool, par: bool) {
        let n = self.n;
        assert!(bh.len() >= nrhs * n && bl.len() >= nrhs * n);
        let ng = nrhs.div_ceil(8);
        let (bh0, bl0): (&[f64], &[f64]) = (bh, bl);
        let rg = self.col_ranges();
        let rg = &rg;
        let group = |g: usize| -> Vec<DV> {
            let live = (nrhs - 8 * g).min(8);
            let mut v = vec![DV::zero(); n];
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
        };
        let out: Vec<Vec<DV>> = if par && ng > 1 {
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
    fn solve_dv(&self, b: &mut [DV], rg: &[(usize, usize)]) {
        let n = self.n;
        for k in 0..n {
            let p = self.perm[k];
            if p != k {
                b.swap(k, p);
            }
        }
        for k in 0..n {
            let nt = neg_lanes(b[k]);
            let z = nt.hi.to_array();
            let nz = z.iter().filter(|&&x| x == 0.0).count();
            if nz == 8 {
                continue;
            }
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
                b[i] = if nz == 0 { u } else { keep_lanes(u, b[i], &z) };
            }
        }
        for k in (0..n).rev() {
            let q = div_lanes(b[k], self.at(k, k));
            b[k] = q;
            let nt = neg_lanes(q);
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
    }

    /// `solve_t` lane by lane.
    fn solve_t_dv(&self, b: &mut [DV], rg: &[(usize, usize)]) {
        let n = self.n;
        let mut nb = vec![DV::zero(); n];
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
            b[k] = div_lanes(acc, self.at(k, k));
            nb[k] = neg_lanes(b[k]);
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
            nb[k] = neg_lanes(acc);
        }
        for k in (0..n).rev() {
            let p = self.perm[k];
            if p != k {
                b.swap(k, p);
            }
        }
    }

    #[inline(always)]
    fn at(&self, i: usize, j: usize) -> DD {
        DD {
            hi: self.hi[j * self.ld + i],
            lo: self.lo[j * self.ld + i],
        }
    }

    /// Solve A x = b in place (b: n values).
    pub fn solve(&self, b: &mut [DD]) {
        let n = self.n;
        for k in 0..n {
            let p = self.perm[k];
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
                b[i] = dd_axpy(b[i], self.at(i, k), nt);
            }
        }
        for k in (0..n).rev() {
            b[k] = b[k] / self.at(k, k);
            let nt = -b[k];
            for i in 0..k {
                b[i] = dd_axpy(b[i], self.at(i, k), nt);
            }
        }
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
        let (n, ld) = (self.n, self.ld);
        for k in 0..n {
            let p = self.perm[k];
            if p != k {
                b.swap(k, p);
            }
        }
        for k in 0..n {
            let nt = -b[k];
            if nt == 0.0 {
                continue;
            }
            let col = &self.hi[k * ld..k * ld + n];
            for i in k + 1..n {
                b[i] = col[i].mul_add(nt, b[i]);
            }
        }
        for k in (0..n).rev() {
            b[k] /= self.hi[k * ld + k];
            let nt = -b[k];
            let col = &self.hi[k * ld..k * ld + k];
            for i in 0..k {
                b[i] = col[i].mul_add(nt, b[i]);
            }
        }
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
fn panel_getf2_f64(
    n: usize,
    ld: usize,
    j0: usize,
    jb: usize,
    pa: &mut [f64],
    perm: &mut [usize],
) -> Result<(), String> {
    let mut m = vec![0.0f64; ld];
    let mut blocks: Vec<usize> = Vec::with_capacity(ld / 8);
    for c in 0..jb {
        let k = j0 + c;
        let ck = c * ld;
        let mut p = k;
        let mut best = pa[ck + k].abs();
        for i in k + 1..n {
            let v = pa[ck + i].abs();
            if v > best {
                best = v;
                p = i;
            }
        }
        if best == 0.0 || !best.is_finite() {
            return Err(format!("singular or non-finite pivot at column {k} ({best})"));
        }
        perm[k] = p;
        if p != k {
            for j in 0..jb {
                pa.swap(j * ld + k, j * ld + p);
            }
        }
        let inv = 1.0 / pa[ck + k];
        for i in k + 1..n {
            pa[ck + i] *= inv;
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
            let nt = V8::splat(-ch[k]);
            for &i in &blocks {
                V8::load(&m[i..i + 8])
                    .fma(nt, V8::load(&ch[i..i + 8]))
                    .store(&mut ch[i..i + 8]);
            }
        }
    }
    Ok(())
}

#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn tile_rows_f64<const R: usize, const W: usize>(
    ch: &mut [f64],
    cols: &[usize],
    nto: &[usize],
    nt: &[f64],
    rows: &[(usize, usize)],
    pk: &[f64],
    jb: usize,
) {
    let mut acc = [[V8::zero(); W]; R];
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
fn gemm_f64(jb: usize, ch: &mut [f64], cols: &[usize], nto: &[usize], nt: &[f64], rows: &[(usize, usize)], pk: &[f64]) {
    const TR64: usize = 4;
    let mut j = 0;
    while j < cols.len() {
        let w = (cols.len() - j).min(NC);
        let mut r = 0;
        while r < rows.len() {
            let h = (rows.len() - r).min(TR64);
            if w == NC && h == TR64 {
                tile_rows_f64::<TR64, NC>(ch, &cols[j..], &nto[j..], nt, &rows[r..], pk, jb);
            } else {
                for q in 0..w {
                    for rr in 0..h {
                        tile_rows_f64::<1, 1>(ch, &cols[j + q..], &nto[j + q..], nt, &rows[r + rr..], pk, jb);
                    }
                }
            }
            r += h;
        }
        j += w;
    }
}

impl DDLu {
    /// The blocked LU of `factor_blocked` (the same panels, row swaps, skipped zero blocks and register tiles) in plain
    /// f64 on an f64 matrix: an f64 LU with partial pivoting (backward stable: L U = P (A + E), |E| of the order of
    /// n eps |L| |U|), stored with lo = 0 so that the double-double solves (solve, solve_t, solve_many, chord) use these
    /// factors as they are. For the mixed-precision Newton step, whose Jacobian is f64 to begin with.
    pub fn factor_f64(n: usize, ld: usize, mut a: Vec<f64>, par: bool) -> Result<DDLu, String> {
        assert!(ld.is_multiple_of(8) && ld >= n && a.len() >= ld * n);
        let mut perm = vec![0usize; n];
        let mut j0 = 0;
        while j0 < n {
            let jb = NB.min(n - j0);
            let je = j0 + jb;
            let (left, rest) = a.split_at_mut(j0 * ld);
            let (pan, right) = rest.split_at_mut(jb * ld);
            panel_getf2_f64(n, ld, j0, jb, pan, &mut perm)?;
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
                        let tv = V8::splat(t);
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
                    gemm_f64(jb, ch, &cols, &nto, &nt, &rows, &pk);
                }
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
    }
}

/// Gram matrix G = J^T J and g = J^T b for a column-major J (n x n, leading dimension ld): G column-major with
/// leading dimension ld (only what LU needs; G is symmetric and filled completely).
pub fn gram(n: usize, ld: usize, jh: &[f64], jl: &[f64], bh: &[f64], bl: &[f64]) -> (Vec<f64>, Vec<f64>, Vec<DD>) {
    let dot = |a: usize, bh2: &[f64], bl2: &[f64]| -> DD {
        let mut acc = dv::DotAcc::zero();
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

#[allow(dead_code)]
fn _unused(_: V8) {}

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
