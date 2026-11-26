import ExpansionBounds.DDExpEval
import ExpansionBounds.LogThm

/-!
# Proposition 44 (`prop:ddexplog`): `DD::ln`, for a case

Theorem 42 (`thm:log`) read with `n = 2`, with no part bounds and each `G_OP`'s error replaced by `e_OP Z̄`. The
start `y_0` is one float within `E` of `ln x` (`DDLog.lean`), `(k, t)` are EXP's reduction and core on `-y_0`
(`DDExpRed.lean`, `DDExpCore.lean`, `m = 0`), and

* step (3): `x' = 2^k x` and `φ = DWPlusFP(x', -1)`, which is `x' - 1` exactly (Lemma 41; a hypothesis here, as the
  relative bound of DWPlusFP does not give it);
* step (4): `c = ADD(φ, t)` where `min(e_φ, e_t) < -B - 13`, otherwise `c = ADD(ADD(φ, t), p)` with
  `p = 2^{e_φ+e_t} MUL(2^{-e_φ}φ, 2^{-e_t}t)`;
* step (5): `y_c = c` where `e_c < -B - 13`, otherwise `h` by Horner's rule on the `F'_i` with
  `c ⊗ v = 2^{e_c} MUL(2^{-e_c}c, v)` and `y_c = c ⊗ DWPlusFP(c ⊗ h, 1)`; the result is `DWPlusFP(y_c, y_0)`.

The bounds are those of `Log.bin` in `explog_consts.py` for double words, before its roundings up (`ddLogEc`,
`ddLogP`, `ddLogBound`).

Each scaling back is rounded by a function that moves a part by at most `η` and keeps a double word whose high part
is at least a floor `lo` (`SclDW`). A scaled-back product `z` of `a` and `b` has `|z_h|(1 + u) ≥ (1 - e_P)|ab|`, so
its floor is asked as `lo(1 + u) ≤ (1 - e_P)|ab|` (`dd_mul_scaled`), and the theorem asks it through lower bounds of
the factors.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- `c ⊗ v = 2^e MUL(2^{-e} c, v)`, its scaling back rounded by `S` -/
noncomputable def ddSmul (O : DWOps) (S : ℝ × ℝ → ℝ × ℝ) (e : ℤ) (a b : ℝ × ℝ) : ℝ × ℝ :=
  S (dwScale e (O.mul (dwScale (-e) a) b))

/-- step (3): `x' = 2^k x`, rounded by `S`, and `φ = DWPlusFP(x', -1)` -/
noncomputable def ddLogPhi (O : DWOps) (S : ℝ × ℝ → ℝ × ℝ) (k : ℤ) (x : ℝ × ℝ) : ℝ × ℝ :=
  O.addF (S (dwScale k x)) (-1)

/-- step (4): `c = ADD(φ, t)` where `min(e_φ, e_t) < -B - 13`; otherwise `c = ADD(ADD(φ, t), p)`, the scalings back
of `p` rounded by `S` -/
noncomputable def ddLogC (O : DWOps) (S : ℝ × ℝ → ℝ × ℝ) (B eφ et : ℤ) (φ t : ℝ × ℝ) : ℝ × ℝ :=
  if min eφ et < -B - 13 then O.add φ t
  else O.add (O.add φ t) (S (dwScale (eφ + et) (O.mul (dwScale (-eφ) φ) (dwScale (-et) t))))

/-- step (5): `y_c = c` where `e_c < -B - 13`; otherwise `h` by Horner's rule on the `F'_i` with `c ⊗ v`, and
`y_c = c ⊗ DWPlusFP(c ⊗ h, 1)` -/
noncomputable def ddLogYc (O : DWOps) (S : ℝ × ℝ → ℝ × ℝ) (B ec : ℤ) (c : ℝ × ℝ) (F' : ℕ → ℝ × ℝ) (q : ℕ) :
    ℝ × ℝ :=
  if ec < -B - 13 then c else
    ddSmul O S ec c (O.addF (ddSmul O S ec c (ddHornerP O (ddSmul O S ec c) F' q (q - 2))) 1)

/-- LOG after its start `y_0`, a float, with `t` from EXP's core on `-y_0`: `DWPlusFP(y_c, y_0)`; `S_x`, `S_p` and
`S_c` round the scalings of steps (3), (4) and (5) -/
noncomputable def ddLogOp (O : DWOps) (Sx Sp Sc : ℝ × ℝ → ℝ × ℝ) (y0 : ℝ) (x : ℝ × ℝ) (k : ℤ) (t : ℝ × ℝ)
    (B eφ et ec : ℤ) (F' : ℕ → ℝ × ℝ) (q : ℕ) : ℝ × ℝ :=
  O.addF (ddLogYc O Sc B ec (ddLogC O Sp B eφ et (ddLogPhi O Sx k x) t) F' q) y0

/-- step (4)'s `E_c` read with `n = 2`, with `D` the paper's `2nη_0` between `x'` and `2^k x` and `D_p` its `2nη_0`
for the scalings back of `p`: `ε_{φt} = e_P φ̄(t̄ + E_m) + D_p + 2^{-B-12}max(φ̄, t̄ + E_m)`,
`ε_{φ+t} = e_A(2(e^{b̂} - 1 - b̂) + e^{b̂}(e^{E+δ} - 1) + E_m + D)`, `E_δ = e^E(e^δ - 1) + D(1 + t̄ + E_m)`,
`ε_c = e_A(c̄* + ξE_m + E_δ + ε_{φt} + ε_{φ+t})` and `E_c = ξE_m + E_δ + ε_{φt} + ε_{φ+t} + ε_c` -/
noncomputable def ddLogEc (D Dp φb tb Em E δ b ξ : ℝ) (B : ℤ) : ℝ :=
  let εφt := eP p * (φb * (tb + Em)) + Dp + (2 : ℝ) ^ (-B - 12) * max φb (tb + Em)
  let εs := eA p * (2 * (Real.exp (b + δ) - 1 - (b + δ)) + Real.exp (b + δ) * (Real.exp (E + δ) - 1) + Em + D)
  let Eδ := Real.exp E * (Real.exp δ - 1) + D * (1 + tb + Em)
  let εc := eA p * ((Real.exp E - 1) + ξ * Em + Eδ + εφt + εs)
  ξ * Em + Eδ + εφt + εs + εc

/-- step (5)'s `h̄ = C(v_2 + e_2) + ε^h`, with `ε^h = e_P C(v_2 + e_2) + D_c` and `D_c` the paper's `nη_0` -/
noncomputable def ddLogHb (Dc C : ℝ) (φ' : ℕ → ℝ) (q : ℕ) : ℝ :=
  C * (logV C q 2 + ddHornerB p C Dc φ' (logV C q) q (q - 2)) +
    (eP p * (C * (logV C q 2 + ddHornerB p C Dc φ' (logV C q) q (q - 2))) + Dc)

/-- step (5)'s `P` read with `n = 2`: `ε^g = e_F(1 + h̄)`, `ε^r = e_P C(1 + h̄ + ε^g) + D_c` and
`P = ε^r + C(ε^g + ε^h + Ce_2) + max(C^{q+1}/(q + 1), 2^{-B-13}C)/(1 - C) + E_c/(1 - C)` -/
noncomputable def ddLogP (Dc C Ec : ℝ) (φ' : ℕ → ℝ) (q : ℕ) (B : ℤ) : ℝ :=
  let e2 := ddHornerB p C Dc φ' (logV C q) q (q - 2)
  let Zh := C * (logV C q 2 + e2)
  let εh := eP p * Zh + Dc
  let hb := Zh + εh
  let εg := eF p * (1 + hb)
  let εr := eP p * (C * (1 + hb + εg)) + Dc
  εr + C * (εg + εh + C * e2) + max (C ^ (q + 1) / (q + 1)) ((2 : ℝ) ^ (-B - 13) * C) / (1 - C) + Ec / (1 - C)

/-- `𝓔(ℓ) = e_F(ℓ + P) + P` read with `n = 2`, the scalings of steps (3), (4) and (5) within `η_x`, `η_p` and
`η_c` a part and step (3) of EXP's within `η` -/
noncomputable def ddLogBound (η ηx ηp ηc ℓ E : ℝ) (pos : Bool) (a b δ : ℝ) (φF : ℕ → ℝ) (d' : ℕ) (φ' : ℕ → ℝ)
    (q : ℕ) (B : ℤ) : ℝ :=
  let Em := ddCoreE p (coreT pos b 0) η b φF d'
  let Ec := ddLogEc p (2 * ηx) (2 * ηp) (logPhiB (2 * ηx) pos E a b δ) (coreT pos b 0) Em E δ b
    (logXi (2 * ηx) pos E a b δ) B
  let P := ddLogP p (2 * ηc) (Real.exp E - 1 + Ec) Ec φ' q B
  eF p * (ℓ + P) + P

/-- `𝓔(ℓ)` with `t̄`, `φ̄` and `ξ` given: `ddLogBound` is the case `t̄ = e^b - 1` or `1 - e^{-b}`,
`φ̄ = max(ξ - 1, 1 - e^{-(E+b+δ)} + 2nη_0)` and `ξ` of the theorem; the paragraph "Convexity" of Theorem 42's proof
takes the larger `t̄ = b` for `r ≤ 0` and `φ̄ = max(ξ - 1, E + b + δ + 2nη_0)` -/
noncomputable def ddLogBoundG (η ηx ηp ηc ℓ E tb φb ξ b δ : ℝ) (φF : ℕ → ℝ) (d' : ℕ) (φ' : ℕ → ℝ) (q : ℕ)
    (B : ℤ) : ℝ :=
  let Em := ddCoreE p tb η b φF d'
  let Ec := ddLogEc p (2 * ηx) (2 * ηp) φb tb Em E δ b ξ B
  let P := ddLogP p (2 * ηc) (Real.exp E - 1 + Ec) Ec φ' q B
  eF p * (ℓ + P) + P

variable [Prec_gt_0 p]

omit [Prec_gt_0 p] in
/-- `e_P ≤ 1` where `4u < 1` -/
theorem eP_le_one (hu : 4 * u p < 1) : eP p ≤ 1 := by
  have h0 := u_pos p
  unfold eP
  rw [div_le_one (by positivity)]
  nlinarith

omit [Prec_gt_0 p] in
/-- `e_F ≤ 1` where `4u < 1` -/
theorem eF_le_one (hu : 4 * u p < 1) : eF p ≤ 1 := by
  have h0 := u_pos p
  unfold eF
  nlinarith

/-- a product formed on factors scaled by powers of two and scaled back, the scaling back rounded by `S`: for double
words `a` and `b` with `lo(1 + u) ≤ (1 - e_P)|ab|`, it is a double word within `e_P|ab| + 2η` of `ab` -/
theorem dd_mul_scaled {O : DWOps} (hO : DWSpec p O) (hu : 4 * u p < 1) {η lo : ℝ} {S : ℝ × ℝ → ℝ × ℝ}
    (hS : SclDW p η lo S) {a b : ℝ × ℝ} (ha : DW p a) (hb : DW p b) (i j : ℤ)
    (hfl : lo * (1 + u p) ≤ (1 - eP p) * |dwVal a * dwVal b|) :
    DW p (S (dwScale (i + j) (O.mul (dwScale (-i) a) (dwScale (-j) b)))) ∧
      |dwVal (S (dwScale (i + j) (O.mul (dwScale (-i) a) (dwScale (-j) b)))) - dwVal a * dwVal b| ≤
        eP p * |dwVal a * dwVal b| + 2 * η := by
  have hu0 := u_pos p
  obtain ⟨ah, hah⟩ : ∃ ah, ah = dwScale (-i) a := ⟨_, rfl⟩
  obtain ⟨bh, hbh⟩ : ∃ bh, bh = dwScale (-j) b := ⟨_, rfl⟩
  have hahdw : DW p ah := hah ▸ DW.dwScale p ha (-i)
  have hbhdw : DW p bh := hbh ▸ DW.dwScale p hb (-j)
  obtain ⟨A, hA⟩ : ∃ A, A = dwVal a := ⟨_, rfl⟩
  obtain ⟨Bv, hBv⟩ : ∃ Bv, Bv = dwVal b := ⟨_, rfl⟩
  rw [← hA, ← hBv] at hfl ⊢
  have hahv : dwVal ah = (2 : ℝ) ^ (-i) * A := by rw [hah, dwVal_dwScale, hA]
  have hbhv : dwVal bh = (2 : ℝ) ^ (-j) * Bv := by rw [hbh, dwVal_dwScale, hBv]
  rw [← hah, ← hbh]
  obtain ⟨m, hm⟩ : ∃ m, m = O.mul ah bh := ⟨_, rfl⟩
  have hmdw : DW p m := hm ▸ hO.mul_dw ah bh hahdw hbhdw
  rw [← hm]
  obtain ⟨V, hV⟩ : ∃ V, V = dwScale (i + j) m := ⟨_, rfl⟩
  have hVdw : DW p V := hV ▸ DW.dwScale p hmdw (i + j)
  rw [← hV]
  have hsc : (2 : ℝ) ^ (i + j) * ((2 : ℝ) ^ (-i) * (2 : ℝ) ^ (-j)) = 1 := by
    rw [← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero, show i + j + (-i + -j) = 0 by ring, zpow_zero]
  have hVv : |dwVal V - A * Bv| ≤ eP p * |A * Bv| := by
    have h := abs_scale_le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (i + j)) (hO.mul_err ah bh hahdw hbhdw)
    rw [← hm, hahv, hbhv] at h
    rw [hV, dwVal_dwScale]
    rwa [show (2 : ℝ) ^ (i + j) * (dwVal m - (2 : ℝ) ^ (-i) * A * ((2 : ℝ) ^ (-j) * Bv)) =
          (2 : ℝ) ^ (i + j) * dwVal m - A * Bv by linear_combination (-(A * Bv)) * hsc,
      show (2 : ℝ) ^ (i + j) * ((2 : ℝ) ^ (-i) * A * ((2 : ℝ) ^ (-j) * Bv)) = A * Bv by
        linear_combination (A * Bv) * hsc] at h
  have hSv := hS.val p V
  constructor
  · -- `|V_h|(1 + u) ≥ |V| ≥ (1 - e_P)|ab| ≥ lo(1 + u)`
    refine hS.dw V hVdw ?_
    have h1 := abs_sub_abs_le_abs_sub (A * Bv) (dwVal V)
    rw [abs_sub_comm (A * Bv) (dwVal V)] at h1
    have h3 : |dwVal V| ≤ (1 + u p) * |V.1| := by
      have h4 := (DW.parts p hVdw).1
      calc |dwVal V| ≤ |V.1| + |V.2| := abs_add_le _ _
        _ ≤ (1 + u p) * |V.1| := by linarith
    have h5 : (1 - eP p) * |A * Bv| = |A * Bv| - eP p * |A * Bv| := by ring
    rw [h5] at hfl
    refine le_of_mul_le_mul_right ?_ (by linarith : (0 : ℝ) < 1 + u p)
    calc lo * (1 + u p) ≤ |A * Bv| - eP p * |A * Bv| := hfl
      _ ≤ |dwVal V| := by linarith
      _ ≤ (1 + u p) * |V.1| := h3
      _ = |V.1| * (1 + u p) := by ring
  · calc |dwVal (S V) - A * Bv| = |(dwVal V - A * Bv) + (dwVal (S V) - dwVal V)| := by ring_nf
      _ ≤ |dwVal V - A * Bv| + |dwVal (S V) - dwVal V| := abs_add_le _ _
      _ ≤ eP p * |A * Bv| + 2 * η := add_le_add hVv hSv

/-- step (4) read with `n = 2`: for double words `φ` and `t` with `|φ| ≤ φ̄`, `|t| ≤ t̄`, `|φ + t| ≤ Z̄_s` and
`φ + t + φt` within `E_x` of `c*`, `|c*| ≤ c̄*`, the computed `c` is a double word within
`E_x + ε_{φt} + ε_{φ+t} + ε_c` of `c*`, with or without the product; where the product is formed, its floor is
`lo(1 + u) ≤ (1 - e_P)|φt|` -/
theorem dd_log_step4 {O : DWOps} (hO : DWSpec p O) (hu : 4 * u p < 1) {η lo : ℝ} {S : ℝ × ℝ → ℝ × ℝ}
    (hS : SclDW p η lo S) (φ t : ℝ × ℝ) (hφ : DW p φ) (ht : DW p t) {φb tb Zs Ex cs cb : ℝ}
    (hφb : |dwVal φ| ≤ φb) (htb : |dwVal t| ≤ tb) (hZs : |dwVal φ + dwVal t| ≤ Zs)
    (hEx : |dwVal φ + dwVal t + dwVal φ * dwVal t - cs| ≤ Ex) (hcs : |cs| ≤ cb) (B eφ et : ℤ)
    (hUφ : |φ.1| + |φ.2| < (2 : ℝ) ^ (eφ + 1)) (hUt : |t.1| + |t.2| < (2 : ℝ) ^ (et + 1))
    (hfl : ¬ min eφ et < -B - 13 → lo * (1 + u p) ≤ (1 - eP p) * |dwVal φ * dwVal t|) :
    DW p (ddLogC O S B eφ et φ t) ∧
      |dwVal (ddLogC O S B eφ et φ t) - cs| ≤
        Ex + (eP p * (φb * tb) + 2 * η + (2 : ℝ) ^ (-B - 12) * max φb tb) + eA p * Zs +
          eA p * (cb + Ex + (eP p * (φb * tb) + 2 * η + (2 : ℝ) ^ (-B - 12) * max φb tb) + eA p * Zs) := by
  have heA := eA_nonneg p hu
  have heP := eP_nonneg p
  have hη := hS.nonneg p
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = dwVal φ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = dwVal t := ⟨_, rfl⟩
  rw [← hΦ] at hφb
  rw [← hT] at htb
  rw [← hΦ, ← hT] at hZs hEx hfl
  have hφb0 : 0 ≤ φb := (abs_nonneg _).trans hφb
  have htb0 : 0 ≤ tb := (abs_nonneg _).trans htb
  have hZs0 : 0 ≤ Zs := (abs_nonneg _).trans hZs
  have hEx0 : 0 ≤ Ex := (abs_nonneg _).trans hEx
  have hcb0 : 0 ≤ cb := (abs_nonneg _).trans hcs
  have hM0 : 0 ≤ (2 : ℝ) ^ (-B - 12) * max φb tb := mul_nonneg (by positivity) (le_max_of_le_left hφb0)
  have hΦT : |Φ * T| ≤ φb * tb := by
    rw [abs_mul]
    exact mul_le_mul hφb htb (abs_nonneg _) hφb0
  have hPT0 : 0 ≤ eP p * (φb * tb) := mul_nonneg heP (mul_nonneg hφb0 htb0)
  obtain ⟨εφt, hεφt⟩ : ∃ εφt, εφt = eP p * (φb * tb) + 2 * η + (2 : ℝ) ^ (-B - 12) * max φb tb := ⟨_, rfl⟩
  rw [← hεφt]
  have hεs0 : 0 ≤ eA p * Zs := mul_nonneg heA hZs0
  have hs : |dwVal (O.add φ t) - (Φ + T)| ≤ eA p * Zs := by
    have h := hO.add_err φ t hφ ht
    rw [← hΦ, ← hT] at h
    exact h.trans (mul_le_mul_of_nonneg_left hZs heA)
  unfold ddLogC
  split_ifs with hd
  · -- `c = ADD(φ, t)`: the smaller of `|φ|` and `|t|` is below `2^{-B-12}`
    refine ⟨hO.add_dw φ t hφ ht, ?_⟩
    have hsmall : |Φ * T| ≤ (2 : ℝ) ^ (-B - 12) * max φb tb := by
      rw [abs_mul]
      rcases le_total eφ et with h | h
      · rw [min_eq_left h] at hd
        have h1 : |Φ| ≤ (2 : ℝ) ^ (-B - 12) := by
          rw [hΦ]
          exact ((abs_add_le _ _).trans hUφ.le).trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
        exact (mul_le_mul h1 htb (abs_nonneg _) (by positivity)).trans
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
      · rw [min_eq_right h] at hd
        have h1 : |T| ≤ (2 : ℝ) ^ (-B - 12) := by
          rw [hT]
          exact ((abs_add_le _ _).trans hUt.le).trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
        rw [mul_comm |Φ|]
        exact (mul_le_mul h1 hφb (abs_nonneg _) (by positivity)).trans
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
    have hεc0 : 0 ≤ eA p * (cb + Ex + εφt + eA p * Zs) := by
      rw [hεφt]
      exact mul_nonneg heA (by linarith)
    calc |dwVal (O.add φ t) - cs| =
          |(dwVal (O.add φ t) - (Φ + T)) + (Φ + T + Φ * T - cs) + -(Φ * T)| := by ring_nf
      _ ≤ |dwVal (O.add φ t) - (Φ + T)| + |Φ + T + Φ * T - cs| + |-(Φ * T)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ eA p * Zs + Ex + (2 : ℝ) ^ (-B - 12) * max φb tb := by
          rw [abs_neg]
          exact add_le_add (add_le_add hs hEx) hsmall
      _ ≤ _ := by linarith
  · -- `c = ADD(ADD(φ, t), p)`
    obtain ⟨p1, p2⟩ := dd_mul_scaled p hO hu hS hφ ht eφ et (by rw [← hΦ, ← hT]; exact hfl hd)
    obtain ⟨pp, hpp⟩ : ∃ pp, pp = S (dwScale (eφ + et) (O.mul (dwScale (-eφ) φ) (dwScale (-et) t))) := ⟨_, rfl⟩
    rw [← hpp] at p1 p2 ⊢
    rw [← hΦ, ← hT] at p2
    have hp3 : |dwVal pp - Φ * T| ≤ εφt := by
      rw [hεφt]
      linarith [mul_le_mul_of_nonneg_left hΦT heP]
    obtain ⟨s, hsd⟩ : ∃ s, s = O.add φ t := ⟨_, rfl⟩
    have hsdw : DW p s := hsd ▸ hO.add_dw φ t hφ ht
    rw [← hsd] at hs ⊢
    have hsum : |dwVal s + dwVal pp - cs| ≤ Ex + εφt + eA p * Zs := by
      calc |dwVal s + dwVal pp - cs| =
            |(dwVal s - (Φ + T)) + (dwVal pp - Φ * T) + (Φ + T + Φ * T - cs)| := by ring_nf
        _ ≤ |dwVal s - (Φ + T)| + |dwVal pp - Φ * T| + |Φ + T + Φ * T - cs| :=
            (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ eA p * Zs + εφt + Ex := add_le_add (add_le_add hs hp3) hEx
        _ = Ex + εφt + eA p * Zs := by ring
    have hsumb : |dwVal s + dwVal pp| ≤ cb + Ex + εφt + eA p * Zs := by
      calc |dwVal s + dwVal pp| = |cs + (dwVal s + dwVal pp - cs)| := by ring_nf
        _ ≤ |cs| + |dwVal s + dwVal pp - cs| := abs_add_le _ _
        _ ≤ cb + (Ex + εφt + eA p * Zs) := add_le_add hcs hsum
        _ = cb + Ex + εφt + eA p * Zs := by ring
    have hc := (hO.add_err s pp hsdw p1).trans (mul_le_mul_of_nonneg_left hsumb heA)
    refine ⟨hO.add_dw s pp hsdw p1, ?_⟩
    calc |dwVal (O.add s pp) - cs| = |(dwVal s + dwVal pp - cs) + (dwVal (O.add s pp) - (dwVal s + dwVal pp))| := by
          ring_nf
      _ ≤ |dwVal s + dwVal pp - cs| + |dwVal (O.add s pp) - (dwVal s + dwVal pp)| := abs_add_le _ _
      _ ≤ Ex + εφt + eA p * Zs + eA p * (cb + Ex + εφt + eA p * Zs) := add_le_add hsum hc

omit [Prec_gt_0 p] in
/-- Horner's `e_k` on double words is nonnegative -/
theorem ddHornerB_nonneg (hu : 4 * u p < 1) {zb D : ℝ} (hzb : 0 ≤ zb) (hD : 0 ≤ D) {φ v : ℕ → ℝ}
    (hφ : ∀ k, 0 ≤ φ k) (hv : ∀ k, 0 ≤ v k) (d : ℕ) : ∀ j, 0 ≤ ddHornerB p zb D φ v d j
  | 0 => hφ d
  | j + 1 => by
    have ih := ddHornerB_nonneg hu hzb hD hφ hv d j
    have heA := eA_nonneg p hu
    have heP := eP_nonneg p
    simp only [ddHornerB]
    have h1 : 0 ≤ zb * ddHornerB p zb D φ v d j + φ (d - (j + 1)) +
        (eP p * (zb * (v (d - (j + 1) + 1) + ddHornerB p zb D φ v d j)) + D) :=
      add_nonneg (add_nonneg (mul_nonneg hzb ih) (hφ _))
        (add_nonneg (mul_nonneg heP (mul_nonneg hzb (add_nonneg (hv _) ih))) hD)
    exact add_nonneg h1 (mul_nonneg heA (add_nonneg (hv _) h1))

omit [Prec_gt_0 p] in
/-- `|p^e_k| ≥ 1/k - C v_{k+1}` for the coefficients of `log(1 + c)` and `|c| ≤ C` -/
theorem logH_ge {z C : ℝ} (hz : |z| ≤ C) (q k : ℕ) (hkq : k ≤ q) :
    1 / (k : ℝ) - C * logV C q (k + 1) ≤ |hornerE logFe z q k| := by
  have h1 : |logFe k| = 1 / (k : ℝ) := by
    unfold logFe
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_nonneg (Nat.cast_nonneg k)]
  rcases lt_or_eq_of_le hkq with h | h
  · rw [hornerE_succ logFe z q k h]
    have h2 : |z * hornerE logFe z q (k + 1)| ≤ C * logV C q (k + 1) := by
      rw [abs_mul]
      exact mul_le_mul hz (logV_bound hz q (k + 1)) (abs_nonneg _) ((abs_nonneg _).trans hz)
    have h3 := abs_sub_abs_le_abs_sub (logFe k) (-(z * hornerE logFe z q (k + 1)))
    rw [abs_neg, sub_neg_eq_add] at h3
    linarith
  · subst h
    have h0 : hornerE logFe z k k = logFe k := by simp [hornerE]
    have hV : logV C k (k + 1) = 0 := by simp [logV]
    rw [h0, hV, mul_zero, sub_zero, h1]

omit [Prec_gt_0 p] in
/-- a scaling by `2^0` is the identity -/
theorem dwScale_zero (x : ℝ × ℝ) : dwScale 0 x = x := by simp [dwScale]

/-- `c ⊗ b` with its floor from lower bounds of the factors: for double words `c` and `b` with `0 ≤ l_c ≤ |c|`,
`l_b ≤ |b|` and `lo(1 + u) ≤ (1 - e_P) l_c l_b`, it is a double word within `e_P|cb| + 2η` of `cb` -/
theorem dd_smul_spec {O : DWOps} (hO : DWSpec p O) (hu : 4 * u p < 1) {η lo : ℝ} {S : ℝ × ℝ → ℝ × ℝ}
    (hS : SclDW p η lo S) {c b : ℝ × ℝ} (hc : DW p c) (hb : DW p b) (e : ℤ) {lc lb : ℝ} (hlc0 : 0 ≤ lc)
    (hlc : lc ≤ |dwVal c|) (hlb : lb ≤ |dwVal b|) (hfl : lo * (1 + u p) ≤ (1 - eP p) * (lc * lb)) :
    DW p (ddSmul O S e c b) ∧
      |dwVal (ddSmul O S e c b) - dwVal c * dwVal b| ≤ eP p * |dwVal c * dwVal b| + 2 * η := by
  have h1eP : 0 ≤ 1 - eP p := by linarith [eP_le_one p hu]
  have h2 : lc * lb ≤ |dwVal c| * |dwVal b| := by
    rcases le_total 0 lb with h0 | h0
    · exact mul_le_mul hlc hlb h0 (abs_nonneg _)
    · exact (mul_nonpos_of_nonneg_of_nonpos hlc0 h0).trans (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have h := dd_mul_scaled p hO hu hS hc hb e 0 (by
    rw [abs_mul]
    exact hfl.trans (mul_le_mul_of_nonneg_left h2 h1eP))
  rw [neg_zero, dwScale_zero, add_zero] at h
  exact h

/-- step (5)'s Horner's rule read with `n = 2`: with `|c| ≤ C`, `0 ≤ l_c ≤ |c|` and each `p^e_k`, `2 ≤ k ≤ q`, at
least `l_v + e_k` in magnitude, where `lo(1 + u) ≤ (1 - e_P) l_c l_v`, `h = p_2` is a double word within `e_2` of
`H(c)` and at least `l_v` in magnitude -/
theorem dd_log_horner {O : DWOps} (hO : DWSpec p O) (hu : 4 * u p < 1) {η lo : ℝ} {S : ℝ × ℝ → ℝ × ℝ}
    (hS : SclDW p η lo S) (c : ℝ × ℝ) (hc : DW p c) {C : ℝ} (hSC : |dwVal c| ≤ C) (F' : ℕ → ℝ × ℝ)
    (hF' : ∀ k, DW p (F' k)) (φ' : ℕ → ℝ) (hφ' : ∀ k, |dwVal (F' k) - logFe k| ≤ φ' k) (q : ℕ) (hq : 2 ≤ q)
    (ec : ℤ) {lc lv : ℝ} (hlc0 : 0 ≤ lc) (hlc : lc ≤ |dwVal c|)
    (hlv : ∀ k, 2 ≤ k → k ≤ q → lv ≤ 1 / (k : ℝ) - C * logV C q (k + 1) -
      ddHornerB p C (2 * η) φ' (logV C q) q (q - k))
    (hfl : lo * (1 + u p) ≤ (1 - eP p) * (lc * lv)) :
    DW p (ddHornerP O (ddSmul O S ec c) F' q (q - 2)) ∧
      |dwVal (ddHornerP O (ddSmul O S ec c) F' q (q - 2)) - hornerE logFe (dwVal c) q 2| ≤
        ddHornerB p C (2 * η) φ' (logV C q) q (q - 2) ∧
      lv ≤ |dwVal (ddHornerP O (ddSmul O S ec c) F' q (q - 2))| := by
  have hM : ∀ b, DW p b → lv ≤ |dwVal b| → DW p (ddSmul O S ec c b) ∧
      |dwVal (ddSmul O S ec c b) - dwVal c * dwVal b| ≤ eP p * |dwVal c * dwVal b| + 2 * η := fun b hb hA =>
    dd_smul_spec p hO hu hS hc hb ec hlc0 hlc hA hfl
  have hrun : ∀ j, j ≤ q - 2 →
      (|dwVal (ddHornerP O (ddSmul O S ec c) F' q j) - hornerE logFe (dwVal c) q (q - j)| ≤
          ddHornerB p C (2 * η) φ' (logV C q) q j ∧ DW p (ddHornerP O (ddSmul O S ec c) F' q j)) ∧
        lv ≤ |dwVal (ddHornerP O (ddSmul O S ec c) F' q j)| := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have hA : ∀ i < j, lv ≤ |dwVal (ddHornerP O (ddSmul O S ec c) F' q i)| := fun i hi =>
        (ih i hi (by omega)).2
      have hs := dd_horner_step p hO hu (A := fun b => lv ≤ |dwVal b|) hSC hM F' hF' logFe φ' (logV C q) hφ' q 2
        (fun k _ _ => logV_bound hSC q k) j hj hA
      refine ⟨hs, ?_⟩
      have h1 := hlv (q - j) (by omega) (by omega)
      rw [show q - (q - j) = j by omega] at h1
      have h2 := logH_ge hSC q (q - j) (by omega)
      have h3 := abs_sub_abs_le_abs_sub (hornerE logFe (dwVal c) q (q - j))
        (dwVal (ddHornerP O (ddSmul O S ec c) F' q j))
      rw [abs_sub_comm (hornerE logFe (dwVal c) q (q - j))] at h3
      have h4 := hs.1
      linarith only [h1, h2, h3, h4]
  obtain ⟨⟨r1, r2⟩, r3⟩ := hrun (q - 2) le_rfl
  rw [show q - (q - 2) = 2 by omega] at r1
  exact ⟨r2, r1, r3⟩

/-- step (5)'s last products and sum read with `n = 2`: from `h` within `e_2` of `H`, `|H| ≤ v_2`, the double
word `y_c = c ⊗ DWPlusFP(c ⊗ h, 1)` is within `ε^r + C(ε^g + ε^h + Ce_2)` of `c + c²H`; the floors are those of
`c ⊗ h`, through `l_v ≤ |h|`, and of the last product, through `(1 - e_F)(1 - h̄)` -/
theorem dd_log_series {O : DWOps} (hO : DWSpec p O) (hu : 4 * u p < 1) {η lo : ℝ} {S : ℝ × ℝ → ℝ × ℝ}
    (hS : SclDW p η lo S) (c hh : ℝ × ℝ) (hc : DW p c) (hhdw : DW p hh) {C H v2 e2 : ℝ} (hSC : |dwVal c| ≤ C)
    (hH : |H| ≤ v2) (hhH : |dwVal hh - H| ≤ e2) (ec : ℤ) {lc lv : ℝ} (hlc0 : 0 ≤ lc) (hlc : lc ≤ |dwVal c|)
    (hlvh : lv ≤ |dwVal hh|) (hfl : lo * (1 + u p) ≤ (1 - eP p) * (lc * lv)) {Zh εh hb εg εr : ℝ}
    (hZh : Zh = C * (v2 + e2)) (hεh : εh = eP p * Zh + 2 * η) (hhb : hb = Zh + εh) (hεg : εg = eF p * (1 + hb))
    (hεr : εr = eP p * (C * (1 + hb + εg)) + 2 * η)
    (hflg : lo * (1 + u p) ≤ (1 - eP p) * (lc * ((1 - eF p) * (1 - hb)))) :
    DW p (ddSmul O S ec c (O.addF (ddSmul O S ec c hh) 1)) ∧
      |dwVal (ddSmul O S ec c (O.addF (ddSmul O S ec c hh) 1)) - (dwVal c + dwVal c ^ 2 * H)| ≤
        εr + C * (εg + εh + C * e2) := by
  have heP := eP_nonneg p
  have heF := eF_nonneg p
  have heF1 := eF_le_one p hu
  have hη := hS.nonneg p
  obtain ⟨Sv, hSv⟩ : ∃ Sv, Sv = dwVal c := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hSC
  have hhb1 : |dwVal hh| ≤ v2 + e2 := by
    have := abs_sub_abs_le_abs_sub (dwVal hh) H
    linarith only [this, hH, hhH]
  -- `ĥ = c ⊗ h`
  obtain ⟨k1, k2⟩ := dd_smul_spec p hO hu hS hc hhdw ec hlc0 hlc hlvh hfl
  obtain ⟨hc', hc'd⟩ : ∃ hc', hc' = ddSmul O S ec c hh := ⟨_, rfl⟩
  rw [← hc'd] at k1 k2 ⊢
  rw [← hSv] at hSC k2 ⊢
  have hSh : |Sv * dwVal hh| ≤ Zh := by
    rw [abs_mul, hZh]
    exact mul_le_mul hSC hhb1 (abs_nonneg _) hC0
  have k3 : |dwVal hc' - Sv * dwVal hh| ≤ εh := by
    have := mul_le_mul_of_nonneg_left hSh heP
    linarith only [k2, this, hεh]
  have k4 : |dwVal hc'| ≤ hb := by
    have := abs_sub_abs_le_abs_sub (dwVal hc') (Sv * dwVal hh)
    linarith only [this, k3, hSh, hhb]
  -- `g = DWPlusFP(ĥ, 1)`
  obtain ⟨g, hg⟩ : ∃ g, g = O.addF hc' 1 := ⟨_, rfl⟩
  have hgdw : DW p g := hg ▸ hO.addF_dw hc' 1 k1 (F_one p)
  rw [← hg]
  have g0 := hO.addF_err hc' 1 k1 (F_one p)
  rw [← hg] at g0
  have g1 : |dwVal hc' + 1| ≤ 1 + hb := by
    have := abs_add_le (dwVal hc') 1
    rw [abs_one] at this
    linarith only [this, k4]
  have g2 : |dwVal g - (dwVal hc' + 1)| ≤ εg := by
    rw [hεg]
    exact g0.trans (mul_le_mul_of_nonneg_left g1 heF)
  have g3 : |dwVal g| ≤ 1 + hb + εg := by
    have := abs_sub_abs_le_abs_sub (dwVal g) (dwVal hc' + 1)
    linarith only [this, g1, g2]
  have g4 : (1 - eF p) * (1 - hb) ≤ |dwVal g| := by
    have h1 : 1 - hb ≤ |dwVal hc' + 1| := by
      have := abs_sub_abs_le_abs_sub (1 : ℝ) (-dwVal hc')
      rw [abs_one, abs_neg, sub_neg_eq_add, add_comm 1 (dwVal hc')] at this
      linarith only [this, k4]
    have h2 := abs_sub_abs_le_abs_sub (dwVal hc' + 1) (dwVal g)
    rw [abs_sub_comm (dwVal hc' + 1)] at h2
    have h3 : (1 - eF p) * (1 - hb) ≤ (1 - eF p) * |dwVal hc' + 1| :=
      mul_le_mul_of_nonneg_left h1 (by linarith only [heF1])
    have h4 : (1 - eF p) * |dwVal hc' + 1| = |dwVal hc' + 1| - eF p * |dwVal hc' + 1| := by ring
    linarith only [h2, h3, h4, g0]
  -- `y_c = c ⊗ g`
  obtain ⟨y1, y2⟩ := dd_smul_spec p hO hu hS hc hgdw ec hlc0 hlc g4 hflg
  refine ⟨y1, ?_⟩
  obtain ⟨y, hy⟩ : ∃ y, y = ddSmul O S ec c g := ⟨_, rfl⟩
  rw [← hy] at y2 ⊢
  rw [← hSv] at y2
  have hSg : |Sv * dwVal g| ≤ C * (1 + hb + εg) := by
    rw [abs_mul]
    exact mul_le_mul hSC g3 (abs_nonneg _) hC0
  have y3 : |dwVal y - Sv * dwVal g| ≤ εr := by
    have := mul_le_mul_of_nonneg_left hSg heP
    linarith only [y2, this, hεr]
  -- `y_c - S_q(c) = (y_c - cg) + c(g - 1 - ĥ) + c(ĥ - ch) + c²(h - H(c))`
  have e1 : dwVal y - (Sv + Sv ^ 2 * H) = (dwVal y - Sv * dwVal g) + Sv * (dwVal g - (dwVal hc' + 1)) +
      Sv * (dwVal hc' - Sv * dwVal hh) + Sv * (Sv * (dwVal hh - H)) := by ring
  have b1 : |Sv * (dwVal g - (dwVal hc' + 1))| ≤ C * εg := by
    rw [abs_mul]
    exact mul_le_mul hSC g2 (abs_nonneg _) hC0
  have b2 : |Sv * (dwVal hc' - Sv * dwVal hh)| ≤ C * εh := by
    rw [abs_mul]
    exact mul_le_mul hSC k3 (abs_nonneg _) hC0
  have b3 : |Sv * (Sv * (dwVal hh - H))| ≤ C * (C * e2) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul hSC (mul_le_mul hSC hhH (abs_nonneg _) hC0) (by positivity) hC0
  rw [e1]
  calc _ ≤ |dwVal y - Sv * dwVal g| + |Sv * (dwVal g - (dwVal hc' + 1))| +
        |Sv * (dwVal hc' - Sv * dwVal hh)| + |Sv * (Sv * (dwVal hh - H))| :=
        (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ εr + C * εg + C * εh + C * (C * e2) := add_le_add (add_le_add (add_le_add y3 b1) b2) b3
    _ = εr + C * (εg + εh + C * e2) := by ring

/-- step (5) read with `n = 2`: for a double word `c` within `E_c` of `c*`, `|c*| ≤ c̄*` and `C = c̄* + E_c < 1`,
`y_c` is a double word within `P` of `log(1 + c*)`. Where the series is formed, the floors of its scaled products
are asked through `l_c ≤ |c|`, a lower bound `l_v` of Horner's iterates, `1/k - C v_{k+1} - e_k` for `2 ≤ k ≤ q`, and
the lower bound `(1 - e_F)(1 - h̄)` of `DWPlusFP(c ⊗ h, 1)` -/
theorem dd_log_step5 {O : DWOps} (hO : DWSpec p O) (hu : 4 * u p < 1) {η lo : ℝ} {S : ℝ × ℝ → ℝ × ℝ}
    (hS : SclDW p η lo S) (c : ℝ × ℝ) (hc : DW p c) {cs cb Ec : ℝ} (hcs : |cs| ≤ cb) (hEc : |dwVal c - cs| ≤ Ec)
    (hC : cb + Ec < 1) (F' : ℕ → ℝ × ℝ) (hF' : ∀ k, DW p (F' k)) (φ' : ℕ → ℝ)
    (hφ' : ∀ k, |dwVal (F' k) - logFe k| ≤ φ' k) (q : ℕ) (hq : 2 ≤ q) (B ec : ℤ)
    (hU : |c.1| + |c.2| < (2 : ℝ) ^ (ec + 1)) {lc lv : ℝ} (hlc0 : 0 ≤ lc)
    (hfloor : ¬ ec < -B - 13 → lc ≤ |dwVal c| ∧
      (∀ k, 2 ≤ k → k ≤ q → lv ≤ 1 / (k : ℝ) - (cb + Ec) * logV (cb + Ec) q (k + 1) -
        ddHornerB p (cb + Ec) (2 * η) φ' (logV (cb + Ec) q) q (q - k)) ∧
      lo * (1 + u p) ≤ (1 - eP p) * (lc * lv) ∧
      lo * (1 + u p) ≤ (1 - eP p) * (lc * ((1 - eF p) * (1 - ddLogHb p (2 * η) (cb + Ec) φ' q)))) :
    DW p (ddLogYc O S B ec c F' q) ∧
      |dwVal (ddLogYc O S B ec c F' q) - Real.log (1 + cs)| ≤ ddLogP p (2 * η) (cb + Ec) Ec φ' q B := by
  have heP := eP_nonneg p
  have heF := eF_nonneg p
  have hη := hS.nonneg p
  obtain ⟨C, hCd⟩ : ∃ C, C = cb + Ec := ⟨_, rfl⟩
  rw [← hCd] at hC hfloor ⊢
  obtain ⟨Sv, hSv⟩ : ∃ Sv, Sv = dwVal c := ⟨_, rfl⟩
  have hEc' : |Sv - cs| ≤ Ec := hSv ▸ hEc
  have hEc0 : 0 ≤ Ec := (abs_nonneg _).trans hEc
  have hcb0 : 0 ≤ cb := (abs_nonneg _).trans hcs
  have hC0 : 0 ≤ C := by linarith only [hCd, hEc0, hcb0]
  have hC1 : 0 < 1 - C := by linarith only [hC]
  have hSC : |Sv| ≤ C := by
    have := abs_sub_abs_le_abs_sub Sv cs
    linarith only [this, hEc', hcs, hCd]
  have hcsC : |cs| ≤ C := by linarith only [hcs, hCd, hEc0]
  have hlip : |Real.log (1 + Sv) - Real.log (1 + cs)| ≤ Ec / (1 - C) :=
    (log_lip hSC hcsC hC).trans (div_le_div_of_nonneg_right hEc' hC1.le)
  have hφ0 : ∀ k, 0 ≤ φ' k := fun k => (abs_nonneg _).trans (hφ' k)
  have hv0 : ∀ k, 0 ≤ logV C q k := logV_nonneg hC0 q
  obtain ⟨e2, he2⟩ : ∃ e2, e2 = ddHornerB p C (2 * η) φ' (logV C q) q (q - 2) := ⟨_, rfl⟩
  have he20 : 0 ≤ e2 := he2 ▸ ddHornerB_nonneg p hu hC0 (by linarith only [hη]) hφ0 hv0 q (q - 2)
  obtain ⟨Zh, hZh⟩ : ∃ Zh, Zh = C * (logV C q 2 + e2) := ⟨_, rfl⟩
  have hZh0 : 0 ≤ Zh := hZh ▸ mul_nonneg hC0 (add_nonneg (hv0 2) he20)
  obtain ⟨εh, hεh⟩ : ∃ εh, εh = eP p * Zh + 2 * η := ⟨_, rfl⟩
  have hεh0 : 0 ≤ εh := by
    have := mul_nonneg heP hZh0
    linarith only [this, hεh, hη]
  obtain ⟨hb, hhb⟩ : ∃ hb, hb = Zh + εh := ⟨_, rfl⟩
  have hhb0 : 0 ≤ hb := by linarith only [hhb, hZh0, hεh0]
  obtain ⟨εg, hεg⟩ : ∃ εg, εg = eF p * (1 + hb) := ⟨_, rfl⟩
  have hεg0 : 0 ≤ εg := hεg ▸ mul_nonneg heF (by linarith only [hhb0])
  obtain ⟨εr, hεr⟩ : ∃ εr, εr = eP p * (C * (1 + hb + εg)) + 2 * η := ⟨_, rfl⟩
  have hεr0 : 0 ≤ εr := by
    have := mul_nonneg heP (mul_nonneg hC0 (by linarith only [hhb0, hεg0] : (0 : ℝ) ≤ 1 + hb + εg))
    linarith only [this, hεr, hη]
  obtain ⟨M, hM⟩ : ∃ M, M = max (C ^ (q + 1) / (q + 1)) ((2 : ℝ) ^ (-B - 13) * C) := ⟨_, rfl⟩
  have hP : ddLogP p (2 * η) C Ec φ' q B = εr + C * (εg + εh + C * e2) + M / (1 - C) + Ec / (1 - C) := by
    rw [hM, hεr, hεg, hhb, hεh, hZh, he2]
    rfl
  have hHb : ddLogHb p (2 * η) C φ' q = hb := by
    rw [hhb, hεh, hZh, he2]
    rfl
  rw [hP]
  have hrest : 0 ≤ εr + C * (εg + εh + C * e2) :=
    add_nonneg hεr0 (mul_nonneg hC0 (add_nonneg (add_nonneg hεg0 hεh0) (mul_nonneg hC0 he20)))
  unfold ddLogYc
  split_ifs with hd
  · -- `y_c = c`, with `|c| < 2^{-B-13}`
    refine ⟨hc, ?_⟩
    rw [← hSv]
    have hSs : |Sv| ≤ (2 : ℝ) ^ (-B - 13) := by
      rw [hSv]
      exact ((abs_add_le _ _).trans hU.le).trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
    have ht := log_tail (lt_of_le_of_lt hSC hC) 1
    simp only [range_one, sum_singleton, Nat.cast_zero, Nat.cast_one, zero_add, pow_one, div_one] at ht
    have hm : (2 : ℝ) ^ (-B - 13) * C ≤ M := hM ▸ le_max_right _ _
    have h2 : |Sv| ^ (1 + 1) / ((1 + 1) * (1 - |Sv|)) ≤ M / (1 - C) := by
      rw [show |Sv| ^ (1 + 1) = |Sv| * |Sv| by ring, div_le_div_iff₀ (by nlinarith [abs_nonneg Sv]) hC1]
      have h3 : |Sv| * |Sv| ≤ (2 : ℝ) ^ (-B - 13) * C := mul_le_mul hSs hSC (abs_nonneg _) (by positivity)
      have h4 : 1 - C ≤ (1 + 1) * (1 - |Sv|) := by linarith only [abs_nonneg Sv, hSC, hC]
      calc |Sv| * |Sv| * (1 - C) ≤ M * (1 - C) := mul_le_mul_of_nonneg_right (h3.trans hm) hC1.le
        _ ≤ M * ((1 + 1) * (1 - |Sv|)) := mul_le_mul_of_nonneg_left h4 ((by positivity : (0 : ℝ) ≤
            (2 : ℝ) ^ (-B - 13) * C).trans hm)
    have h5 : |Sv - Real.log (1 + Sv)| ≤ M / (1 - C) := by
      rw [abs_sub_comm, show Real.log (1 + Sv) - Sv = Real.log (1 + Sv) + -Sv by ring]
      exact ht.trans h2
    calc |Sv - Real.log (1 + cs)| ≤ |Sv - Real.log (1 + Sv)| + |Real.log (1 + Sv) - Real.log (1 + cs)| :=
          abs_sub_le _ _ _
      _ ≤ M / (1 - C) + Ec / (1 - C) := add_le_add h5 hlip
      _ ≤ _ := by linarith only [hrest]
  · -- the series
    obtain ⟨f1, f2, f3, f4⟩ := hfloor hd
    obtain ⟨r2, r1, r3⟩ := dd_log_horner p hO hu hS c hc (hSv ▸ hSC) F' hF' φ' hφ' q hq ec hlc0 f1 f2 f3
    rw [← he2] at r1
    obtain ⟨H, hH⟩ : ∃ H, H = hornerE logFe (dwVal c) q 2 := ⟨_, rfl⟩
    rw [← hH] at r1
    have hHb2 : |H| ≤ logV C q 2 := hH ▸ logV_bound (hSv ▸ hSC) q 2
    obtain ⟨y1, y2⟩ := dd_log_series p hO hu hS c _ hc r2 (hSv ▸ hSC) hHb2 r1 ec hlc0 f1 r3 f3 hZh hεh hhb hεg hεr
      (by rw [← hHb]; exact f4)
    refine ⟨y1, ?_⟩
    rw [hH, ← hSv, ← logS_eq Sv q hq] at y2
    have ht := log_tail (lt_of_le_of_lt hSC hC) q
    have h2 : |Sv| ^ (q + 1) / ((q + 1) * (1 - |Sv|)) ≤ M / (1 - C) := by
      have hq0 : (0 : ℝ) < q + 1 := by positivity
      calc |Sv| ^ (q + 1) / ((q + 1) * (1 - |Sv|)) ≤ C ^ (q + 1) / ((q + 1) * (1 - C)) :=
            div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) hSC _) (by positivity)
              (mul_le_mul_of_nonneg_left (by linarith only [hSC]) hq0.le)
        _ = C ^ (q + 1) / (q + 1) / (1 - C) := by rw [div_div]
        _ ≤ M / (1 - C) := div_le_div_of_nonneg_right (hM ▸ le_max_left _ _) hC1.le
    have h5 : |-∑ i ∈ range q, (-Sv) ^ (i + 1) / ((i : ℝ) + 1) - Real.log (1 + Sv)| ≤ M / (1 - C) := by
      rw [abs_sub_comm, sub_neg_eq_add]
      exact ht.trans h2
    calc _ ≤ |dwVal (ddSmul O S ec c (O.addF (ddSmul O S ec c
              (ddHornerP O (ddSmul O S ec c) F' q (q - 2))) 1)) -
            -∑ i ∈ range q, (-Sv) ^ (i + 1) / ((i : ℝ) + 1)| +
          |-∑ i ∈ range q, (-Sv) ^ (i + 1) / ((i : ℝ) + 1) - Real.log (1 + Sv)| +
          |Real.log (1 + Sv) - Real.log (1 + cs)| :=
          (abs_sub_le _ _ _).trans (add_le_add (abs_sub_le _ _ _) le_rfl)
      _ ≤ (εr + C * (εg + εh + C * e2)) + M / (1 - C) + Ec / (1 - C) := add_le_add (add_le_add y2 h5) hlip

omit [Prec_gt_0 p] in
/-- `l_a l_b ≤ |xy|` from `0 ≤ l_a ≤ |x|` and `l_b ≤ |y|` -/
theorem mul_le_abs_mul {la lb x y : ℝ} (h0 : 0 ≤ la) (ha : la ≤ |x|) (hb : lb ≤ |y|) : la * lb ≤ |x * y| := by
  rw [abs_mul]
  rcases le_total 0 lb with h | h
  · exact mul_le_mul ha hb h (abs_nonneg _)
  · exact (mul_nonpos_of_nonneg_of_nonpos h0 h).trans (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- step (3) read with `n = 2`: with `2^k x = e^{-e_0 - r_e}`, `|e_0| ≤ E`, `r` within `δ` of `r_e`, `a ≤ |r| ≤ b`
and the case's sign, the computed `x'` is a double word within `2η_x` of `2^k x`, and `φ = x' - 1` is a double word
with `|φ + 1| ≤ ξ` and `|φ| ≤ φ̄`; the floor of `x'` is `lo_x ≤ 2^k|x_h|`, and `φ = x' - 1` exactly is Lemma 41, a
hypothesis here -/
theorem dd_log_step3 {O : DWOps} (hO : DWSpec p O) {ηx lox : ℝ} {Sx : ℝ × ℝ → ℝ × ℝ} (hSx : SclDW p ηx lox Sx)
    (x : ℝ × ℝ) (hx : DW p x) (k : ℤ) (hlox : lox ≤ |(2 : ℝ) ^ k * x.1|)
    (hφex : dwVal (ddLogPhi O Sx k x) = dwVal (Sx (dwScale k x)) - 1) {e0 re R E a b δ : ℝ} (pos : Bool)
    (hX' : (2 : ℝ) ^ k * dwVal x = Real.exp (-e0 - re)) (hE : |e0| ≤ E) (hδ : |R - re| ≤ δ) (ha : a ≤ |R|)
    (hb : |R| ≤ b) (hsgn : if pos then 0 ≤ R else R ≤ 0) :
    DW p (ddLogPhi O Sx k x) ∧ |dwVal (ddLogPhi O Sx k x) + 1 - Real.exp (-e0 - re)| ≤ 2 * ηx ∧
      |dwVal (ddLogPhi O Sx k x) + 1| ≤ logXi (2 * ηx) pos E a b δ ∧
      |dwVal (ddLogPhi O Sx k x)| ≤ logPhiB (2 * ηx) pos E a b δ := by
  have hη := hSx.nonneg p
  have h1 := abs_le.mp hδ
  have h2 := abs_le.mp hE
  have hreR : |re| ≤ b + δ := by
    have := abs_sub_abs_le_abs_sub re R
    rw [abs_sub_comm re R] at this
    linarith only [this, hδ, hb]
  have hξ : Real.exp (-e0 - re) + 2 * ηx ≤ logXi (2 * ηx) pos E a b δ := by
    rw [logXi]
    refine add_le_add ?_ le_rfl
    cases pos with
    | true =>
      simp only [ite_true] at hsgn ⊢
      rw [abs_of_nonneg hsgn] at ha
      exact Real.exp_le_exp.mpr (by linarith only [h1.1, h1.2, h2.1, h2.2, ha])
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hsgn ⊢
      rw [abs_of_nonpos hsgn] at hb
      exact Real.exp_le_exp.mpr (by linarith only [h1.1, h1.2, h2.1, h2.2, hb])
  have hlo : Real.exp (-(E + b + δ)) ≤ Real.exp (-e0 - re) :=
    Real.exp_le_exp.mpr (by linarith only [h2.2, (abs_le.mp hreR).2])
  obtain ⟨x', hx'd⟩ : ∃ x', x' = Sx (dwScale k x) := ⟨_, rfl⟩
  have hx'dw : DW p x' := hx'd ▸ hSx.dw _ (DW.dwScale p hx k) hlox
  have hXp : |dwVal x' - Real.exp (-e0 - re)| ≤ 2 * ηx := by
    rw [hx'd, ← hX', ← dwVal_dwScale]
    exact hSx.val p _
  have hXp' := abs_le.mp hXp
  have hpos := Real.exp_pos (-e0 - re)
  have hφd : ddLogPhi O Sx k x = O.addF x' (-1) := by rw [hx'd]; rfl
  rw [← hx'd] at hφex
  refine ⟨hφd ▸ hO.addF_dw x' (-1) hx'dw (F_neg p (F_one p)), ?_, ?_, ?_⟩
  · rw [hφex, sub_add_cancel]
    exact hXp
  · rw [hφex, sub_add_cancel, abs_le]
    constructor <;> linarith only [hXp'.1, hXp'.2, hξ, hpos, hη]
  · rw [hφex, logPhiB, abs_le]
    constructor
    · linarith only [le_max_right (logXi (2 * ηx) pos E a b δ - 1) (1 - Real.exp (-(E + b + δ)) + 2 * ηx),
        hXp'.1, hlo]
    · linarith only [le_max_left (logXi (2 * ηx) pos E a b δ - 1) (1 - Real.exp (-(E + b + δ)) + 2 * ηx),
        hXp'.2, hξ]

/-- Theorem 42 (`thm:log`) read with `n = 2`, for a case, with any `t̄`, `φ̄` and `ξ` at least the theorem's: with
`x > 0` a double word, the start `y_0` a float within `E` of `ln x` and `ℓ ≥ |ln x|`; EXP's reduction of `-y_0` to a
double word `r` within `δ` of `r_e = -y_0 - k ln 2`, with `a ≤ |r| ≤ b` and the case's sign; its core with degree
`d'`; the exponents `e_φ`, `e_t` and `e_c` of steps (4) and (5) with `|v_h| + |v_l| < 2^{e_v+1}`; and
`C = e^E - 1 + E_c < 1`: `DD::ln`'s result `y` satisfies `|y - ln x| ≤ 𝓔(ℓ)`.

Lemma 41 on double words, `φ = x' - 1` exactly, is the hypothesis `hφex`. The floors of the scalings back, each a
bound below on the high part of a scaled-back pair, are: `hlo` for EXP's `t` (as in `dd_core`); `hlox`, `lo_x ≤
2^k|x_h|`, for `x'`; `hfl4` for the product `p` of step (4), where it is formed, through `l_φ ≤ |φ|` and
`l_t ≤ |t|`; and `hfl5` for the products `c ⊗ v` of step (5), where its series is formed, through `l_c ≤ |c|`,
`l_v ≤ 1/k - C v_{k+1} - e_k` for `2 ≤ k ≤ q` and `(1 - e_F)(1 - h̄)`. `hfl4` and `hfl5` may use that `φ`, `t` and
`c` are double words -/
theorem dd_thm42_case_g {O : DWOps} (hO : DWSpec p O) (hu : 4 * u p < 1) {η lo ηx lox ηp lop ηc loc : ℝ}
    {S Sx Sp Sc : ℝ × ℝ → ℝ × ℝ} (hS : SclDW p η lo S) (hSx : SclDW p ηx lox Sx) (hSp : SclDW p ηp lop Sp)
    (hSc : SclDW p ηc loc Sc) (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (y0 : ℝ) (hy0 : F p y0) (ℓ E : ℝ)
    (hℓ : |Real.log (dwVal x)| ≤ ℓ) (hE : |y0 - Real.log (dwVal x)| ≤ E) (r : ℝ × ℝ) (hr : DW p r) (k : ℤ)
    (δ : ℝ) (hδ : |dwVal r - (-y0 - k * Real.log 2)| ≤ δ) (a b : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ |dwVal r|)
    (hb : |dwVal r| ≤ b) (pos : Bool) (hsgn : if pos then 0 ≤ dwVal r else dwVal r ≤ 0) (e : ℤ) (d' : ℕ)
    (hd : 1 ≤ d') (hbd : b < d' + 2) (Fk : ℕ → ℝ × ℝ) (hF : ∀ k, DW p (Fk k)) (φF : ℕ → ℝ)
    (hφF : ∀ k, |dwVal (Fk k) - invF k| ≤ φF k)
    (hlo : d' ≠ 1 → lo * (1 + u p) ≤ a / (1 + a) - ddCoreE p (coreT pos b 0) 0 b φF d')
    (hlox : lox ≤ |(2 : ℝ) ^ k * x.1|) (hφex : dwVal (ddLogPhi O Sx k x) = dwVal (Sx (dwScale k x)) - 1)
    (B eφ et ec : ℤ) (hUφ : |(ddLogPhi O Sx k x).1| + |(ddLogPhi O Sx k x).2| < (2 : ℝ) ^ (eφ + 1))
    (hUt : |(ddExpT O S e r Fk d').1| + |(ddExpT O S e r Fk d').2| < (2 : ℝ) ^ (et + 1))
    (hUc : |(ddLogC O Sp B eφ et (ddLogPhi O Sx k x) (ddExpT O S e r Fk d')).1| +
      |(ddLogC O Sp B eφ et (ddLogPhi O Sx k x) (ddExpT O S e r Fk d')).2| < (2 : ℝ) ^ (ec + 1))
    (F' : ℕ → ℝ × ℝ) (hF' : ∀ k, DW p (F' k)) (φ' : ℕ → ℝ) (hφ' : ∀ k, |dwVal (F' k) - logFe k| ≤ φ' k) (q : ℕ)
    (hq : 2 ≤ q) {tb φb ξ : ℝ} (htbT : coreT pos b 0 ≤ tb) (hφbP : logPhiB (2 * ηx) pos E a b δ ≤ φb)
    (hξX : logXi (2 * ηx) pos E a b δ ≤ ξ) {lφ lt lc lv : ℝ} (hlφ0 : 0 ≤ lφ) (hlc0 : 0 ≤ lc)
    (hfl4 : ¬ min eφ et < -B - 13 → DW p (ddLogPhi O Sx k x) → DW p (ddExpT O S e r Fk d') →
      lφ ≤ |dwVal (ddLogPhi O Sx k x)| ∧ lt ≤ |dwVal (ddExpT O S e r Fk d')| ∧
      lop * (1 + u p) ≤ (1 - eP p) * (lφ * lt))
    (hfl5 : ¬ ec < -B - 13 → DW p (ddLogC O Sp B eφ et (ddLogPhi O Sx k x) (ddExpT O S e r Fk d')) →
      lc ≤ |dwVal (ddLogC O Sp B eφ et (ddLogPhi O Sx k x) (ddExpT O S e r Fk d'))| ∧
      (∀ j, 2 ≤ j → j ≤ q → lv ≤ 1 / (j : ℝ) -
        (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) φb tb (ddCoreE p tb η b φF d') E δ b ξ B) *
          logV (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) φb tb (ddCoreE p tb η b φF d') E δ b ξ B) q (j + 1) -
        ddHornerB p (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) φb tb (ddCoreE p tb η b φF d') E δ b ξ B)
          (2 * ηc) φ'
          (logV (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) φb tb (ddCoreE p tb η b φF d') E δ b ξ B) q) q
          (q - j)) ∧
      loc * (1 + u p) ≤ (1 - eP p) * (lc * lv) ∧
      loc * (1 + u p) ≤ (1 - eP p) * (lc * ((1 - eF p) * (1 - ddLogHb p (2 * ηc)
        (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) φb tb (ddCoreE p tb η b φF d') E δ b ξ B) φ' q))))
    (hC : Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) φb tb (ddCoreE p tb η b φF d') E δ b ξ B < 1) :
    |dwVal (ddLogOp O Sx Sp Sc y0 x k (ddExpT O S e r Fk d') B eφ et ec F' q) - Real.log (dwVal x)| ≤
      ddLogBoundG p η ηx ηp ηc ℓ E tb φb ξ b δ φF d' φ' q B := by
  have heF := eF_nonneg p
  have h1eP : 0 ≤ 1 - eP p := by linarith only [eP_le_one p hu]
  -- Lemma 39
  obtain ⟨c1', c2, c3'⟩ := dd_core p hO hu hS r hr a b ha0 ha hb e d' hd hbd Fk hF φF hφF pos hsgn hlo
  have c1 := c1'.trans (ddCoreE_mono p hu htbT η b φF d')
  have c3 := c3'.trans htbT
  obtain ⟨R, hR⟩ : ∃ R, R = dwVal r := ⟨_, rfl⟩
  rw [← hR] at hδ ha hb hsgn c1 c3
  obtain ⟨t, htd⟩ : ∃ t, t = ddExpT O S e r Fk d' := ⟨_, rfl⟩
  rw [← htd] at c1 c2 hUt hUc hfl4 hfl5 ⊢
  obtain ⟨Em, hEm⟩ : ∃ Em, Em = ddCoreE p tb η b φF d' := ⟨_, rfl⟩
  rw [← hEm] at c1 hfl5 hC
  have hB : ddLogBoundG p η ηx ηp ηc ℓ E tb φb ξ b δ φF d' φ' q B =
      eF p * (ℓ + ddLogP p (2 * ηc) (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) φb tb Em E δ b ξ B)
        (ddLogEc p (2 * ηx) (2 * ηp) φb tb Em E δ b ξ B) φ' q B) +
      ddLogP p (2 * ηc) (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) φb tb Em E δ b ξ B)
        (ddLogEc p (2 * ηx) (2 * ηp) φb tb Em E δ b ξ B) φ' q B := by
    rw [hEm]
    rfl
  rw [hB]
  -- `2^k x = e^{-e_0 - r_e}` with `e_0 = y_0 - ln x` and `r_e = -y_0 - k ln 2`
  obtain ⟨X, hXd⟩ : ∃ X, X = dwVal x := ⟨_, rfl⟩
  rw [← hXd] at hX0 hℓ hE ⊢
  obtain ⟨e0, he0d⟩ : ∃ e0, e0 = y0 - Real.log X := ⟨_, rfl⟩
  obtain ⟨re, hred⟩ : ∃ re, re = -y0 - k * Real.log 2 := ⟨_, rfl⟩
  rw [← he0d] at hE
  rw [← hred] at hδ
  have hX' : (2 : ℝ) ^ k * dwVal x = Real.exp (-e0 - re) := by
    rw [← hXd, he0d, hred, show -(y0 - Real.log X) - (-y0 - k * Real.log 2) = Real.log X + k * Real.log 2 by ring,
      Real.exp_add, Real.exp_log hX0, exp_int_mul_log_two, mul_comm]
  -- step (3)
  obtain ⟨s1, s2, s3', s4'⟩ := dd_log_step3 p hO hSx x hx k hlox hφex pos hX' hE hδ ha hb hsgn
  have s3 := s3'.trans hξX
  have s4 := s4'.trans hφbP
  obtain ⟨φ, hφd⟩ : ∃ φ, φ = ddLogPhi O Sx k x := ⟨_, rfl⟩
  rw [← hφd] at s1 s2 s3 s4 hUφ hUc hfl4 hfl5
  -- step (4)
  obtain ⟨x1, x2, x3⟩ := log_c_exact hδ hE hb s2 s3 c1 c3
  have htbT' : |dwVal t| ≤ tb + Em := by
    have := abs_sub_abs_le_abs_sub (dwVal t) (Real.exp R - 1)
    linarith only [this, c1, c3]
  obtain ⟨d1, d2⟩ := dd_log_step4 p hO hu hSp φ t s1 c2 s4 htbT' x3 x2 x1 B eφ et hUφ hUt (fun h => by
    obtain ⟨f1, f2, f3⟩ := hfl4 h s1 c2
    exact f3.trans (mul_le_mul_of_nonneg_left (mul_le_abs_mul hlφ0 f1 f2) h1eP))
  obtain ⟨c, hcd⟩ : ∃ c, c = ddLogC O Sp B eφ et φ t := ⟨_, rfl⟩
  rw [← hcd] at d1 d2 hUc hfl5
  obtain ⟨Ec, hEcd⟩ : ∃ Ec, Ec = ddLogEc p (2 * ηx) (2 * ηp) φb tb Em E δ b ξ B := ⟨_, rfl⟩
  rw [← hEcd] at hfl5 hC ⊢
  have hEc : |dwVal c - (Real.exp (-e0) - 1)| ≤ Ec := by
    refine d2.trans (le_of_eq ?_)
    rw [hEcd]
    unfold ddLogEc
    ring
  -- step (5)
  obtain ⟨g1, g2⟩ := dd_log_step5 p hO hu hSc c d1 x1 hEc hC F' hF' φ' hφ' q hq B ec hUc hlc0
    (fun h => hfl5 h d1)
  rw [show 1 + (Real.exp (-e0) - 1) = Real.exp (-e0) by ring, Real.log_exp] at g2
  obtain ⟨yc, hycd⟩ : ∃ yc, yc = ddLogYc O Sc B ec c F' q := ⟨_, rfl⟩
  rw [← hycd] at g1 g2
  obtain ⟨P, hPd⟩ : ∃ P, P = ddLogP p (2 * ηc) (Real.exp E - 1 + Ec) Ec φ' q B := ⟨_, rfl⟩
  rw [← hPd] at g2 ⊢
  -- the last DWPlusFP
  have hres : ddLogOp O Sx Sp Sc y0 x k t B eφ et ec F' q = O.addF yc y0 := by
    rw [hycd, hcd, hφd]
    rfl
  rw [hres]
  have hsum : |dwVal yc + y0 - Real.log X| ≤ P := by
    rw [show dwVal yc + y0 - Real.log X = dwVal yc - -e0 by rw [he0d]; ring]
    exact g2
  have hZ : |dwVal yc + y0| ≤ ℓ + P := by
    calc |dwVal yc + y0| = |Real.log X + (dwVal yc + y0 - Real.log X)| := by ring_nf
      _ ≤ |Real.log X| + |dwVal yc + y0 - Real.log X| := abs_add_le _ _
      _ ≤ ℓ + P := add_le_add hℓ hsum
  have hadd := (hO.addF_err yc y0 g1 hy0).trans (mul_le_mul_of_nonneg_left hZ heF)
  calc |dwVal (O.addF yc y0) - Real.log X| =
        |(dwVal (O.addF yc y0) - (dwVal yc + y0)) + (dwVal yc + y0 - Real.log X)| := by ring_nf
    _ ≤ |dwVal (O.addF yc y0) - (dwVal yc + y0)| + |dwVal yc + y0 - Real.log X| := abs_add_le _ _
    _ ≤ eF p * (ℓ + P) + P := add_le_add hadd hsum

/-- Theorem 42 (`thm:log`) read with `n = 2`, for a case, with the theorem's `t̄`, `φ̄` and `ξ`: `|y - ln x| ≤ 𝓔(ℓ)`;
the hypotheses are those of `dd_thm42_case_g` -/
theorem dd_thm42_case {O : DWOps} (hO : DWSpec p O) (hu : 4 * u p < 1) {η lo ηx lox ηp lop ηc loc : ℝ}
    {S Sx Sp Sc : ℝ × ℝ → ℝ × ℝ} (hS : SclDW p η lo S) (hSx : SclDW p ηx lox Sx) (hSp : SclDW p ηp lop Sp)
    (hSc : SclDW p ηc loc Sc) (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (y0 : ℝ) (hy0 : F p y0) (ℓ E : ℝ)
    (hℓ : |Real.log (dwVal x)| ≤ ℓ) (hE : |y0 - Real.log (dwVal x)| ≤ E) (r : ℝ × ℝ) (hr : DW p r) (k : ℤ)
    (δ : ℝ) (hδ : |dwVal r - (-y0 - k * Real.log 2)| ≤ δ) (a b : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ |dwVal r|)
    (hb : |dwVal r| ≤ b) (pos : Bool) (hsgn : if pos then 0 ≤ dwVal r else dwVal r ≤ 0) (e : ℤ) (d' : ℕ)
    (hd : 1 ≤ d') (hbd : b < d' + 2) (Fk : ℕ → ℝ × ℝ) (hF : ∀ k, DW p (Fk k)) (φF : ℕ → ℝ)
    (hφF : ∀ k, |dwVal (Fk k) - invF k| ≤ φF k)
    (hlo : d' ≠ 1 → lo * (1 + u p) ≤ a / (1 + a) - ddCoreE p (coreT pos b 0) 0 b φF d')
    (hlox : lox ≤ |(2 : ℝ) ^ k * x.1|) (hφex : dwVal (ddLogPhi O Sx k x) = dwVal (Sx (dwScale k x)) - 1)
    (B eφ et ec : ℤ) (hUφ : |(ddLogPhi O Sx k x).1| + |(ddLogPhi O Sx k x).2| < (2 : ℝ) ^ (eφ + 1))
    (hUt : |(ddExpT O S e r Fk d').1| + |(ddExpT O S e r Fk d').2| < (2 : ℝ) ^ (et + 1))
    (hUc : |(ddLogC O Sp B eφ et (ddLogPhi O Sx k x) (ddExpT O S e r Fk d')).1| +
      |(ddLogC O Sp B eφ et (ddLogPhi O Sx k x) (ddExpT O S e r Fk d')).2| < (2 : ℝ) ^ (ec + 1))
    (F' : ℕ → ℝ × ℝ) (hF' : ∀ k, DW p (F' k)) (φ' : ℕ → ℝ) (hφ' : ∀ k, |dwVal (F' k) - logFe k| ≤ φ' k) (q : ℕ)
    (hq : 2 ≤ q) {lφ lt lc lv : ℝ} (hlφ0 : 0 ≤ lφ) (hlc0 : 0 ≤ lc)
    (hfl4 : ¬ min eφ et < -B - 13 → DW p (ddLogPhi O Sx k x) → DW p (ddExpT O S e r Fk d') →
      lφ ≤ |dwVal (ddLogPhi O Sx k x)| ∧ lt ≤ |dwVal (ddExpT O S e r Fk d')| ∧
      lop * (1 + u p) ≤ (1 - eP p) * (lφ * lt))
    (hfl5 : ¬ ec < -B - 13 → DW p (ddLogC O Sp B eφ et (ddLogPhi O Sx k x) (ddExpT O S e r Fk d')) →
      lc ≤ |dwVal (ddLogC O Sp B eφ et (ddLogPhi O Sx k x) (ddExpT O S e r Fk d'))| ∧
      (∀ j, 2 ≤ j → j ≤ q → lv ≤ 1 / (j : ℝ) -
        (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) (logPhiB (2 * ηx) pos E a b δ) (coreT pos b 0)
          (ddCoreE p (coreT pos b 0) η b φF d') E δ b (logXi (2 * ηx) pos E a b δ) B) *
          logV (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) (logPhiB (2 * ηx) pos E a b δ) (coreT pos b 0)
            (ddCoreE p (coreT pos b 0) η b φF d') E δ b (logXi (2 * ηx) pos E a b δ) B) q (j + 1) -
        ddHornerB p (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) (logPhiB (2 * ηx) pos E a b δ) (coreT pos b 0)
            (ddCoreE p (coreT pos b 0) η b φF d') E δ b (logXi (2 * ηx) pos E a b δ) B) (2 * ηc) φ'
          (logV (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) (logPhiB (2 * ηx) pos E a b δ) (coreT pos b 0)
            (ddCoreE p (coreT pos b 0) η b φF d') E δ b (logXi (2 * ηx) pos E a b δ) B) q) q (q - j)) ∧
      loc * (1 + u p) ≤ (1 - eP p) * (lc * lv) ∧
      loc * (1 + u p) ≤ (1 - eP p) * (lc * ((1 - eF p) * (1 - ddLogHb p (2 * ηc)
        (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) (logPhiB (2 * ηx) pos E a b δ) (coreT pos b 0)
          (ddCoreE p (coreT pos b 0) η b φF d') E δ b (logXi (2 * ηx) pos E a b δ) B) φ' q))))
    (hC : Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) (logPhiB (2 * ηx) pos E a b δ) (coreT pos b 0)
      (ddCoreE p (coreT pos b 0) η b φF d') E δ b (logXi (2 * ηx) pos E a b δ) B < 1) :
    |dwVal (ddLogOp O Sx Sp Sc y0 x k (ddExpT O S e r Fk d') B eφ et ec F' q) - Real.log (dwVal x)| ≤
      ddLogBound p η ηx ηp ηc ℓ E pos a b δ φF d' φ' q B :=
  dd_thm42_case_g p hO hu hS hSx hSp hSc x hx hX0 y0 hy0 ℓ E hℓ hE r hr k δ hδ a b ha0 ha hb pos hsgn e d' hd hbd
    Fk hF φF hφF hlo hlox hφex B eφ et ec hUφ hUt hUc F' hF' φ' hφ' q hq le_rfl le_rfl le_rfl hlφ0 hlc0 hfl4 hfl5 hC

end ExpansionBounds
