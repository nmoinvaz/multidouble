import ExpansionBounds.Sqrt

/-!
# Theorem 22: SQRT^DD

SQRT^DD_n scales `x` as SQRT_{n,J} does and starts from a double word: `v` the double-word square root (Algorithm 8 of
LLMPR23) of `(a_0', a_1') = FastTwoSum(a_0, a_1)`, whose sum is `a_0 + a_1` exactly as `|a_1| ≤ ρ|a_0|`, and
`r = (r_0, r_1, 0, …, 0)` approximating `1/v` (DWDivDW2 of JMP17). The theorems on those algorithms enter as hypotheses,
as in the paper: `v = √(a_0 + a_1)(1 + d_1)` with `|d_1| ≤ η_1 = 25u²/8`, `rv = 1 + d_2` with
`|d_2| ≤ η_2 = 15u² + 56u³`, and `|r_1| ≤ u|r_0|` from their last `FastTwoSum`. With `a = (a_0 + a_1)(1 + d_3)`,
`|d_3| ≤ η_3 = ρ²/(1 - ρ)²`, `r√a = (1 + d_2)√(1 + d_3)/(1 + d_1)` is within `E_0` of 1. One second-order step follows:
`c` as in SQRT, `q = MUL(c, c)`, `t = ADD(q, q/2)`, `w = ADD(c, t)`, `d = MUL(w, r)` and `r ← ADD(r, d)`, with
`(1 + e)(1 + c_e + 3c_e²/2) = 1 + 5e³/2 + 15e⁴/8 + 3e⁵/8` for the exact `c_e = -e - e²/2`. Then one step of SQRT_{n,J}
and the end of SQRT.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ)

/-- `q = MUL(c, c)` -/
noncomputable def sqrtQ (h r : ℕ → ℝ) : ℕ → ℝ := lf (mulOp p n (sqrtCop p n h r) (sqrtCop p n h r))

/-- `w = ADD(c, ADD(q, q/2))` -/
noncomputable def sqrtW (h r : ℕ → ℝ) : ℕ → ℝ :=
  lf (addOp p n (sqrtCop p n h r) (lf (addOp p n (sqrtQ p n h r) fun i => sqrtQ p n h r i / 2)))

/-- the second-order step of SQRT^DD: `d = MUL(w, r)` and `ADD(r, d)` -/
noncomputable def sqrtStep2 (h r : ℕ → ℝ) : ℕ → ℝ := lf (addOp p n r (lf (mulOp p n (sqrtW p n h r) r)))

/-- SQRT^DD_n from the double-word start `(r_0, r_1)`: the second-order step, one Newton step, then `MUL(r, a)`
scaled by `s` -/
noncomputable def sqrtDDOp (x : ℕ → ℝ) (r0 r1 : ℝ) : List ℝ :=
  (mulOp p n (sqrtStep p n (fun i => sqrtA p x i / 2) (sqrtStep2 p n (fun i => sqrtA p x i / 2)
    fun i => if i = 0 then r0 else if i = 1 then r1 else 0)) (sqrtA p x)).map
    fun v => (2 : ℝ) ^ sqrtE p (x 0) * v

/-- `η_1 = 25u²/8`, the relative error of the double-word square root -/
noncomputable def ddEta1 : ℝ := 25 / 8 * u p ^ 2

/-- `η_2 = 15u² + 56u³`, the relative error of DWDivDW2 -/
noncomputable def ddEta2 : ℝ := 15 * u p ^ 2 + 56 * u p ^ 3

/-- `η_3 = ρ²/(1 - ρ)²`, the relative size of `a_2 + a_3 + …` -/
noncomputable def ddEta3 (ρ : ℝ) : ℝ := ρ ^ 2 / (1 - ρ) ^ 2

/-- `E_0 = max((1 + η_3/2)(1 + η_2)/(1 - η_1) - 1, 1 - (1 - η_3)(1 - η_2)/(1 + η_1))` -/
noncomputable def ddE0 (ρ : ℝ) : ℝ :=
  max ((1 + ddEta3 ρ / 2) * (1 + ddEta2 p) / (1 - ddEta1 p) - 1) (1 - (1 - ddEta3 ρ) * (1 - ddEta2 p) / (1 + ddEta1 p))

/-- `π^{(0)} = ((1 + E_0)/(1 - u), u(1 + E_0)/(1 - u), 0, …, 0)` -/
noncomputable def ddPi0 (ρ : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then (1 + ddE0 p ρ) / (1 - u p) else if i = 1 then u p * (1 + ddE0 p ρ) / (1 - u p) else 0

/-- the second-order step's bounds `(E_1, π^{(1)})` from `(E, π)` -/
noncomputable def sqrtB2 (hb : ℕ → ℝ) (E : ℝ) (π : ℕ → ℝ) : ℝ × (ℕ → ℝ) :=
  let εmgc := sqrtEm p n E π / 2 + sqrtEg p n hb E π + sqrtEc p n hb E π
  let cb := sqrtZc p n hb E π + sqrtEc p n hb E π
  let χ := sqrtChi p n hb E π
  let εq := GmulE p n χ χ (cb ^ 2)
  let ν := GmulP p n χ χ (cb ^ 2)
  let qb := cb ^ 2 + εq
  let εt := GaddE p n ν (fun i => ν i / 2) (3 / 2 * qb)
  let ϑ := GaddP p n ν (fun i => ν i / 2) (3 / 2 * qb)
  let tb := 3 / 2 * qb + εt
  let εw := GaddE p n χ ϑ (cb + tb)
  let ω := GaddP p n χ ϑ (cb + tb)
  let wb := cb + tb + εw
  let εd := GmulE p n ω π (wb * (1 + E))
  let δ := GmulP p n ω π (wb * (1 + E))
  let Zr := (1 + E) + wb * (1 + E) + εd
  (5 / 2 * E ^ 3 + 15 / 8 * E ^ 4 + 3 / 8 * E ^ 5 + εd + GaddE p n π δ Zr +
    (1 + E) * (εmgc * (1 + 3 * (E + E ^ 2 / 2) + 3 / 2 * εmgc) + 3 / 2 * εq + εt + εw), GaddP p n π δ Zr)

/-- `δ^DD = E_2 + ε_z`: the second-order step from `(E_0, π^{(0)})`, one step of SQRT_{n,J}, and
`(ε_z, ·) = G_MUL(π^{(2)}, ā; 1 + E_2)` -/
noncomputable def ddDelta (ρ : ℝ) : ℝ :=
  (sqrtB p n (fun i => abar ρ i / 2) (sqrtB2 p n (fun i => abar ρ i / 2) (ddE0 p ρ) (ddPi0 p ρ)).1
      (sqrtB2 p n (fun i => abar ρ i / 2) (ddE0 p ρ) (ddPi0 p ρ)).2).1 +
    GmulE p n (sqrtB p n (fun i => abar ρ i / 2) (sqrtB2 p n (fun i => abar ρ i / 2) (ddE0 p ρ) (ddPi0 p ρ)).1
      (sqrtB2 p n (fun i => abar ρ i / 2) (ddE0 p ρ) (ddPi0 p ρ)).2).2 (abar ρ)
      (1 + (sqrtB p n (fun i => abar ρ i / 2) (sqrtB2 p n (fun i => abar ρ i / 2) (ddE0 p ρ) (ddPi0 p ρ)).1
        (sqrtB2 p n (fun i => abar ρ i / 2) (ddE0 p ρ) (ddPi0 p ρ)).2).1)

variable [Prec_gt_0 p]

/-- the second-order step: from `r` within `Ey` of `y = a^{-1/2}` with parts within `yπ`, the next `r` is within
`E_1y` of `y` with parts within `yπ^{(1)}` -/
theorem sqrt_step2 (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {A y : ℝ} (hy : 0 < y)
    (hAy : A * y ^ 2 = 1) (h hb : ℕ → ℝ) (hh : ∀ i < n, F p (h i)) (hhb : ∀ i < n, |h i| ≤ A * hb i)
    (hb0 : ∀ i, 0 ≤ hb i) (hH : ∑ i ∈ range n, h i = A / 2) (r : ℕ → ℝ) (E : ℝ) (π : ℕ → ℝ) (hE : 0 ≤ E)
    (hπ : ∀ i, 0 ≤ π i) (hr : ∀ i < n, F p (r i)) (hrπ : ∀ i < n, |r i| ≤ y * π i)
    (hR : |∑ i ∈ range n, r i - y| ≤ E * y) :
    (∀ i < n, F p (sqrtStep2 p n h r i)) ∧ (∀ i < n, |sqrtStep2 p n h r i| ≤ y * (sqrtB2 p n hb E π).2 i) ∧
      |∑ i ∈ range n, sqrtStep2 p n h r i - y| ≤ (sqrtB2 p n hb E π).1 * y ∧ 0 ≤ (sqrtB2 p n hb E π).1 ∧
      ∀ i, 0 ≤ (sqrtB2 p n hb E π).2 i := by
  have hA : 0 < A := by
    by_contra hc
    have : A * y ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) (sq_nonneg y)
    linarith
  obtain ⟨c3, c2, hχ0, hce, hCb, hεm0, hεg0, hεc0, hZc0⟩ :=
    sqrt_c p n hp hn hA3 hy hAy h hb hh hhb hb0 hH r E π hE hπ hr hrπ hR
  set c := sqrtCop p n h r with hc
  set χ := sqrtChi p n hb E π with hχ
  set R := ∑ i ∈ range n, r i with hRd
  set C := ∑ i ∈ range n, c i with hCd
  set εmgc := sqrtEm p n E π / 2 + sqrtEg p n hb E π + sqrtEc p n hb E π with hεmgc
  set cb := sqrtZc p n hb E π + sqrtEc p n hb E π with hcb
  have hcb0 : 0 ≤ cb := add_nonneg hZc0 hεc0
  have hεmgc0 : 0 ≤ εmgc := add_nonneg (add_nonneg (div_nonneg hεm0 zero_le_two) hεg0) hεc0
  have hRb : |R| ≤ (1 + E) * y := by
    have := abs_sub_abs_le_abs_sub R y
    rw [abs_of_pos hy] at this
    linarith
  have h1E : (0 : ℝ) ≤ 1 + E := by linarith
  have hEy : 0 ≤ (1 + E) * y := mul_nonneg h1E hy.le
  -- `q = MUL(c, c)`, in units of `1`
  set εq := GmulE p n χ χ (cb ^ 2) with hεq
  set ν := GmulP p n χ χ (cb ^ 2) with hν
  obtain ⟨hεq0, hν0⟩ := Gmul_nonneg p n hA3 hχ0 hχ0 (sq_nonneg cb)
  have hCC : |C * C| ≤ cb ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul hCb hCb (abs_nonneg _) hcb0
  obtain ⟨q1, q2, q3, q4⟩ := mul_G p n hp hn hA3 c c χ χ c3 c3 c2 c2 _ hCC
  set q := sqrtQ p n h r with hq
  set Q := ∑ i ∈ range n, q i with hQd
  have hQs : Q = (mulOp p n c c).sum := (list_sum_getD _ n q4).symm
  rw [← hQs] at q1
  replace q1 : |C * C - Q| ≤ εq := q1
  set qb := cb ^ 2 + εq with hqb
  have hQb : |Q| ≤ qb := by
    have := abs_sub_abs_le_abs_sub Q (C * C)
    rw [abs_sub_comm] at q1
    linarith
  -- `t = ADD(q, q/2)`
  set εt := GaddE p n ν (fun i => ν i / 2) (3 / 2 * qb) with hεt
  set ϑ := GaddP p n ν (fun i => ν i / 2) (3 / 2 * qb) with hϑ
  have hqb0 : 0 ≤ qb := add_nonneg (sq_nonneg _) hεq0
  obtain ⟨hεt0, hϑ0⟩ := Gadd_nonneg p n hA3 hν0 (fun i => div_nonneg (hν0 i) zero_le_two)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) hqb0)
  have hq2F : ∀ i < n, F p (q i / 2) := fun i _ => by
    have := F_zpow_mul p (-1) (q3 i)
    rwa [zpow_neg, zpow_one, ← div_eq_inv_mul] at this
  have hQ2 : ∑ i ∈ range n, q i + ∑ i ∈ range n, q i / 2 = 3 / 2 * Q := by rw [← sum_div]; ring
  have hQQ : |∑ i ∈ range n, q i + ∑ i ∈ range n, q i / 2| ≤ 3 / 2 * qb := by
    rw [hQ2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    exact mul_le_mul_of_nonneg_left hQb (by norm_num)
  obtain ⟨t1, t2, t3, t4⟩ := add_G p n hp hn hA3 q (fun i => q i / 2) ν (fun i => ν i / 2) (fun i _ => q3 i) hq2F
    (fun i _ => q2 i) (fun i _ => by rw [abs_div, abs_two]; exact div_le_div_of_nonneg_right (q2 i) zero_le_two) _ hQQ
  rw [hQ2] at t1
  set t := lf (addOp p n q fun i => q i / 2) with ht
  set T := ∑ i ∈ range n, t i with hTd
  have hTs : T = (addOp p n q fun i => q i / 2).sum := (list_sum_getD _ n t4).symm
  rw [← hTs] at t1
  set tb := 3 / 2 * qb + εt with htb
  have hTb : |T| ≤ tb := by
    have := abs_sub_abs_le_abs_sub T (3 / 2 * Q)
    rw [abs_sub_comm] at t1
    have h32 : |3 / 2 * Q| ≤ 3 / 2 * qb := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
      exact mul_le_mul_of_nonneg_left hQb (by norm_num)
    linarith
  -- `w = ADD(c, t)`
  set εw := GaddE p n χ ϑ (cb + tb) with hεw
  set ω := GaddP p n χ ϑ (cb + tb) with hω
  have htb0 : 0 ≤ tb := add_nonneg (mul_nonneg (by norm_num) hqb0) hεt0
  obtain ⟨hεw0, hω0⟩ := Gadd_nonneg p n hA3 hχ0 hϑ0 (add_nonneg hcb0 htb0)
  have hCT : |C + T| ≤ cb + tb := (abs_add_le _ _).trans (add_le_add hCb hTb)
  obtain ⟨w1, w2, w3, w4⟩ := add_G p n hp hn hA3 c t χ ϑ c3 (fun i _ => t3 i) c2 (fun i _ => t2 i) _ hCT
  set w := sqrtW p n h r with hw
  set W := ∑ i ∈ range n, w i with hWd
  have hWs : W = (addOp p n c t).sum := (list_sum_getD _ n w4).symm
  rw [← hWs] at w1
  set wb := cb + tb + εw with hwb
  have hWb : |W| ≤ wb := by
    have := abs_sub_abs_le_abs_sub W (C + T)
    rw [abs_sub_comm] at w1
    linarith
  have hwb0 : 0 ≤ wb := add_nonneg (add_nonneg hcb0 htb0) hεw0
  -- `d = MUL(w, r)`, in units of `y`
  set εd := GmulE p n ω π (wb * (1 + E)) with hεd
  set δ := GmulP p n ω π (wb * (1 + E)) with hδ
  obtain ⟨hεd0, hδ0⟩ := Gmul_nonneg p n hA3 hω0 hπ (mul_nonneg hwb0 h1E)
  have hWR : |W * R| ≤ 1 * y * (wb * (1 + E)) := by
    rw [abs_mul]
    calc |W| * |R| ≤ wb * ((1 + E) * y) := mul_le_mul hWb hRb (abs_nonneg _) hwb0
      _ = 1 * y * (wb * (1 + E)) := by ring
  obtain ⟨d1, d2, d3, d4⟩ := mul_G p n hp hn hA3 w r (fun i => 1 * ω i) (fun j => y * π j) (fun i _ => w3 i) hr
    (fun i _ => by rw [one_mul]; exact w2 i) hrπ _ hWR
  obtain ⟨u1, u2⟩ := Gmul_smul p n ω π (wb * (1 + E)) zero_le_one hy.le
  rw [u1, one_mul] at d1
  set d := lf (mulOp p n w r) with hd
  set D := ∑ i ∈ range n, d i with hDd
  have hDs : D = (mulOp p n w r).sum := (list_sum_getD _ n d4).symm
  rw [← hDs] at d1
  have hdb : ∀ i < n, |d i| ≤ y * δ i := fun i _ => by
    have := d2 i
    rw [u2 i, one_mul] at this
    exact this
  -- `r' = ADD(r, d)`, in units of `y`
  set Zr := (1 + E) + wb * (1 + E) + εd with hZr
  have hRD : |R + D| ≤ y * Zr := by
    have : |D| ≤ |W * R| + y * εd := by
      have := abs_sub_abs_le_abs_sub D (W * R)
      rw [abs_sub_comm] at d1
      linarith
    calc |R + D| ≤ |R| + |D| := abs_add_le _ _
      _ ≤ (1 + E) * y + (1 * y * (wb * (1 + E)) + y * εd) := add_le_add hRb (this.trans (by linarith))
      _ = y * Zr := by rw [hZr]; ring
  obtain ⟨a1, a2, a3, a4⟩ := add_G p n hp hn hA3 r d (fun i => y * π i) (fun j => y * δ j) hr (fun i _ => d3 i)
    hrπ hdb _ hRD
  obtain ⟨v1, v2⟩ := Gadd_smul p n π δ Zr hy.le
  rw [v1] at a1
  have hZr0 : 0 ≤ Zr := add_nonneg (add_nonneg h1E (mul_nonneg hwb0 h1E)) hεd0
  obtain ⟨hεr0, hπ'0⟩ := Gadd_nonneg p n hA3 hπ hδ0 hZr0
  set εr := GaddE p n π δ Zr with hεr
  set K := εmgc * (1 + 3 * (E + E ^ 2 / 2) + 3 / 2 * εmgc) + 3 / 2 * εq + εt + εw with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ 1 + 3 * (E + E ^ 2 / 2) + 3 / 2 * εmgc := by positivity
    exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg hεmgc0 this) (mul_nonneg (by norm_num) hεq0)) hεt0) hεw0
  have hB : sqrtB2 p n hb E π = (5 / 2 * E ^ 3 + 15 / 8 * E ^ 4 + 3 / 8 * E ^ 5 + εd + εr + (1 + E) * K,
      GaddP p n π δ Zr) := rfl
  have hstep : sqrtStep2 p n h r = lf (addOp p n r d) := rfl
  have hE'0 : 0 ≤ 5 / 2 * E ^ 3 + 15 / 8 * E ^ 4 + 3 / 8 * E ^ 5 + εd + εr + (1 + E) * K :=
    add_nonneg (add_nonneg (add_nonneg (by positivity) hεd0) hεr0) (mul_nonneg h1E hK0)
  rw [hB, hstep]
  refine ⟨fun i _ => a3 i, fun i _ => by rw [← v2 i]; exact a2 i, ?_, hE'0, hπ'0⟩
  -- `r' - y = (r(1 + w_e) - y) + r(w - w_e) + ε̂_d + ε̂_r`, `w_e = c_e + 3c_e²/2`
  have hRs : ∑ i ∈ range n, lf (addOp p n r d) i = (addOp p n r d).sum := (list_sum_getD _ n a4).symm
  rw [hRs]
  set R' := (addOp p n r d).sum with hR'
  set e := R / y - 1 with he
  have hRe : R = y * (1 + e) := by rw [he]; field_simp; ring
  have heE : |e| ≤ E := by
    rw [he, show R / y - 1 = (R - y) / y by field_simp, abs_div, abs_of_pos hy, div_le_iff₀ hy]
    exact hR
  set ce := 1 / 2 - A / 2 * (R * R) with hce_d
  have hce_v : ce = -(e + e ^ 2 / 2) := by
    rw [hce_d, hRe]
    linear_combination (-(1 + e) ^ 2 / 2) * hAy
  have hceb : |ce| ≤ E + E ^ 2 / 2 := by
    rw [hce_v, abs_neg]
    refine (abs_add_le _ _).trans (add_le_add heE ?_)
    rw [abs_div, abs_pow, abs_two]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg e) heE 2) zero_le_two
  have hN : R * (1 + (ce + 3 / 2 * ce ^ 2)) - y = y * (5 / 2 * e ^ 3 + 15 / 8 * e ^ 4 + 3 / 8 * e ^ 5) := by
    rw [hce_v, hRe]
    ring
  have hid : R' - y = (R * (1 + (ce + 3 / 2 * ce ^ 2)) - y) + R * (W - (ce + 3 / 2 * ce ^ 2)) + (D - W * R) -
      ((R + D) - R') := by ring
  have hWw : |W - (ce + 3 / 2 * ce ^ 2)| ≤ K := by
    have hsplit : W - (ce + 3 / 2 * ce ^ 2) = (C - ce) + 3 / 2 * ((C - ce) * (C + ce)) + 3 / 2 * (Q - C * C) +
        (T - 3 / 2 * Q) + (W - (C + T)) := by ring
    have e1 : |(C - ce) * (C + ce)| ≤ εmgc * (εmgc + 2 * (E + E ^ 2 / 2)) := by
      rw [abs_mul]
      have : |C + ce| ≤ εmgc + 2 * (E + E ^ 2 / 2) := by
        calc |C + ce| = |(C - ce) + 2 * ce| := by congr 1; ring
          _ ≤ |C - ce| + |2 * ce| := abs_add_le _ _
          _ ≤ εmgc + 2 * (E + E ^ 2 / 2) := by
              rw [abs_mul, abs_two]
              exact add_le_add hce (mul_le_mul_of_nonneg_left hceb zero_le_two)
      exact mul_le_mul hce this (abs_nonneg _) hεmgc0
    rw [hsplit]
    calc _ ≤ |C - ce| + |3 / 2 * ((C - ce) * (C + ce))| + |3 / 2 * (Q - C * C)| + |T - 3 / 2 * Q| +
          |W - (C + T)| := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
      _ ≤ εmgc + 3 / 2 * (εmgc * (εmgc + 2 * (E + E ^ 2 / 2))) + 3 / 2 * εq + εt + εw := by
          rw [abs_mul (3 / 2 : ℝ), abs_mul (3 / 2 : ℝ), abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
          refine add_le_add (add_le_add (add_le_add (add_le_add hce
            (mul_le_mul_of_nonneg_left e1 (by norm_num : (0 : ℝ) ≤ 3 / 2)))
            (mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 3 / 2))) ?_) ?_
          · rw [abs_sub_comm]; exact q1
          · rw [abs_sub_comm]; exact t1
          · rw [abs_sub_comm]; exact w1
      _ = K := by rw [hK]; ring
  rw [hid, hN]
  have hpoly : |y * (5 / 2 * e ^ 3 + 15 / 8 * e ^ 4 + 3 / 8 * e ^ 5)| ≤
      y * (5 / 2 * E ^ 3 + 15 / 8 * E ^ 4 + 3 / 8 * E ^ 5) := by
    rw [abs_mul, abs_of_pos hy]
    refine mul_le_mul_of_nonneg_left ?_ hy.le
    have h3 := pow_le_pow_left₀ (abs_nonneg e) heE 3
    have h4 := pow_le_pow_left₀ (abs_nonneg e) heE 4
    have h5 := pow_le_pow_left₀ (abs_nonneg e) heE 5
    calc _ ≤ |5 / 2 * e ^ 3| + |15 / 8 * e ^ 4| + |3 / 8 * e ^ 5| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = 5 / 2 * |e| ^ 3 + 15 / 8 * |e| ^ 4 + 3 / 8 * |e| ^ 5 := by
          rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow]
          norm_num
      _ ≤ _ := add_le_add (add_le_add (mul_le_mul_of_nonneg_left h3 (by norm_num))
          (mul_le_mul_of_nonneg_left h4 (by norm_num))) (mul_le_mul_of_nonneg_left h5 (by norm_num))
  have hmid : |R * (W - (ce + 3 / 2 * ce ^ 2))| ≤ (1 + E) * y * K := by
    rw [abs_mul]
    exact mul_le_mul hRb hWw (abs_nonneg _) hEy
  have hd' : |D - W * R| ≤ y * εd := by rw [abs_sub_comm]; exact d1
  calc _ ≤ |y * (5 / 2 * e ^ 3 + 15 / 8 * e ^ 4 + 3 / 8 * e ^ 5)| + |R * (W - (ce + 3 / 2 * ce ^ 2))| +
        |D - W * R| + |(R + D) - R'| :=
        (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ y * (5 / 2 * E ^ 3 + 15 / 8 * E ^ 4 + 3 / 8 * E ^ 5) + (1 + E) * y * K + y * εd + y * εr :=
        add_le_add (add_le_add (add_le_add hpoly hmid) hd') a1
    _ = _ := by ring

omit [Prec_gt_0 p] in
/-- `√t` lies between `1 - η` and `1 + η/2` for `|t - 1| ≤ η` -/
theorem sqrt_near_one {t η : ℝ} (ht : |t - 1| ≤ η) : 1 - η ≤ Real.sqrt t ∧ Real.sqrt t ≤ 1 + η / 2 := by
  have h1 := (abs_le.mp ht).1
  have h2 := (abs_le.mp ht).2
  constructor
  · by_cases hη : 1 - η ≤ 0
    · exact hη.trans (Real.sqrt_nonneg t)
    · push Not at hη
      have hη0 : 0 ≤ η := (abs_nonneg _).trans ht
      rw [show 1 - η = Real.sqrt ((1 - η) ^ 2) from (Real.sqrt_sq hη.le).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
  · by_cases ht0 : t ≤ 0
    · rw [Real.sqrt_eq_zero'.mpr ht0]
      have hη0 : 0 ≤ η := (abs_nonneg _).trans ht
      linarith
    · push Not at ht0
      have hs := Real.sq_sqrt ht0.le
      nlinarith [sq_nonneg (Real.sqrt t - 1), Real.sqrt_nonneg t]

omit [Prec_gt_0 p] in
/-- the start of SQRT^DD: with `v` within `η_1` of `√(a_0 + a_1)` and `(r_0 + r_1)v` within `η_2` of 1, relatively,
`r = r_0 + r_1` is within `E_0` of `y = a^{-1/2}`, relatively, and `|r_1| ≤ u|r_0|` gives `π^{(0)}` -/
theorem sqrt_dd_start (hp : 7 ≤ p) {ρ a0 a1 A v r0 r1 : ℝ} (hρ : 2 * ρ < 1) (ha0 : 0 < a0)
    (ha1 : |a1| ≤ ρ * a0) (hA : |A - (a0 + a1)| ≤ a0 * (ρ ^ 2 / (1 - ρ)))
    (hv : |v - Real.sqrt (a0 + a1)| ≤ ddEta1 p * Real.sqrt (a0 + a1)) (hrv : |(r0 + r1) * v - 1| ≤ ddEta2 p)
    (hr01 : |r1| ≤ u p * |r0|) :
    0 < A ∧ |(r0 + r1) - (Real.sqrt A)⁻¹| ≤ ddE0 p ρ * (Real.sqrt A)⁻¹ ∧
      |r0| ≤ (Real.sqrt A)⁻¹ * ((1 + ddE0 p ρ) / (1 - u p)) ∧
      |r1| ≤ (Real.sqrt A)⁻¹ * (u p * (1 + ddE0 p ρ) / (1 - u p)) := by
  have hu := u_pos p
  have hu7 : u p ≤ 1 / 128 := by
    unfold u
    calc (2 : ℝ) ^ (-p) ≤ (2 : ℝ) ^ (-7 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 / 128 := by norm_num
  have hη1 : ddEta1 p < 1 := by unfold ddEta1; nlinarith
  have hη2 : ddEta2 p < 1 := by unfold ddEta2; nlinarith [pow_pos hu 3]
  have hη10 : 0 ≤ ddEta1 p := by unfold ddEta1; positivity
  have hη20 : 0 ≤ ddEta2 p := by unfold ddEta2; positivity
  have h1ρ : 0 < 1 - ρ := by linarith
  set B := a0 + a1 with hB
  have hB0 : (1 - ρ) * a0 ≤ B := by rw [hB]; linarith [(abs_le.mp ha1).1]
  have hBpos : 0 < B := lt_of_lt_of_le (mul_pos h1ρ ha0) hB0
  set η3 := ddEta3 ρ with hη3
  have hη3l : η3 < 1 := by
    rw [hη3, ddEta3, div_lt_one (by positivity)]
    nlinarith
  have hη30 : 0 ≤ η3 := by rw [hη3, ddEta3]; positivity
  -- `a = B(1 + d_3)` with `|d_3| ≤ η_3`
  set t := A / B with ht
  have htη : |t - 1| ≤ η3 := by
    rw [ht, show A / B - 1 = (A - B) / B by field_simp, abs_div, abs_of_pos hBpos, div_le_iff₀ hBpos]
    calc |A - B| ≤ a0 * (ρ ^ 2 / (1 - ρ)) := hA
      _ ≤ B / (1 - ρ) * (ρ ^ 2 / (1 - ρ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [le_div_iff₀ h1ρ]; linarith
      _ = η3 * B := by rw [hη3, ddEta3]; field_simp
  have hA0 : 0 < A := by
    have h1 : 1 - η3 ≤ t := by linarith [(abs_le.mp htη).1]
    have h2 : (1 - η3) * B ≤ A := by rw [ht, le_div_iff₀ hBpos] at h1; exact h1
    have : 0 < (1 - η3) * B := mul_pos (by linarith) hBpos
    linarith
  obtain ⟨hst1, hst2⟩ := sqrt_near_one htη
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBpos
  have hsA : Real.sqrt A = Real.sqrt B * Real.sqrt t := by
    rw [← Real.sqrt_mul hBpos.le, ht, mul_div_cancel₀ _ hBpos.ne']
  -- `v` and `r = r_0 + r_1`
  set R := r0 + r1 with hR
  have hvlo : (1 - ddEta1 p) * Real.sqrt B ≤ v := by linarith [(abs_le.mp hv).1]
  have hvhi : v ≤ (1 + ddEta1 p) * Real.sqrt B := by linarith [(abs_le.mp hv).2]
  have hvpos : 0 < v := lt_of_lt_of_le (mul_pos (by linarith) hsB) hvlo
  have hRvlo : 1 - ddEta2 p ≤ R * v := by linarith [(abs_le.mp hrv).1]
  have hRvhi : R * v ≤ 1 + ddEta2 p := by linarith [(abs_le.mp hrv).2]
  have hRpos : 0 < R := by
    by_contra hc
    push Not at hc
    have : R * v ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hvpos.le
    linarith
  have hst0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  -- `r√a` between `(1 - η_2)(1 - η_3)/(1 + η_1)` and `(1 + η_2)(1 + η_3/2)/(1 - η_1)`
  have hup : R * Real.sqrt A ≤ (1 + η3 / 2) * (1 + ddEta2 p) / (1 - ddEta1 p) := by
    rw [hsA, le_div_iff₀ (by linarith)]
    have h1 : R * (Real.sqrt B * Real.sqrt t) * (1 - ddEta1 p) ≤ R * v * Real.sqrt t := by
      calc R * (Real.sqrt B * Real.sqrt t) * (1 - ddEta1 p) = R * Real.sqrt t * ((1 - ddEta1 p) * Real.sqrt B) := by
            ring
        _ ≤ R * Real.sqrt t * v := mul_le_mul_of_nonneg_left hvlo (mul_nonneg hRpos.le hst0)
        _ = R * v * Real.sqrt t := by ring
    have h2 : R * v * Real.sqrt t ≤ (1 + ddEta2 p) * (1 + η3 / 2) :=
      mul_le_mul hRvhi hst2 hst0 (by linarith)
    exact h1.trans (h2.trans (le_of_eq (by ring)))
  have hlo : (1 - η3) * (1 - ddEta2 p) / (1 + ddEta1 p) ≤ R * Real.sqrt A := by
    rw [hsA, div_le_iff₀ (by linarith)]
    have h1 : R * v * Real.sqrt t ≤ R * (Real.sqrt B * Real.sqrt t) * (1 + ddEta1 p) := by
      calc R * v * Real.sqrt t = R * Real.sqrt t * v := by ring
        _ ≤ R * Real.sqrt t * ((1 + ddEta1 p) * Real.sqrt B) :=
            mul_le_mul_of_nonneg_left hvhi (mul_nonneg hRpos.le hst0)
        _ = R * (Real.sqrt B * Real.sqrt t) * (1 + ddEta1 p) := by ring
    have h2 : (1 - η3) * (1 - ddEta2 p) ≤ R * v * Real.sqrt t := by
      rcases le_total (1 - η3) 0 with h | h
      · have h3 : (1 - η3) * (1 - ddEta2 p) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by linarith)
        have h4 : 0 ≤ R * v * Real.sqrt t := mul_nonneg (mul_nonneg hRpos.le hvpos.le) hst0
        linarith
      · calc (1 - η3) * (1 - ddEta2 p) ≤ Real.sqrt t * (R * v) :=
            mul_le_mul hst1 hRvlo (by linarith) hst0
          _ = R * v * Real.sqrt t := by ring
    linarith
  set y := (Real.sqrt A)⁻¹ with hy
  have hsA0 : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA0
  have hy0 : 0 < y := inv_pos.mpr hsA0
  have hRy : |R - y| ≤ ddE0 p ρ * y := by
    have hsplit : R - y = y * (R * Real.sqrt A - 1) := by rw [hy]; field_simp
    rw [hsplit, abs_mul, abs_of_pos hy0, mul_comm]
    refine mul_le_mul_of_nonneg_right (abs_le.mpr ⟨?_, ?_⟩) hy0.le
    · have := le_max_right ((1 + η3 / 2) * (1 + ddEta2 p) / (1 - ddEta1 p) - 1)
        (1 - (1 - η3) * (1 - ddEta2 p) / (1 + ddEta1 p))
      unfold ddE0
      linarith
    · have := le_max_left ((1 + η3 / 2) * (1 + ddEta2 p) / (1 - ddEta1 p) - 1)
        (1 - (1 - η3) * (1 - ddEta2 p) / (1 + ddEta1 p))
      unfold ddE0
      linarith
  have hRb : |R| ≤ (1 + ddE0 p ρ) * y := by
    have := abs_sub_abs_le_abs_sub R y
    rw [abs_of_pos hy0] at this
    linarith
  have h1u : 0 < 1 - u p := by linarith
  have hr0 : |r0| ≤ y * ((1 + ddE0 p ρ) / (1 - u p)) := by
    have : (1 - u p) * |r0| ≤ |R| := by
      have := abs_sub_abs_le_abs_sub r0 (-r1)
      rw [sub_neg_eq_add, abs_neg] at this
      linarith
    rw [mul_div_assoc', le_div_iff₀ h1u]
    linarith
  refine ⟨hA0, hRy, hr0, ?_⟩
  calc |r1| ≤ u p * |r0| := hr01
    _ ≤ u p * (y * ((1 + ddE0 p ρ) / (1 - u p))) := mul_le_mul_of_nonneg_left hr0 hu.le
    _ = y * (u p * (1 + ddE0 p ρ) / (1 - u p)) := by ring

/-- Theorem 22: SQRT^DD_n of `x` on `H(θ)` with `0 ≤ θ`, `2θu < 1`, `x_0 > 0`, `(n² + n)u < 1`, `n ≥ 2` and `p ≥ 7`,
from a double-word start within the published bounds, is within `δ^DD√x` of `√x` -/
theorem thm22 (hp : 7 ≤ p) (hn : 2 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {θ : ℝ} (hθ : 0 ≤ θ)
    (hρ : 2 * (θ * u p) < 1) (x : ℕ → ℝ) (hx : ∀ i < n, F p (x i)) (hH : Htheta p n θ x) (hx0 : 0 < x 0)
    (v r0 r1 : ℝ) (hr0 : F p r0) (hr1 : F p r1)
    (hv : |v - Real.sqrt (sqrtA p x 0 + sqrtA p x 1)| ≤ ddEta1 p * Real.sqrt (sqrtA p x 0 + sqrtA p x 1))
    (hrv : |(r0 + r1) * v - 1| ≤ ddEta2 p) (hr01 : |r1| ≤ u p * |r0|) :
    |Real.sqrt (∑ i ∈ range n, x i) - (sqrtDDOp p n x r0 r1).sum| ≤
      ddDelta p n (θ * u p) * Real.sqrt (∑ i ∈ range n, x i) := by
  have hu := u_pos p
  have hp1 : 1 < p := by omega
  have hn1 : 1 ≤ n := by omega
  obtain ⟨haF, ha0, haH, -, -, hA, hab, hhF, -⟩ := sqrt_setup p n hn1 hθ hρ x hx hH hx0
  set ρ := θ * u p with hρd
  have hρ0 : 0 ≤ ρ := mul_nonneg hθ hu.le
  have h1ρ : 0 < 1 - ρ := by linarith
  have h12 : 0 < 1 - 2 * ρ := by linarith
  set a := sqrtA p x with ha
  set A := ∑ i ∈ range n, a i with hAd
  -- `|a - (a_0 + a_1)| ≤ a_0ρ²/(1 - ρ)`
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hAs : A = a 0 + a 1 + ∑ i ∈ range k, a (i + 2) := by
    rw [hAd, sum_range_succ', sum_range_succ']
    ring
  have htail : |A - (a 0 + a 1)| ≤ a 0 * (ρ ^ 2 / (1 - ρ)) := by
    rw [hAs, add_sub_cancel_left]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ range k, |a (i + 2)| ≤ ∑ i ∈ range k, a 0 * ρ ^ 2 * ρ ^ i :=
          sum_le_sum fun i hi => by
            have := haH (i + 2) (by simp at hi; omega)
            calc |a (i + 2)| ≤ ρ ^ (i + 2) * a 0 := this
              _ = a 0 * ρ ^ 2 * ρ ^ i := by ring
      _ = a 0 * ρ ^ 2 * ∑ i ∈ range k, ρ ^ i := by rw [mul_sum]
      _ ≤ a 0 * ρ ^ 2 * (1 / (1 - ρ)) :=
          mul_le_mul_of_nonneg_left (geom_le ρ hρ0 (by linarith) k) (by positivity)
      _ = a 0 * (ρ ^ 2 / (1 - ρ)) := by ring
  have ha1 : |a 1| ≤ ρ * a 0 := by simpa using haH 1 (by omega)
  obtain ⟨-, hst, hr0b, hr1b⟩ := sqrt_dd_start p hp (by linarith) ha0 ha1 htail hv hrv hr01
  set y := (Real.sqrt A)⁻¹ with hy
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hy0 : 0 < y := inv_pos.mpr hsA
  have hAy : A * y ^ 2 = 1 := by
    rw [hy, inv_pow, Real.sq_sqrt hA.le]
    field_simp
  set h : ℕ → ℝ := fun i => a i / 2 with hh
  have hhb : ∀ i < k + 2, |h i| ≤ A * (abar ρ i / 2) := fun i hi => by
    simp only [hh, abs_div, abs_two]
    have := hab i hi
    linarith
  have hhb0 : ∀ i, 0 ≤ abar ρ i / 2 := fun i => by
    rw [abar]; exact div_nonneg (mul_nonneg (pow_nonneg hρ0 i) (div_nonneg h1ρ.le h12.le)) zero_le_two
  have hHs : ∑ i ∈ range (k + 2), h i = A / 2 := by rw [hh, ← sum_div]
  -- the start `(r_0, r_1, 0, …, 0)`
  set rd : ℕ → ℝ := fun i => if i = 0 then r0 else if i = 1 then r1 else 0 with hrd
  have hrdF : ∀ i < k + 2, F p (rd i) := fun i _ => by
    simp only [hrd]; split_ifs
    · exact hr0
    · exact hr1
    · exact F_zero p
  have hrdsum : ∑ i ∈ range (k + 2), rd i = r0 + r1 := by
    rw [sum_range_succ', sum_range_succ', sum_eq_zero fun i _ => by simp [hrd]]
    simp [hrd]
    ring
  have hE0 : 0 ≤ ddE0 p ρ := by
    have hst0 := (abs_nonneg _).trans hst
    exact nonneg_of_mul_nonneg_left hst0 hy0
  have h1u : 0 < 1 - u p := by linarith [u_le_half p hp1]
  have hπ0 : ∀ i, 0 ≤ ddPi0 p ρ i := fun i => by
    unfold ddPi0
    split_ifs
    · exact div_nonneg (by linarith) h1u.le
    · exact div_nonneg (mul_nonneg hu.le (by linarith)) h1u.le
    · exact le_rfl
  have hrdπ : ∀ i < k + 2, |rd i| ≤ y * ddPi0 p ρ i := fun i _ => by
    simp only [hrd, ddPi0]
    split_ifs
    · exact hr0b
    · exact hr1b
    · simp
  -- the second-order step, one Newton step, and the end
  obtain ⟨s1, s2, s3, s4, s5⟩ := sqrt_step2 p (k + 2) hp1 hn1 hA3 hy0 hAy h _ hhF hhb hhb0 hHs rd _ _ hE0 hπ0 hrdF
    hrdπ (by rw [hrdsum]; exact hst)
  obtain ⟨t1, t2, t3, -, -⟩ := sqrt_step p (k + 2) hp1 hn1 hA3 hy0 hAy h _ hhF hhb hhb0 hHs _ _ _ s4 s5 s1 s2 s3
  exact sqrt_final p (k + 2) hp1 hn1 hA3 hθ hρ x hx hH hx0 _ _ _ t1 t2 t3

end ExpansionBounds
