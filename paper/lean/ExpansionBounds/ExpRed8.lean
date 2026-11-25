import ExpansionBounds.Kappa8
import ExpansionBounds.LnB
import ExpansionBounds.SqrtEval
import ExpansionBounds.GMono
import ExpansionBounds.RoundEval

/-!
# Lemma 38 at `n = 8` and `p = 53`, with multidouble's constants

`c_h` is `ln 2` to 42 bits, `c_ℓ` the greedy eight parts of `ln 2 - c_h` and `c_r = RN(1/ln 2)`. The kernel checks an
enclosure of `ln 2` within `3·2^{-600}`, from 200 terms of the series of `artanh(1/3)`, which gives `η_ℓ`,
`|ln 2 - c_h|` and `|c_r - 1/ln 2|`; the bounds of Lemma 38 are then evaluated on their rational mirrors.
-/

namespace ExpansionBounds

open Finset

/-! ## `ln 2` to 600 bits -/

/-- `ln 2 = (2/3)V_∞(1/9)` after `K` terms of the series of `artanh(1/3)` -/
theorem log_two_series (K : ℕ) :
    2 / 3 * atS (1 / 9) K ≤ Real.log 2 ∧
      Real.log 2 ≤ 2 / 3 * atS (1 / 9) K + 2 / 3 * ((1 / 9) ^ K / ((2 * K + 1) * (8 / 9))) := by
  have h := log_artanh (x := 1 / 3) (by rw [abs_of_pos (by norm_num)]; norm_num)
  rw [show Real.log (1 + 1 / 3) - Real.log (1 - 1 / 3) = Real.log 2 by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num] at h
  obtain ⟨h1, h2⟩ := atS_tail (y := 1 / 9) (by norm_num) (by norm_num) K
  rw [show ((1 : ℝ) / 3) ^ 2 = 1 / 9 by norm_num] at h
  rw [show ((1 : ℝ) - 1 / 9) = 8 / 9 by norm_num] at h2
  rw [h]
  constructor <;> linarith

/-- `Σ_{k < K} y^k/(2k + 1)` over `ℚ` -/
def atSQ (y : ℚ) : ℕ → ℚ
  | 0 => 0
  | K + 1 => atSQ y K + y ^ K / (2 * K + 1)

theorem cast_atSQ (y : ℚ) (K : ℕ) : ((atSQ y K : ℚ) : ℝ) = atS (y : ℝ) K := by
  induction K with
  | zero => simp [atSQ, atS]
  | succ K ih =>
    have e : atS (y : ℝ) (K + 1) = atS (y : ℝ) K + (y : ℝ) ^ K / (2 * (K : ℝ) + 1) := by
      unfold atS
      rw [sum_range_succ]
    rw [e, ← ih]
    simp [atSQ]

/-- a lower bound of `ln 2` -/
def ln2A : ℚ :=
  2876225017259457803941422075936356235510355236981739542476444676843237809403636166587937224051855780383968483986161182568312219414999934030440139693377154550791842205675450932055001 / 2 ^ 600

/-- an upper bound of `ln 2` -/
def ln2B : ℚ :=
  2876225017259457803941422075936356235510355236981739542476444676843237809403636166587937224051855780383968483986161182568312219414999934030440139693377154550791842205675450932055004 / 2 ^ 600

set_option maxHeartbeats 4000000 in
theorem ln2_check : ln2A ≤ 2 / 3 * atSQ (1 / 9) 200 ∧
    2 / 3 * atSQ (1 / 9) 200 + 2 / 3 * ((1 / 9) ^ 200 / ((2 * 200 + 1) * (8 / 9))) ≤ ln2B := by
  decide +kernel

/-- `ln 2` within `3·2^{-600}` -/
theorem log_two_600 : ((ln2A : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((ln2B : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := log_two_series 200
  obtain ⟨c1, c2⟩ := ln2_check
  have c1' : ((ln2A : ℚ) : ℝ) ≤ ((2 / 3 * atSQ (1 / 9) 200 : ℚ) : ℝ) := Rat.cast_le.mpr c1
  have c2' : ((2 / 3 * atSQ (1 / 9) 200 + 2 / 3 * ((1 / 9) ^ 200 / ((2 * 200 + 1) * (8 / 9))) : ℚ) : ℝ) ≤
      ((ln2B : ℚ) : ℝ) := Rat.cast_le.mpr c2
  have hS : ((atSQ (1 / 9) 200 : ℚ) : ℝ) = atS (1 / 9) 200 := by
    rw [cast_atSQ]
    norm_num
  rw [Rat.cast_mul, hS] at c1'
  rw [Rat.cast_add, Rat.cast_mul, hS] at c2'
  push_cast at c1' c2' h1 h2
  constructor <;> linarith

/-! ## multidouble's constants -/

/-- `c_h`, `ln 2` to 42 bits -/
def ch8 : ℚ := 3048493539143 / 2 ^ 42

/-- `c_ℓ`, the greedy eight parts of `ln 2 - c_h` -/
def cl8 (i : ℕ) : ℚ :=
  [544487923021427 / 2 ^ 93, 8892529970223641 / 2 ^ 155, 1814850077297165 / 2 ^ 208, 821822486431101 / 2 ^ 261,
    -2517039583496813 / 2 ^ 317, 6022389164064391 / 2 ^ 374, -8411651207940057 / 2 ^ 429,
    4681804994679945 / 2 ^ 487].getD i 0

/-- `c_r = RN(1/ln 2)`, binary64's `LOG2_E` -/
def cr8 : ℚ := 3248660424278399 / 2 ^ 51

variable (p : ℤ) [Prec_gt_0 p]

omit [Prec_gt_0 p] in
/-- `c_h` is a multiple of `2^{-p-1}` -/
theorem ch8_mult (hp : p = 53) : Mult (-p - 1) ((ch8 : ℚ) : ℝ) := by
  subst hp
  refine ⟨3048493539143 * 2 ^ 12, ?_⟩
  simp only [ch8]
  push_cast
  norm_num

/-- the parts of `c_ℓ` are in `F` -/
theorem cl8_F (hp : p = 53) (i : ℕ) : F p ((cl8 i : ℚ) : ℝ) := by
  subst hp
  rw [F_iff_rn]
  rcases Nat.lt_or_ge i 8 with h | h
  · interval_cases i <;> decide +kernel
  · have h0 : cl8 i = 0 := by
      unfold cl8
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h)]
      rfl
    rw [h0]
    decide +kernel

/-- `c_r` is the float `RN(1/ln 2)` -/
theorem cR_eq (hp : p = 53) : cR p = ((cr8 : ℚ) : ℝ) := by
  have hF : F p ((cr8 : ℚ) : ℝ) := by
    subst hp
    rw [F_iff_rn]
    decide +kernel
  obtain ⟨l1, l2⟩ := log_two_dec
  have hc : ((cr8 : ℚ) : ℝ) = 3248660424278399 / 2 ^ 51 := by simp [cr8]
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log 2 := ⟨_, rfl⟩
  rw [← hL] at l1 l2
  have hL0 : 0 < L := by linarith
  unfold cR
  rw [← hL]
  refine RN_eq_of_near p (E := -52) hF ?_ ?_ ?_
  · rw [hp, hc]
    norm_num
  · rw [hp, le_div_iff₀ hL0]
    norm_num
    linarith
  · rw [hc, abs_lt]
    constructor
    · rw [lt_sub_iff_add_lt, lt_div_iff₀ hL0]
      have h : (-((2 : ℝ) ^ (-52 : ℤ) / 2) + 3248660424278399 / 2 ^ 51) * L ≤
          (-((2 : ℝ) ^ (-52 : ℤ) / 2) + 3248660424278399 / 2 ^ 51) * (69314718055994530941724 / 10 ^ 23) :=
        mul_le_mul_of_nonneg_left l2 (by norm_num)
      refine h.trans_lt ?_
      norm_num
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hL0]
      have h : ((2 : ℝ) ^ (-52 : ℤ) / 2 + 3248660424278399 / 2 ^ 51) * (69314718055994530941721 / 10 ^ 23) ≤
          ((2 : ℝ) ^ (-52 : ℤ) / 2 + 3248660424278399 / 2 ^ 51) * L :=
        mul_le_mul_of_nonneg_left l1 (by norm_num)
      refine lt_of_lt_of_le ?_ h
      norm_num

/-! ## The bounds on their rational mirrors -/

/-- `u = 2^{-53}` -/
def red8U : ℚ := 1 / 9007199254740992

/-- `X = 745.2` -/
def red8X : ℚ := 7452 / 10

/-- `x̄_t = ρX/(1 - ρ)` with `ρ = 2u` -/
def red8Xt : ℚ := 2 * red8U / (1 - 2 * red8U) * red8X

/-- a bound of `|c_r - 1/ln 2|` -/
def red8Dl : ℚ := max |cr8 - 1 / ln2B| |cr8 - 1 / ln2A|

/-- a bound of `ε_k = X(|c_r - 1/ln 2| + u c_r)` -/
def red8EpsK : ℚ := red8X * (red8Dl + red8U * cr8)

/-- a bound of `r̄_max = (1/2 + ε_k) ln 2 + x̄_t` -/
def red8RMax : ℚ := (1 / 2 + red8EpsK) * ln2B + red8Xt

/-- a bound of `α_0 = r̄_max + x̄_t + k̄|ln 2 - c_h|` -/
def red8A0 : ℚ := red8RMax + red8Xt + 1075 * max |ch8 - ln2A| |ch8 - ln2B|

/-- a bound of `η_ℓ = |ln 2 - c_h - ∑ c_ℓ|` -/
def red8Eta : ℚ :=
  max |ch8 + ∑ i ∈ range 8, cl8 i - ln2A| |ch8 + ∑ i ∈ range 8, cl8 i - ln2B|

/-- `G_MULF(α, β_0; Z̄)`'s error bound over `ℚ` -/
def GmulfEQ (uq : ℚ) (n : ℕ) (α : ℕ → ℚ) (β0 Zb : ℚ) : ℚ :=
  gErrQ uq n (pairXQ uq n fun m => α m * β0) Zb (pairRQ uq n fun m => α m * β0)

/-- `G_MULF(α, β_0; Z̄)`'s part bounds over `ℚ` -/
def GmulfPQ (uq : ℚ) (n : ℕ) (α : ℕ → ℚ) (β0 Zb : ℚ) : ℕ → ℚ :=
  gPartsQ uq n (pairXQ uq n fun m => α m * β0) Zb (pairRQ uq n fun m => α m * β0)

/-- `ε_1` of `(ε_1, μ) = G_MULF(|c_ℓ|, k̄; k̄|c_ℓ|)` -/
def red8E1 : ℚ := GmulfEQ red8U 8 (fun i => |cl8 i|) 1075 (1075 * |∑ i ∈ range 8, cl8 i|)

/-- `μ` -/
def red8Mu : ℕ → ℚ := GmulfPQ red8U 8 (fun i => |cl8 i|) 1075 (1075 * |∑ i ∈ range 8, cl8 i|)

/-- `α`: the bound of `α_0`, then `ρ^i X` -/
def red8Alpha (i : ℕ) : ℚ := if i = 0 then red8A0 else (2 * red8U) ^ i * red8X

/-- `Z̄ = r̄ + k̄η_ℓ + ε_1` -/
def red8Z (rb : ℚ) : ℚ := rb + 1075 * red8Eta + red8E1

/-- `δ = ε_1 + ε_2 + k̄η_ℓ` with `(ε_2, π^r) = G_ADD(α, μ; Z̄)` -/
def red8Delta (rb : ℚ) : ℚ := red8E1 + GaddEQ red8U 8 red8Alpha red8Mu (red8Z rb) + 1075 * red8Eta

/-- `π^r` -/
def red8Pi (rb : ℚ) : ℕ → ℚ := GaddPQ red8U 8 red8Alpha red8Mu (red8Z rb)

omit [Prec_gt_0 p] in
theorem cast_GmulfE (n : ℕ) {uq : ℚ} (h : (uq : ℝ) = u p) (α : ℕ → ℚ) (β0 Zb : ℚ) :
    ((GmulfEQ uq n α β0 Zb : ℚ) : ℝ) = GmulfE p n (fun i => (α i : ℝ)) β0 Zb := by
  have hX : (fun m => ((pairXQ uq n (fun m => α m * β0) m : ℚ) : ℝ)) =
      pairX p n fun m => (α m : ℝ) * (β0 : ℝ) := by
    funext m
    rw [cast_pairX p n h]
    simp
  have hR : ((pairRQ uq n (fun m => α m * β0) : ℚ) : ℝ) = pairR p n fun m => (α m : ℝ) * (β0 : ℝ) := by
    rw [cast_pairR p n h]
    simp
  simp only [GmulfEQ, GmulfE, cast_gErr p n h, hX, hR]

omit [Prec_gt_0 p] in
theorem cast_GmulfP (n : ℕ) {uq : ℚ} (h : (uq : ℝ) = u p) (α : ℕ → ℚ) (β0 Zb : ℚ) (i : ℕ) :
    ((GmulfPQ uq n α β0 Zb i : ℚ) : ℝ) = GmulfP p n (fun i => (α i : ℝ)) β0 Zb i := by
  have hX : (fun m => ((pairXQ uq n (fun m => α m * β0) m : ℚ) : ℝ)) =
      pairX p n fun m => (α m : ℝ) * (β0 : ℝ) := by
    funext m
    rw [cast_pairX p n h]
    simp
  have hR : ((pairRQ uq n (fun m => α m * β0) : ℚ) : ℝ) = pairR p n fun m => (α m : ℝ) * (β0 : ℝ) := by
    rw [cast_pairR p n h]
    simp
  simp only [GmulfPQ, GmulfP, cast_gParts p n h, hX, hR]

omit [Prec_gt_0 p] in
/-- `|c - t| ≤ max(|c - lo|, |c - hi|)` for `t` in `[lo, hi]` -/
theorem abs_sub_le_max {c t lo hi : ℝ} (h1 : lo ≤ t) (h2 : t ≤ hi) : |c - t| ≤ max |c - lo| |c - hi| := by
  rw [abs_le]
  constructor
  · have a := neg_abs_le (c - hi)
    have b := le_max_right |c - lo| |c - hi|
    linarith
  · have a := le_abs_self (c - lo)
    have b := le_max_left |c - lo| |c - hi|
    linarith

set_option maxHeartbeats 4000000 in
theorem red8_check : 0 < ln2A ∧ red8A0 < 1 / 2 ∧ red8X ≤ 7453 / 10 ∧ 0 ≤ red8EpsK := by decide +kernel

/-- Lemma 38 (`lem:expred`) at `n = 8` and `p = 53` with multidouble's constants, for `x` on `H(2)` with
`|x_0| ≤ 745.2`: `|k| ≤ 1075` and `|r_e| ≤ r̄_max`, and for `k ≠ 0`, `x_0 - k c_h ∈ F`, and for any `r̄ ≥ |r_e|`,
`|r - r_e| ≤ δ` and `|r_i| ≤ π^r_i` with `δ` and `π^r` at `r̄` -/
theorem lemma38_8 (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x)
    (hx0 : |x 0| ≤ 7452 / 10) :
    |expK p (x 0)| ≤ 1075 ∧
      |∑ i ∈ range 8, x i - expK p (x 0) * Real.log 2| ≤ ((red8RMax : ℚ) : ℝ) ∧
      (expK p (x 0) ≠ 0 → F p (x 0 - expK p (x 0) * ((ch8 : ℚ) : ℝ)) ∧
        ∀ rb : ℚ, |∑ i ∈ range 8, x i - expK p (x 0) * Real.log 2| ≤ ((rb : ℚ) : ℝ) →
          |∑ i ∈ range 8, expR p 8 x ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) i -
              (∑ i ∈ range 8, x i - expK p (x 0) * Real.log 2)| ≤ ((red8Delta rb : ℚ) : ℝ) ∧
          ∀ i, |expR p 8 x ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) i| ≤ ((red8Pi rb i : ℚ) : ℝ)) := by
  have hu : ((red8U : ℚ) : ℝ) = u p := by unfold red8U; exact u_53_rat p hp
  have hu53 : u p = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hup := u_pos p
  have hp14 : 14 ≤ p := by omega
  have hA3 : (((8 : ℕ) : ℝ) ^ 2 + (8 : ℕ)) * u p < 1 := by rw [hu53]; norm_num
  obtain ⟨lA, lB⟩ := log_two_600
  obtain ⟨kA, kA0, kX, kE⟩ := red8_check
  have hApos : (0 : ℝ) < ((ln2A : ℚ) : ℝ) := by exact_mod_cast kA
  have hL0 : 0 < Real.log 2 := lt_of_lt_of_le hApos lA
  -- the constants' distances from `ln 2` and `1/ln 2`
  have hinv1 : 1 / ((ln2B : ℚ) : ℝ) ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hL0 lB
  have hinv2 : 1 / Real.log 2 ≤ 1 / ((ln2A : ℚ) : ℝ) := one_div_le_one_div_of_le hApos lA
  have hDl : |cR p - 1 / Real.log 2| ≤ ((red8Dl : ℚ) : ℝ) := by
    rw [cR_eq p hp]
    have h := abs_sub_le_max (c := ((cr8 : ℚ) : ℝ)) hinv1 hinv2
    simpa [red8Dl] using h
  have hXnn : (0 : ℝ) ≤ ((red8X : ℚ) : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have hEps : epsK p ((red8X : ℚ) : ℝ) ≤ ((red8EpsK : ℚ) : ℝ) := by
    unfold epsK
    rw [show ((red8EpsK : ℚ) : ℝ) = (red8X : ℝ) * ((red8Dl : ℝ) + u p * cR p) by
      rw [cR_eq p hp, ← hu]; simp [red8EpsK]]
    exact mul_le_mul_of_nonneg_left (by linarith) hXnn
  have hRM : rMax p ((red8X : ℚ) : ℝ) ((red8Xt : ℚ) : ℝ) ≤ ((red8RMax : ℚ) : ℝ) := by
    unfold rMax
    rw [show ((red8RMax : ℚ) : ℝ) = (1 / 2 + (red8EpsK : ℝ)) * (ln2B : ℝ) + (red8Xt : ℝ) by simp [red8RMax]]
    have hE0 : (0 : ℝ) ≤ 1 / 2 + ((red8EpsK : ℚ) : ℝ) := by
      have : (0 : ℝ) ≤ ((red8EpsK : ℚ) : ℝ) := Rat.cast_nonneg.mpr kE
      linarith
    linarith [mul_le_mul (add_le_add (le_refl (1 / 2 : ℝ)) hEps) lB hL0.le hE0]
  have hDe : |Real.log 2 - ((ch8 : ℚ) : ℝ)| ≤ ((max |ch8 - ln2A| |ch8 - ln2B| : ℚ) : ℝ) := by
    rw [abs_sub_comm]
    have h := abs_sub_le_max (c := ((ch8 : ℚ) : ℝ)) lA lB
    simpa using h
  have hA0 : expA0 p ((red8X : ℚ) : ℝ) ((red8Xt : ℚ) : ℝ) ((ch8 : ℚ) : ℝ) ≤ ((red8A0 : ℚ) : ℝ) := by
    unfold expA0
    rw [show ((red8A0 : ℚ) : ℝ) = (red8RMax : ℝ) + (red8Xt : ℝ) +
      1075 * ((max |ch8 - ln2A| |ch8 - ln2B| : ℚ) : ℝ) by simp [red8A0]]
    linarith
  have hEta : etaL 8 ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) ≤ ((red8Eta : ℚ) : ℝ) := by
    unfold etaL
    rw [show Real.log 2 - ((ch8 : ℚ) : ℝ) - ∑ i ∈ range 8, ((cl8 i : ℚ) : ℝ) =
      -((((ch8 : ℚ) : ℝ) + ∑ i ∈ range 8, ((cl8 i : ℚ) : ℝ)) - Real.log 2) by ring, abs_neg]
    have h := abs_sub_le_max (c := ((ch8 : ℚ) : ℝ) + ∑ i ∈ range 8, ((cl8 i : ℚ) : ℝ)) lA lB
    simpa [red8Eta] using h
  -- part (a)
  have hXe : ((red8X : ℚ) : ℝ) = 7452 / 10 := by simp [red8X]
  have hX0 : |x 0| ≤ ((red8X : ℚ) : ℝ) := by rw [hXe]; exact hx0
  have hX1 : ((red8X : ℚ) : ℝ) ≤ 745.3 := by rw [hXe]; norm_num
  have hρ : (2 : ℝ) * u p < 1 := by rw [hu53]; norm_num
  have hxt : |∑ i ∈ range 8, x i - x 0| ≤ ((red8Xt : ℚ) : ℝ) := by
    have h := Htheta_tail p 8 (by norm_num) 2 (by norm_num) hρ x hH
    rw [show ((red8Xt : ℚ) : ℝ) = 2 * u p / (1 - 2 * u p) * (red8X : ℝ) by rw [← hu]; simp [red8Xt]]
    exact h.trans (mul_le_mul_of_nonneg_left hX0 (div_nonneg (by positivity) (by linarith)))
  have hA0lt : expA0 p ((red8X : ℚ) : ℝ) ((red8Xt : ℚ) : ℝ) ((ch8 : ℚ) : ℝ) < 1 / 2 :=
    hA0.trans_lt (lt_of_lt_of_eq (Rat.cast_lt.mpr kA0) (by norm_num))
  obtain ⟨a1, a2, -, a4⟩ := lemma_expred_a p 8 hp14 x (hx 0 (by norm_num)) _ _ _ hX0 hX1 hxt (ch8_mult p hp) hA0lt
  refine ⟨a1, a2.trans hRM, fun hk => ⟨a4 hk, fun rb hrb => ?_⟩⟩
  -- part (b)
  set cl : ℕ → ℝ := fun i => ((cl8 i : ℚ) : ℝ) with hcl
  set α : ℕ → ℝ := fun i => ((red8Alpha i : ℚ) : ℝ) with hα
  have hα0 : expA0 p ((red8X : ℚ) : ℝ) ((red8Xt : ℚ) : ℝ) ((ch8 : ℚ) : ℝ) ≤ α 0 := by
    show _ ≤ ((red8Alpha 0 : ℚ) : ℝ)
    simpa [red8Alpha] using hA0
  have hαi : ∀ i, 1 ≤ i → i < 8 → |x i| ≤ α i := by
    intro i h1 h8
    have h := Htheta_le p 8 hH i h8
    show _ ≤ ((red8Alpha i : ℚ) : ℝ)
    rw [show ((red8Alpha i : ℚ) : ℝ) = (2 * u p) ^ i * (red8X : ℝ) by
      rw [← hu]; simp [red8Alpha, show i ≠ 0 by omega]]
    exact h.trans (mul_le_mul_of_nonneg_left hX0 (by positivity))
  obtain ⟨b1, b2⟩ := lemma_expred_b p 8 hp14 (by norm_num) hA3 x hx _ _ _ cl α hX0 hX1 hxt (ch8_mult p hp)
    (fun i _ => cl8_F p hp i) hA0lt hα0 hαi hk _ hrb
  -- the bounds are their mirrors' values
  have hcabs : (fun i => ((|cl8 i| : ℚ) : ℝ)) = fun i => |cl i| := by
    funext i
    simp [hcl]
  have hZc : ((1075 * |∑ i ∈ range 8, cl8 i| : ℚ) : ℝ) = 1075 * |∑ i ∈ range 8, cl i| := by simp [hcl]
  have hE1 : redE1 p 8 cl = ((red8E1 : ℚ) : ℝ) := by
    unfold redE1 red8E1
    rw [cast_GmulfE p 8 hu, hcabs, hZc]
    simp
  have hMu : redMu p 8 cl = fun i => ((red8Mu i : ℚ) : ℝ) := by
    funext i
    unfold redMu red8Mu
    rw [cast_GmulfP p 8 hu, hcabs, hZc]
    simp
  have hZ : redZ p 8 ((ch8 : ℚ) : ℝ) cl ((rb : ℚ) : ℝ) ≤ ((red8Z rb : ℚ) : ℝ) := by
    unfold redZ
    rw [hE1, show ((red8Z rb : ℚ) : ℝ) = (rb : ℝ) + 1075 * (red8Eta : ℝ) + (red8E1 : ℝ) by
      simp [red8Z]]
    linarith
  obtain ⟨g1, g2⟩ := Gadd_mono p 8 hA3 (α := α) (α' := α) (β := redMu p 8 cl) (β' := redMu p 8 cl)
    (fun _ => le_rfl) (fun _ => le_rfl) hZ
  have hGE : GaddE p 8 α (redMu p 8 cl) ((red8Z rb : ℚ) : ℝ) =
      ((GaddEQ red8U 8 red8Alpha red8Mu (red8Z rb) : ℚ) : ℝ) := by
    rw [cast_GaddE p 8 hu, hMu]
  have hGP : ∀ i, GaddP p 8 α (redMu p 8 cl) ((red8Z rb : ℚ) : ℝ) i =
      ((GaddPQ red8U 8 red8Alpha red8Mu (red8Z rb) i : ℚ) : ℝ) := fun i => by
    rw [cast_GaddP p 8 hu, hMu]
  refine ⟨?_, fun i => (b2 i).trans ((g2 i).trans_eq (hGP i))⟩
  refine b1.trans ?_
  rw [show ((red8Delta rb : ℚ) : ℝ) = (red8E1 : ℝ) +
    ((GaddEQ red8U 8 red8Alpha red8Mu (red8Z rb) : ℚ) : ℝ) + 1075 * (red8Eta : ℝ) by simp [red8Delta],
    ← hGE, hE1]
  linarith

set_option maxHeartbeats 4000000 in
theorem red8_values : red8RMax ≤ 346574 / 10 ^ 6 ∧ red8Delta red8RMax ≤ 346574 / 10 ^ 6 * red8U ^ 8 ∧
    ∀ i < 8, red8Pi red8RMax i ≤ 346574 / 10 ^ 6 * red8U ^ i := by decide +kernel

/-- Lemma 38 at `n = 8` and `p = 53` in decimals: `|r_e| ≤ 0.346574`, and for `k ≠ 0`, `|r - r_e| ≤ 0.346574u^8` and
`|r_i| ≤ 0.346574u^i` -/
theorem lemma38_8_dec (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x)
    (hx0 : |x 0| ≤ 7452 / 10) :
    |expK p (x 0)| ≤ 1075 ∧ |∑ i ∈ range 8, x i - expK p (x 0) * Real.log 2| ≤ 346574 / 10 ^ 6 ∧
      (expK p (x 0) ≠ 0 → F p (x 0 - expK p (x 0) * ((ch8 : ℚ) : ℝ)) ∧
        |∑ i ∈ range 8, expR p 8 x ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) i -
            (∑ i ∈ range 8, x i - expK p (x 0) * Real.log 2)| ≤ 346574 / 10 ^ 6 * u p ^ 8 ∧
        ∀ i < 8, |expR p 8 x ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) i| ≤ 346574 / 10 ^ 6 * u p ^ i) := by
  have hu : ((red8U : ℚ) : ℝ) = u p := by unfold red8U; exact u_53_rat p hp
  obtain ⟨v1, v2, v3⟩ := red8_values
  obtain ⟨a1, a2, a3⟩ := lemma38_8 p hp x hx hH hx0
  have w1 : ((red8RMax : ℚ) : ℝ) ≤ 346574 / 10 ^ 6 :=
    (Rat.cast_le (K := ℝ).mpr v1).trans_eq (by norm_num)
  have w2 : ((red8Delta red8RMax : ℚ) : ℝ) ≤ 346574 / 10 ^ 6 * u p ^ 8 :=
    (Rat.cast_le (K := ℝ).mpr v2).trans_eq (by rw [← hu]; push_cast; ring)
  have w3 : ∀ i < 8, ((red8Pi red8RMax i : ℚ) : ℝ) ≤ 346574 / 10 ^ 6 * u p ^ i := fun i hi =>
    (Rat.cast_le (K := ℝ).mpr (v3 i hi)).trans_eq (by rw [← hu]; push_cast; ring)
  refine ⟨a1, a2.trans w1, fun hk => ?_⟩
  obtain ⟨b1, b23⟩ := a3 hk
  obtain ⟨b2, b3⟩ := b23 red8RMax a2
  exact ⟨b1, b2.trans w2, fun i hi => (b3 i).trans (w3 i hi)⟩

end ExpansionBounds
