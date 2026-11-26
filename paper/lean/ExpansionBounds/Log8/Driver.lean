import ExpansionBounds.Log8.Psi
import ExpansionBounds.Exp8

/-!
# Theorem 42 at `n = 8` and `p = 53`: from a run to its case

A run of `LOG_{8,6,43,4}` after its start `y_0`, a two-part expansion within `E(|ln x|)` of `ln x`: the reduction
of `-y_0` gives `k` and `r`, step (2)'s `U` selects the exponent `e`, and `e` with the sign and the size of `r`
selects a case of the tables of `Log8/Table.lean`. `log8_run0` (`k = 0`) and `log8_run1` (`k ≠ 0`) are `log8_k0`
and `log8_k1` for that case: they take the kernel's evaluations of the groups (`Log8Group0`, `Log8Group1`) and
its checks of the parts of `t` (`Log8GroupT0`, `Log8GroupT1`) as hypotheses, which `Log8/All.lean` and
`Log8/PsiAll.lean` prove, and the scalings' roundings in the class `Scl`; step (4)'s need be in the class only
where `∑|t_i| ≤ 1`, which the case gives. Here also: the part bounds `π^x` of the scaled `x` (`log8_pix`), and
that binary64's rule keeps a part in `[1/2, 2]` scaled in two steps (`log8_keep`).
-/

namespace ExpansionBounds

open Finset Set

/-- `π^x` for a run: for `x > 0` on `H(2)`, `y_0` within `E` of `ln x`, `r` within `δ` of `-y_0 - k ln 2`, `r` of the
sign `pos` and `a ≤ |r| ≤ b`, `2^k x ≤ ξ`, so each scaled part is within the ladder's bound for the value `ξ`, plus
the scaling's `η` -/
theorem log8_pix {Sx : ℝ → ℝ} {η : ℝ} (hSx : Scl 53 η Sx) (x : ℕ → ℝ) (hX0 : 0 < ∑ i ∈ range 8, x i)
    (hH : Htheta 53 8 2 x) (Y0 R : ℝ) (k : ℤ) {E δ a b : ℝ} (hE : |Y0 - Real.log (∑ i ∈ range 8, x i)| ≤ E)
    (hδ : |R - (-Y0 - k * Real.log 2)| ≤ δ) (ha : a ≤ |R|) (hb : |R| ≤ b) (pos : Bool)
    (hsgn : if pos then 0 ≤ R else R ≤ 0) :
    ∀ i < 8, |Sx ((2 : ℝ) ^ k * x i)| ≤ logPiX 8 (2 * u 53) η (logXi ((8 : ℕ) * η) pos E a b δ) i := by
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← u_53_rat 53 rfl]; norm_num
  have hη := Scl.nonneg 53 hSx
  have hρ : (2 : ℝ) * (2 * u 53) < 1 := by rw [hu53]; norm_num
  obtain ⟨l1, l2⟩ := Htheta_lead_pos 53 8 (by norm_num) 2 (by norm_num) hρ x hH hX0
  obtain ⟨X, hXd⟩ : ∃ X, X = ∑ i ∈ range 8, x i := ⟨_, rfl⟩
  rw [← hXd] at hX0 hE l1 l2
  have hH' := Htheta_le 53 8 hH
  obtain ⟨ρ, hρd⟩ : ∃ ρ, ρ = 2 * u (53 : ℤ) := ⟨_, rfl⟩
  rw [← hρd] at hρ l1 l2 hH' ⊢
  have hρ0 : 0 ≤ ρ := by rw [hρd, hu53]; norm_num
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < 1 - 2 * ρ := by linarith
  have hx0 : 0 < x 0 := lt_of_lt_of_le (mul_pos h1 hX0) l1
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  -- `2^k x ≤ e^{E + δ - a}` or `e^{E + b + δ}`
  obtain ⟨e1, e2⟩ := abs_le.mp hE
  obtain ⟨d1, d2⟩ := abs_le.mp hδ
  have hk : (2 : ℝ) ^ k * X = Real.exp (k * Real.log 2 + Real.log X) := by
    rw [Real.exp_add, Real.exp_log hX0, exp_int_mul_log_two]
  have hξ : (2 : ℝ) ^ k * X ≤ logXi ((8 : ℕ) * η) pos E a b δ := by
    have h8 : (0 : ℝ) ≤ (8 : ℕ) * η := by positivity
    rw [hk]
    unfold logXi
    cases pos
    · simp only [Bool.false_eq_true, ↓reduceIte] at hsgn ⊢
      rw [abs_of_nonpos hsgn] at hb
      have := Real.exp_le_exp.mpr (show k * Real.log 2 + Real.log X ≤ E + b + δ by linarith)
      linarith
    · simp only [↓reduceIte] at hsgn ⊢
      rw [abs_of_nonneg hsgn] at ha
      have := Real.exp_le_exp.mpr (show k * Real.log 2 + Real.log X ≤ E + δ - a by linarith)
      linarith
  intro i hi
  have hpart : |x i| ≤ ρ ^ i * x 0 := by
    have := hH' i hi
    rwa [abs_of_pos hx0] at this
  have hpi : (0 : ℝ) ≤ ρ ^ i := pow_nonneg hρ0 i
  have hv : |(2 : ℝ) ^ k * x i| ≤ ρ ^ i * (logXi ((8 : ℕ) * η) pos E a b δ * (1 - ρ) / (1 - 2 * ρ)) := by
    rw [abs_mul, abs_of_pos h2k]
    calc (2 : ℝ) ^ k * |x i| ≤ 2 ^ k * (ρ ^ i * x 0) := mul_le_mul_of_nonneg_left hpart h2k.le
      _ ≤ 2 ^ k * (ρ ^ i * ((1 - ρ) / (1 - 2 * ρ) * X)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left l2 hpi) h2k.le
      _ = ρ ^ i * ((2 ^ k * X) * (1 - ρ) / (1 - 2 * ρ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hξ h1.le) h2.le) hpi
  have herr := hSx.err ((2 : ℝ) ^ k * x i)
  have ht := abs_sub_abs_le_abs_sub (Sx ((2 : ℝ) ^ k * x i)) ((2 : ℝ) ^ k * x i)
  simp only [logPiX, ladderB, hi, ↓reduceIte]
  linarith

/-- A rounding `S` of binary64's rule (`hS`) keeps a value `w ≥ 1/2` scaled in two steps, the second by `2^j` with
`j ≤ 0`: neither `2^{-j}w` nor `w` is below `2^{-1022}`. In binary64 the first step must also stay finite, which the
model, with no largest value, does not express. -/
theorem log8_keep {S : ℝ → ℝ}
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    {j : ℤ} (hj : j ≤ 0) {w : ℝ} (hw : 1 / 2 ≤ w) : S ((2 : ℝ) ^ j * S ((2 : ℝ) ^ (-j) * w)) = w := by
  have hsmall : (2 : ℝ) ^ (-1022 : ℤ) ≤ 1 / 2 := by
    rw [show (1 : ℝ) / 2 = 2 ^ (-1 : ℤ) by norm_num]
    exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have keep : ∀ v : ℝ, 1 / 2 ≤ v → S v = v := fun v hv => by
    rcases hS v with h | ⟨-, h, -⟩
    · exact h
    · rw [abs_of_nonneg (by linarith)] at h
      linarith
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (-j) := one_le_zpow₀ (by norm_num) (by omega)
  have h2 : 1 / 2 ≤ (2 : ℝ) ^ (-j) * w := by nlinarith
  rw [keep _ h2, ← mul_assoc, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero, one_mul]
  exact keep w hw

/-- A two-part expansion `y` with `|y_1| ≤ u|y_0|`: its sum, the sum of its parts' magnitudes, and
`(1 - u)|y_0| ≤ |y| ≤ (1 + u)|y_0|`, for `-y` -/
theorem log8_two (y0 : ℕ → ℝ) (hy1 : |y0 1| ≤ u 53 * |y0 0|) (hy2 : ∀ i, 2 ≤ i → y0 i = 0) :
    ∑ i ∈ range 8, y0 i = y0 0 + y0 1 ∧ ∑ i ∈ range 8, |-y0 i| = |y0 0| + |y0 1| ∧
      |y0 0| * (1 - u 53) ≤ |∑ i ∈ range 8, y0 i| ∧ |∑ i ∈ range 8, y0 i| ≤ |y0 0| * (1 + u 53) ∧
      ∑ i ∈ range 8, |-y0 i| ≤ |y0 0| * (1 + u 53) := by
  have hsum : ∑ i ∈ range 8, y0 i = y0 0 + y0 1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hy2 2 le_rfl, hy2 3 (by norm_num),
      hy2 4 (by norm_num), hy2 5 (by norm_num), hy2 6 (by norm_num), hy2 7 (by norm_num)]
    ring
  have habs : ∑ i ∈ range 8, |-y0 i| = |y0 0| + |y0 1| := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hy2 2 le_rfl, hy2 3 (by norm_num),
      hy2 4 (by norm_num), hy2 5 (by norm_num), hy2 6 (by norm_num), hy2 7 (by norm_num), abs_neg, abs_zero]
    ring
  have h2 : |y0 0| - |y0 1| ≤ |y0 0 + y0 1| := by
    have := abs_sub_abs_le_abs_sub (y0 0) (-y0 1)
    rwa [abs_neg, sub_neg_eq_add] at this
  have h3 := abs_add_le (y0 0) (y0 1)
  refine ⟨hsum, habs, ?_, ?_, ?_⟩
  · rw [hsum]; linarith
  · rw [hsum]; linarith
  · rw [habs]; linarith

variable [Prec_gt_0 (53 : ℤ)]

/-- The tables of EXP's and LOG's coefficients at `n = 8`: the parts are in `F`, and `φ_k`, `φ'_k` are the
distances to `1/k!` and to `(-1)^{k+1}/k`. -/
theorem log8_tables : (∀ k, ∀ i < 8, F 53 ((exp8F k i : ℚ) : ℝ)) ∧
    (∀ k, |∑ i ∈ range 8, ((exp8F k i : ℚ) : ℝ) - invF k| ≤ ((exp8Phi k : ℚ) : ℝ)) ∧
    (∀ k, ∀ i < 8, F 53 ((log8F k i : ℚ) : ℝ)) ∧
    ∀ k, |∑ i ∈ range 8, ((log8F k i : ℚ) : ℝ) - logFe k| ≤ ((log8Phi k : ℚ) : ℝ) := by
  obtain ⟨-, tF2⟩ := exp8_table
  obtain ⟨-, tL2⟩ := log8_table
  refine ⟨fun k i _ => dyFn_getD_F 53 exp8Fact (dyF_of_all 53 exp8Fact tF2) k i, fun k => ?_,
    fun k i _ => dyFn_getD_F 53 log8Ser (dyF_of_all 53 log8Ser tL2) k i, fun k => ?_⟩
  · unfold exp8Phi invF
    push_cast
    exact le_rfl
  · unfold log8Phi logFe
    push_cast
    exact le_rfl

/-- Step (2)'s selection of `e`, the exponent of `U` or `-1023` where `U < 2^{-1022}`: `∑|r_i| < 2^{e+1}`, and
`2^e(1 - 2^{-46}) ≤ ∑|r_i|` for `e ≥ -436` -/
theorem log8_sel (r : ℕ → ℝ) (e : ℤ)
    (hsel : ((2 : ℝ) ^ e ≤ expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) r ∧
        expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) r < (2 : ℝ) ^ (e + 1)) ∨
      (expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) r < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023)) :
    ∑ i ∈ range 8, |r i| < (2 : ℝ) ^ (e + 1) ∧
      (-436 ≤ e → (2 : ℝ) ^ e ≤ expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) r ∧
        (2 : ℝ) ^ e * (1 - 1 / 2 ^ 46) ≤ ∑ i ∈ range 8, |r i|) := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hup := u_pos (53 : ℤ)
  obtain ⟨-, -, -, -, -, -, -, -, -, cγ, cC⟩ := exp8_consts
  have hγ : (1 + u (53 : ℤ)) ^ 8 ≤ 1 + (2 : ℝ) ^ (-48 : ℤ) := by
    have h1 := (Rat.cast_le (K := ℝ)).mpr cγ
    push_cast at h1
    rw [hu] at h1
    exact h1.trans_eq (by norm_num)
  have hSU : ∑ i ∈ range 8, |r i| ≤ expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) r := expU_ge 53 8 (by norm_num) _ hγ r
  refine ⟨?_, fun he => ?_⟩
  · rcases hsel with ⟨-, h2⟩ | ⟨h2, he⟩
    · exact hSU.trans_lt h2
    · rw [he]
      exact (hSU.trans_lt h2).trans_eq (by norm_num)
  · have h1 : (2 : ℝ) ^ e ≤ expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) r := by
      rcases hsel with ⟨h1, -⟩ | ⟨-, he'⟩
      · exact h1
      · omega
    refine ⟨h1, ?_⟩
    have h3 := h1.trans (expU_le 53 8 (by norm_num) ((2 : ℝ) ^ (-48 : ℤ)) (by positivity) r)
    have h4 : (1 : ℝ) - 1 / 2 ^ 46 ≤ 1 / ((1 + u 53) ^ 8 * (1 + (2 : ℝ) ^ (-48 : ℤ))) := by
      have h1 := (Rat.cast_le (K := ℝ)).mpr cC
      push_cast at h1
      rw [hu] at h1
      exact h1.trans_eq (by norm_num)
    have hc : 0 < (1 + u (53 : ℤ)) ^ 8 * (1 + (2 : ℝ) ^ (-48 : ℤ)) := by positivity
    calc (2 : ℝ) ^ e * (1 - 1 / 2 ^ 46) ≤
          (2 : ℝ) ^ e * (1 / ((1 + u 53) ^ 8 * (1 + (2 : ℝ) ^ (-48 : ℤ)))) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = (2 : ℝ) ^ e / ((1 + u 53) ^ 8 * (1 + (2 : ℝ) ^ (-48 : ℤ))) := mul_one_div _ _
      _ ≤ ∑ i ∈ range 8, |r i| := by rw [div_le_iff₀ hc, mul_comm]; exact h3

omit [Prec_gt_0 (53 : ℤ)] in
/-- The group of an exponent `e ≤ -2` for `k = 0`: one of the table for `e ≥ -436`, and the last below; `P` is
what the kernel proves of every group. -/
theorem log8_pick0 {P : Log8G0 → Prop} (hall : ∀ g ∈ log8Grp0, P g) (hlast : P log8Last0) {e : ℤ} (he2 : e ≤ -2) :
    ∃ (g : Log8G0) (last : Bool), P g ∧ Log8G0Ok last g ∧ g.m = (e + 7).toNat ∧
      g.d = exp8Deg (e - (e + 7).toNat) ∧ e ≤ g.ehi ∧ (last = false → -436 ≤ e ∧ g.elo ≤ e) := by
  obtain ⟨gOk, gCov, gLast, gL1, gL2, gL3⟩ := log8_grps0
  by_cases he : -436 ≤ e
  · obtain ⟨g, hg, hg1, hg2⟩ := gCov e he he2
    have hok := gOk g hg
    obtain ⟨o1a, o1b⟩ := hok.1 e hg1 hg2
    exact ⟨g, false, hall g hg, hok, o1a, by rw [← o1a]; exact o1b, hg2, fun _ => ⟨he, hg1⟩⟩
  · have he437 : e ≤ -437 := by omega
    have hm0 : (e + 7).toNat = 0 := by omega
    refine ⟨log8Last0, true, hlast, gLast, by rw [gL1, hm0], ?_, by rw [gL3]; exact he437, fun h => by simp at h⟩
    rw [gL2, hm0]
    simpa using (exp8Deg_small he437).symm

/-- Theorem 42 (`thm:log`) at `n = 8` for a run with `k = 0`, from the kernel's evaluations of the groups of
`k = 0`: the reduction returns `r = -y_0`, the exponent `e` of step (2) selects a group, whose numbers put `|r|`
in `[a, hi]` and `|ln x|` in `[ℓ₁, ℓ₂]`, and `log8_k0` applies with `b = ȳ(ℓ)` or the constant `hi` -/
theorem log8_run0 (hall : ∀ g ∈ log8Grp0, Log8Group0 g ∧ Log8GroupT0 g)
    (hlast : Log8Group0 log8Last0 ∧ Log8GroupT0 log8Last0) (hsh : Log8Shared)
    {S₁ S₂ Sx Sp Sc : ℝ → ℝ} (e : ℤ) (hS₁ : Scl 53 ((exp8Eta1 (e + 7).toNat : ℚ) : ℝ) S₁)
    (hS₂ : Scl 53 ((exp8Eta : ℚ) : ℝ) S₂) (hSx : Scl 53 ((2 * exp8Eta : ℚ) : ℝ) Sx)
    (hSc : Scl 53 ((exp8Eta : ℚ) : ℝ) Sc) (x : ℕ → ℝ)
    (hx : ∀ i < 8, F 53 (x i)) (hX0 : 0 < ∑ i ∈ range 8, x i) (hH : Htheta 53 8 2 x) (y0 : ℕ → ℝ)
    (hy0 : ∀ i < 8, F 53 (y0 i)) (hy1 : |y0 1| ≤ u 53 * |y0 0|) (hy2 : ∀ i, 2 ≤ i → y0 i = 0)
    (hE : |∑ i ∈ range 8, y0 i - Real.log (∑ i ∈ range 8, x i)| ≤ log8E |Real.log (∑ i ∈ range 8, x i)|)
    (hk0 : expK 53 (-y0 0) = 0) (r : ℕ → ℝ) (hrd : r = fun i => -y0 i)
    (hSp : ∑ i ∈ range 8, |expCore 53 8 S₁ S₂ e (e + 7).toNat r (fun k i => ((exp8F k i : ℚ) : ℝ))
      (exp8Deg (e - (e + 7).toNat)) i| ≤ 1 → Scl 53 ((2 * exp8Eta : ℚ) : ℝ) Sp)
    (hsel : ((2 : ℝ) ^ e ≤ expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) r ∧
        expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) r < (2 : ℝ) ^ (e + 1)) ∨
      (expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) r < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023))
    (hSx0 : 1 / 2 ≤ (2 : ℝ) ^ (0 : ℤ) * x 0 → (2 : ℝ) ^ (0 : ℤ) * x 0 ≤ 2 →
      Sx ((2 : ℝ) ^ (0 : ℤ) * x 0) = (2 : ℝ) ^ (0 : ℤ) * x 0) (eφ et ec : ℤ)
    (hUφ : ∑ i ∈ range 8, |logPhi 53 8 Sx 0 x i| < (2 : ℝ) ^ (eφ + 1))
    (hUt : ∑ i ∈ range 8, |expCore 53 8 S₁ S₂ e (e + 7).toNat r (fun k i => ((exp8F k i : ℚ) : ℝ))
      (exp8Deg (e - (e + 7).toNat)) i| < (2 : ℝ) ^ (et + 1))
    (hUc : ∑ i ∈ range 8, |logC 53 8 Sp 436 eφ et (logPhi 53 8 Sx 0 x)
      (expCore 53 8 S₁ S₂ e (e + 7).toNat r (fun k i => ((exp8F k i : ℚ) : ℝ))
        (exp8Deg (e - (e + 7).toNat))) i| < (2 : ℝ) ^ (ec + 1)) :
    |(logOp 53 8 Sx Sp Sc y0 x 0 (expCore 53 8 S₁ S₂ e (e + 7).toNat r (fun k i => ((exp8F k i : ℚ) : ℝ))
        (exp8Deg (e - (e + 7).toNat))) 436 eφ et ec (fun k i => ((log8F k i : ℚ) : ℝ)) 4).sum -
        Real.log (∑ i ∈ range 8, x i)| ≤
      9926 / 1000 * u 53 ^ 8 * |Real.log (∑ i ∈ range 8, x i)| + 1 / 2 ^ 509 := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have h1u : (0 : ℝ) ≤ 1 - u 53 := by rw [hu53]; norm_num
  have h1p : (0 : ℝ) < 1 + u 53 := by rw [hu53]; norm_num
  obtain ⟨hF, hφF, hF', hφ'⟩ := log8_tables
  obtain ⟨he0, he1, -⟩ := log8E_consts
  obtain ⟨cTop, cE1, -⟩ := log8_consts0
  obtain ⟨-, -, -, -, -, -, -, ccr, -, -, -⟩ := exp8_consts
  have hcr : (0 : ℝ) < ((cr8 : ℚ) : ℝ) := by exact_mod_cast ccr
  have he0' : (0 : ℝ) ≤ ((log8E0 : ℚ) : ℝ) := by exact_mod_cast he0
  have he1' : (0 : ℝ) ≤ ((log8E1 : ℚ) : ℝ) := by exact_mod_cast he1
  have he1'' : ((log8E1 : ℚ) : ℝ) < 1 := by exact_mod_cast cE1
  have hc46 : (0 : ℝ) ≤ (1 - 1 / 2 ^ 46) * (1 - u 53) / (1 + u 53) := by rw [hu53]; norm_num
  have e1 : ∀ t : ℝ, t * ((1 - 1 / 2 ^ 46) * (1 - u 53) / (1 + u 53)) =
      t * (1 - 1 / 2 ^ 46) * (1 - u 53) / (1 + u 53) := fun t => by ring
  obtain ⟨-, -, hlo, hhi, hA⟩ := log8_two y0 hy1 hy2
  obtain ⟨hY, -⟩ := log8_start_parts y0 hy1 hy2 hE
  have hry : ∀ i, r i = -y0 i := fun i => by rw [hrd]
  have hRY : ∑ i ∈ range 8, r i = -∑ i ∈ range 8, y0 i := by
    rw [hrd]
    simp only [Finset.sum_neg_distrib]
  have hRabs : |∑ i ∈ range 8, r i| = |∑ i ∈ range 8, y0 i| := by rw [hRY, abs_neg]
  have hAr : ∑ i ∈ range 8, |r i| = ∑ i ∈ range 8, |-y0 i| := by rw [hrd]
  have hR0 : 0 ≤ |∑ i ∈ range 8, r i| := abs_nonneg _
  -- `|y_{0,0}| < 1/(2c_r)`, so `|y_0| ≤ (1 + u)/(2c_r)`
  have hy00 : |y0 0| < 1 / (2 * ((cr8 : ℚ) : ℝ)) := by
    have h1 := abs_lt_half_of_RN 53 (roundAway_eq_zero hk0)
    rw [cR_eq 53 rfl, abs_mul, abs_neg, abs_of_pos hcr] at h1
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hRtop : |∑ i ∈ range 8, r i| ≤ ((log8Top0 : ℚ) : ℝ) := by
    rw [hRabs]
    have h1 : |y0 0| * (1 + u 53) ≤ 1 / (2 * ((cr8 : ℚ) : ℝ)) * (1 + u 53) :=
      mul_le_mul_of_nonneg_right hy00.le h1p.le
    have h2 : ((log8Top0 : ℚ) : ℝ) = 1 / (2 * ((cr8 : ℚ) : ℝ)) * (1 + u 53) := by
      unfold log8Top0
      push_cast
      rw [hu]
    rw [h2]
    linarith
  -- the exponent
  obtain ⟨hU, hsel2⟩ := log8_sel r e hsel
  have hlow : -436 ≤ e →
      (2 : ℝ) ^ e * (1 - 1 / 2 ^ 46) * (1 - u 53) / (1 + u 53) ≤ |∑ i ∈ range 8, r i| := by
    intro he
    obtain ⟨-, h1⟩ := hsel2 he
    rw [hRabs, div_le_iff₀ h1p]
    have h2 : (∑ i ∈ range 8, |r i|) * (1 - u 53) ≤ |∑ i ∈ range 8, y0 i| * (1 + u 53) := by
      rw [hAr]
      calc (∑ i ∈ range 8, |-y0 i|) * (1 - u 53) ≤ |y0 0| * (1 + u 53) * (1 - u 53) :=
            mul_le_mul_of_nonneg_right hA h1u
        _ = |y0 0| * (1 - u 53) * (1 + u 53) := by ring
        _ ≤ |∑ i ∈ range 8, y0 i| * (1 + u 53) := mul_le_mul_of_nonneg_right hlo h1p.le
    have := mul_le_mul_of_nonneg_right h1 h1u
    linarith
  have he2 : e ≤ -2 := by
    by_contra hcon
    have hl := hlow (by omega)
    have h6 : (2 : ℝ) ^ (-1 : ℤ) ≤ (2 : ℝ) ^ e := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h7 := (Rat.cast_lt (K := ℝ)).mpr cTop
    push_cast at h7
    rw [hu] at h7
    have h8 := mul_le_mul_of_nonneg_right h6 hc46
    rw [e1, e1] at h8
    linarith
  -- the group of `e`
  obtain ⟨g, last, ⟨hgG, hgT⟩, hgOk, hgm, hgd, hge, hgl⟩ := log8_pick0 hall hlast he2
  obtain ⟨-, o2, -, o4, o5, o6, o7, o8, o9, o10⟩ := hgOk
  obtain ⟨m, hm⟩ : ∃ m, m = (e + 7).toNat := ⟨_, rfl⟩
  rw [← hm] at hS₁ hSp hUt hUc hgm hgd ⊢
  obtain ⟨d', hd'⟩ : ∃ d', d' = exp8Deg (e - m) := ⟨_, rfl⟩
  rw [← hd'] at hSp hUt hUc hgd ⊢
  have ha : ((g.a : ℚ) : ℝ) ≤ |∑ i ∈ range 8, r i| := by
    cases last
    · simp only [Bool.false_eq_true, ↓reduceIte] at o4
      obtain ⟨he, hel⟩ := hgl rfl
      have h3 := (Rat.cast_le (K := ℝ)).mpr o4
      push_cast at h3
      rw [hu] at h3
      refine h3.trans (le_trans ?_ (hlow he))
      have h6 : (2 : ℝ) ^ g.elo ≤ (2 : ℝ) ^ e := zpow_le_zpow_right₀ (by norm_num) hel
      have h8 := mul_le_mul_of_nonneg_right h6 hc46
      rw [e1, e1] at h8
      exact h8
    · simp only [↓reduceIte] at o4
      rw [o4, Rat.cast_zero]
      exact hR0
  have hb : |∑ i ∈ range 8, r i| ≤ ((g.hi : ℚ) : ℝ) := by
    have h3 := (Rat.cast_le (K := ℝ)).mpr o5
    push_cast at h3
    refine le_trans (le_min hRtop ?_) h3
    exact ((abs_sum_le_sum_abs _ _).trans hU.le).trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
  -- `|ln x|` lies in `[ℓ₁, ℓ₂]`
  have hE' := hE
  simp only [log8E, logE] at hE'
  have t1 : |∑ i ∈ range 8, y0 i| ≤ |Real.log (∑ i ∈ range 8, x i)| +
      (((log8E0 : ℚ) : ℝ) + ((log8E1 : ℚ) : ℝ) * |Real.log (∑ i ∈ range 8, x i)|) := by
    have h := abs_add_le (Real.log (∑ i ∈ range 8, x i)) (∑ i ∈ range 8, y0 i - Real.log (∑ i ∈ range 8, x i))
    rw [add_sub_cancel] at h
    linarith
  have t2 : |Real.log (∑ i ∈ range 8, x i)| ≤ |∑ i ∈ range 8, y0 i| +
      (((log8E0 : ℚ) : ℝ) + ((log8E1 : ℚ) : ℝ) * |Real.log (∑ i ∈ range 8, x i)|) := by
    have h := abs_sub_abs_le_abs_sub (Real.log (∑ i ∈ range 8, x i)) (∑ i ∈ range 8, y0 i)
    rw [abs_sub_comm] at h
    linarith
  have hl1 : ((g.l₁ : ℚ) : ℝ) ≤ |Real.log (∑ i ∈ range 8, x i)| := by
    rcases o7 with h | h
    · rw [h, Rat.cast_zero]
      exact abs_nonneg _
    · have h3 := (Rat.cast_le (K := ℝ)).mpr h
      push_cast at h3
      rw [hRabs] at ha
      refine le_of_mul_le_mul_right ?_ (by linarith : (0 : ℝ) < 1 + ((log8E1 : ℚ) : ℝ))
      linarith
  have hl2 : |Real.log (∑ i ∈ range 8, x i)| ≤ ((g.l₂ : ℚ) : ℝ) := by
    have h3 := (Rat.cast_le (K := ℝ)).mpr o8
    push_cast at h3
    rw [hRabs] at hb
    refine le_of_mul_le_mul_right ?_ (by linarith : (0 : ℝ) < 1 - ((log8E1 : ℚ) : ℝ))
    linarith
  have h01 : (0 : ℝ) ≤ ((g.l₁ : ℚ) : ℝ) := by exact_mod_cast o6
  have hs : Convex ℝ (Icc ((g.l₁ : ℚ) : ℝ) ((g.l₂ : ℚ) : ℝ)) := convex_Icc _ _
  have hpos' : ∀ t ∈ Icc ((g.l₁ : ℚ) : ℝ) ((g.l₂ : ℚ) : ℝ), 0 ≤ t := fun t h => h01.trans h.1
  -- the sign, the evaluations and the case
  obtain ⟨pos, hpos⟩ : ∃ pos : Bool, if pos then 0 ≤ ∑ i ∈ range 8, r i else ∑ i ∈ range 8, r i ≤ 0 := by
    rcases le_total 0 (∑ i ∈ range 8, r i) with h | h
    · exact ⟨true, by simpa using h⟩
    · exact ⟨false, by simpa using h⟩
  obtain ⟨ev₁, ev₂⟩ := hgG pos
  have ps := hgT pos
  rw [hgm, hgd] at ev₁ ev₂ ps
  have hr : ∀ i < 8, F 53 (r i) := fun i hi => by rw [hry i]; exact F_neg 53 (hy0 i hi)
  have hδ0 : |∑ i ∈ range 8, r i - (-∑ i ∈ range 8, y0 i - ((0 : ℤ) : ℝ) * Real.log 2)| ≤ (0 : ℝ) := by
    rw [hRY]
    simp
  have key : ∀ b : ℝ → ℝ, Cvx (Icc ((g.l₁ : ℚ) : ℝ) ((g.l₂ : ℚ) : ℝ)) b →
      |∑ i ∈ range 8, r i| ≤ b |Real.log (∑ i ∈ range 8, x i)| → b ((g.l₁ : ℚ) : ℝ) ≤ ((g.b₁ : ℚ) : ℝ) →
      b ((g.l₂ : ℚ) : ℝ) ≤ ((g.b₂ : ℚ) : ℝ) →
      |(logOp 53 8 Sx Sp Sc y0 x 0 (expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d') 436 eφ et ec
          (fun k i => ((log8F k i : ℚ) : ℝ)) 4).sum - Real.log (∑ i ∈ range 8, x i)| ≤
        (if g.zero then (1 : ℝ) / 2 ^ 509 else 0) +
          9926 / 1000 * u 53 ^ 8 * |Real.log (∑ i ∈ range 8, x i)| := fun b hbc hbl hb₁ hb₂ =>
    log8_k0 hS₁ hS₂ hSx
      (hSp (log8_tsum_k0 hS₁ hS₂ y0 hy1 hy2 o6 ⟨hl1, hl2⟩ hbc hE r hr hry g.a ha hbl pos hpos e hU d'
        (by rw [← hgd]; exact o2) hF hφF ps hb₂))
      hSc x hx hX0 hH y0 hy0 hy1 hy2 o6 ⟨hl1, hl2⟩ hbc hE r hr hry g.a ha hbl pos hpos e hU
      d' (by rw [← hgd]; exact o2) hF hφF (log8_pix hSx x hX0 hH _ _ 0 hE hδ0 ha hbl pos hpos) hSx0 eφ et ec hUφ
      hUt hUc hF' hφ' hsh ev₁ ev₂ hb₁ hb₂ o10
  have hfin : ∀ z : Bool, (if z then (1 : ℝ) / 2 ^ 509 else 0) +
      9926 / 1000 * u 53 ^ 8 * |Real.log (∑ i ∈ range 8, x i)| ≤
        9926 / 1000 * u 53 ^ 8 * |Real.log (∑ i ∈ range 8, x i)| + 1 / 2 ^ 509 := fun z => by
    cases z
    · simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
      exact le_add_of_nonneg_right (by positivity)
    · simp only [↓reduceIte]
      exact (add_comm _ _).le
  cases hcst : g.cst
  · simp only [hcst, Bool.false_eq_true, ↓reduceIte] at o9
    exact (key log8Yb (logYb_cvx hs hpos' he0' he1') (by rw [hRabs]; exact hY)
      ((log8Yb_le g.l₁).trans ((Rat.cast_le (K := ℝ)).mpr o9.1))
      ((log8Yb_le g.l₂).trans ((Rat.cast_le (K := ℝ)).mpr o9.2))).trans (hfin _)
  · simp only [hcst, ↓reduceIte] at o9
    exact (key (fun _ => ((g.hi : ℚ) : ℝ)) (Cvx.const hs (hR0.trans hb)) hb ((Rat.cast_le (K := ℝ)).mpr o9.1)
      ((Rat.cast_le (K := ℝ)).mpr o9.2)).trans (hfin _)

omit [Prec_gt_0 (53 : ℤ)] in
/-- The group of an exponent `e ≤ -2` for `k ≠ 0`: one of the table for `e ≥ -436`, and the last below; `P` is
what the kernel proves of every group. -/
theorem log8_pick1 {P : Log8G1 → Prop} (hall : ∀ g ∈ log8Grp1, P g) (hlast : P log8Last1) {e : ℤ}
    (he2 : e ≤ -2) :
    ∃ (g : Log8G1) (last : Bool), P g ∧ Log8G1Ok log8Top1 log8Tail1 last g ∧
      g.m = (e + 7).toNat ∧ g.d = exp8Deg (e - (e + 7).toNat) ∧ e ≤ g.ehi ∧
      (last = false → -436 ≤ e ∧ g.elo ≤ e) := by
  obtain ⟨gOk, gCov, gLast, gL1, gL2, gL3⟩ := log8_grps1
  by_cases he : -436 ≤ e
  · obtain ⟨g, hg, hg1, hg2⟩ := gCov e he he2
    have hok := gOk g hg
    obtain ⟨o1a, o1b⟩ := hok.1 e hg1 hg2
    exact ⟨g, false, hall g hg, hok, o1a, by rw [← o1a]; exact o1b, hg2, fun _ => ⟨he, hg1⟩⟩
  · have he437 : e ≤ -437 := by omega
    have hm0 : (e + 7).toNat = 0 := by omega
    refine ⟨log8Last1, true, hlast, gLast, by rw [gL1, hm0], ?_, by rw [gL3]; exact he437, fun h => by simp at h⟩
    rw [gL2, hm0]
    simpa using (exp8Deg_small he437).symm

/-- The run's `r` for `k ≠ 0`, a two-part start within `E(|ln x|)` of `ln x` and `|ln x| ≤ X = 745.2`: its parts
are in `F`, `|r| ≤ r̄_max + δ*` and `∑_{i ≥ 1}|r_i|` are within the table's bounds, and `|ln x| ≥ ℓ_k^-` -/
theorem log8_red_facts (y0 : ℕ → ℝ) (hy0 : ∀ i < 8, F 53 (y0 i)) (hy1 : |y0 1| ≤ u 53 * |y0 0|)
    (hy2 : ∀ i, 2 ≤ i → y0 i = 0) {L : ℝ} (hE : |∑ i ∈ range 8, y0 i - L| ≤ log8E |L|)
    (hL : |L| ≤ ((log8X : ℚ) : ℝ)) (hk : expK 53 (-y0 0) ≠ 0) :
    (∀ i < 8, F 53 (expR 53 8 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) i)) ∧
      |∑ i ∈ range 8, expR 53 8 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) i| ≤
        ((log8Top1 : ℚ) : ℝ) ∧
      ∑ i ∈ Ico 1 8, |expR 53 8 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) i| ≤
        ((log8Tail1 : ℚ) : ℝ) ∧ ((log8Lk : ℚ) : ℝ) ≤ |L| := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hA3 : (((8 : ℕ) : ℝ) ^ 2 + (8 : ℕ)) * u (53 : ℤ) < 1 := by rw [hu53]; norm_num
  have h1u : (0 : ℝ) ≤ 1 - u 53 := by rw [hu53]; norm_num
  have h1p : (0 : ℝ) < 1 + u 53 := by rw [hu53]; norm_num
  obtain ⟨cLk, -, -, cX1, cA0, cTop, cTail, -, cTop0⟩ := log8_consts1
  obtain ⟨-, he1, -⟩ := log8E_consts
  obtain ⟨-, -, -, -, -, -, -, ccr, -, -, -⟩ := exp8_consts
  have hcr : (0 : ℝ) < ((cr8 : ℚ) : ℝ) := by exact_mod_cast ccr
  have he1' : (0 : ℝ) ≤ ((log8E1 : ℚ) : ℝ) := by exact_mod_cast he1
  have hXq : (0 : ℚ) ≤ log8X := by unfold log8X; norm_num
  have hX0 : (0 : ℝ) ≤ ((log8X : ℚ) : ℝ) := by exact_mod_cast hXq
  have hTop0 : (0 : ℝ) ≤ ((log8Top1 : ℚ) : ℝ) := by exact_mod_cast cTop0
  have hs : Convex ℝ (Icc (0 : ℝ) ((log8X : ℚ) : ℝ)) := convex_Icc _ _
  have hpos : ∀ l ∈ Icc (0 : ℝ) ((log8X : ℚ) : ℝ), 0 ≤ l := fun l h => h.1
  have mL : |L| ∈ Icc (0 : ℝ) ((log8X : ℚ) : ℝ) := ⟨abs_nonneg L, hL⟩
  have mX : ((log8X : ℚ) : ℝ) ∈ Icc (0 : ℝ) ((log8X : ℚ) : ℝ) := ⟨hX0, le_rfl⟩
  obtain ⟨cv1, cv2, -, cv4⟩ := log8_red_cvx hs hpos hTop0
  obtain ⟨a1, a4, a2, hlem⟩ := log8_red_b y0 hy0 hy1 hy2 hE hL cX1 cA0 hk
  obtain ⟨r, hrd⟩ : ∃ r, r = expR 53 8 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) :=
    ⟨_, rfl⟩
  rw [← hrd] at hlem ⊢
  -- `|r| ≤ r̄_max + δ*`, at `X`
  have hRtop : |∑ i ∈ range 8, r i| ≤ ((log8Top1 : ℚ) : ℝ) := by
    have hds : _ ≤ log8DsR |L| := (hlem _ a2).1
    have h1 : rMax 53 (log8Yb |L| / (1 - u 53)) (2 * u 53 * log8Yb |L|) ≤ ((log8RMax log8X : ℚ) : ℝ) :=
      (cv1.mono mL mX hL).trans (log8RMax_le log8X hXq)
    have h2 := (cv2.mono mL mX hL).trans (log8DsR_le log8X hXq)
    have h3 := (Rat.cast_le (K := ℝ)).mpr cTop
    push_cast at h3
    have h4 := abs_sub_abs_le_abs_sub (∑ i ∈ range 8, r i)
      (-∑ i ∈ range 8, y0 i - expK 53 (-y0 0) * Real.log 2)
    linarith
  -- the parts, at `r̄ = ` the bound of `|r|`
  have hre : |-∑ i ∈ range 8, y0 i - expK 53 (-y0 0) * Real.log 2| ≤ ((log8Top1 : ℚ) : ℝ) + log8DsR |L| := by
    have hds : _ ≤ log8DsR |L| := (hlem _ a2).1
    have h := abs_sub_le_add (∑ i ∈ range 8, r i)
      (∑ i ∈ range 8, r i - (-∑ i ∈ range 8, y0 i - expK 53 (-y0 0) * Real.log 2))
    rw [sub_sub_cancel] at h
    linarith
  have hπT : ∀ i, |r i| ≤ ((log8PiR log8X log8Top1 i : ℚ) : ℝ) := fun i =>
    (((hlem _ hre).2 i).trans ((cv4 i).mono mL mX hL)).trans (log8PR_le log8X hXq le_rfl i)
  have htail : ∑ i ∈ Ico 1 8, |r i| ≤ ((log8Tail1 : ℚ) : ℝ) := by
    have h1 : ∑ i ∈ Ico 1 8, |r i| ≤ ∑ i ∈ Ico 1 8, ((log8PiR log8X log8Top1 i : ℚ) : ℝ) :=
      sum_le_sum fun i _ => hπT i
    have h2 := (Rat.cast_le (K := ℝ)).mpr cTail
    push_cast at h2
    linarith
  -- the parts are in `F`
  have hrF : ∀ i < 8, F 53 (r i) := by
    intro i _
    have hkb' : |((expK 53 (-y0 0) : ℤ) : ℝ)| ≤ 1075 := by rw [← Int.cast_abs]; exact_mod_cast a1
    have hkF : F 53 (-((expK 53 (-y0 0) : ℤ) : ℝ)) := by
      refine F_of_mult 53 (E := 0) ⟨-expK 53 (-y0 0), by push_cast; ring⟩ ?_
      rw [abs_neg, zero_add]
      calc |((expK 53 (-y0 0) : ℤ) : ℝ)| ≤ 1075 := hkb'
        _ < (2 : ℝ) ^ (53 : ℤ) := by norm_num
    obtain ⟨-, -, m3, -⟩ := mulf_G 53 8 (by norm_num) (by norm_num) hA3 (fun i => ((cl8 i : ℚ) : ℝ))
      (-((expK 53 (-y0 0) : ℤ) : ℝ)) (fun i => |((cl8 i : ℚ) : ℝ)|) |(-((expK 53 (-y0 0) : ℤ) : ℝ))|
      (fun i _ => cl8_F 53 rfl i) hkF (fun _ _ => le_rfl) le_rfl _ le_rfl
    have hxF : ∀ i < 8, F 53 (xRed 53 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) i) := fun i hi => by
      unfold xRed
      split_ifs with h0
      · exact a4
      · exact F_neg 53 (hy0 i hi)
    have := F_addOp 53 8 (by norm_num) (by norm_num) hA3 (xRed 53 (fun i => -y0 i) ((ch8 : ℚ) : ℝ))
      (pt (mulfOp 53 8 (fun i => ((cl8 i : ℚ) : ℝ)) (-((expK 53 (-y0 0) : ℤ) : ℝ)))) hxF (fun j _ => m3 j) i
    rw [hrd]
    unfold expR
    simp only [hk, ↓reduceIte]
    exact this
  -- `|ln x| ≥ ℓ_k^-`: `|y_{0,0}| ≥ 1/(2c_r(1 + u))`
  have hLk : ((log8Lk : ℚ) : ℝ) ≤ |L| := by
    obtain ⟨-, -, hlo, -, -⟩ := log8_two y0 hy1 hy2
    have h1 : 1 / 2 ≤ |RN 53 (-y0 0 * cR 53)| := roundAway_ne_zero hk
    have h2 := abs_RN_le 53 (-y0 0 * cR 53)
    rw [cR_eq 53 rfl] at h1 h2
    rw [abs_mul, abs_neg, abs_of_pos hcr] at h2
    have h3 : (1 - u 53) / (2 * ((cr8 : ℚ) : ℝ) * (1 + u 53)) ≤ |∑ i ∈ range 8, y0 i| := by
      rw [div_le_iff₀ (by positivity)]
      calc 1 - u 53 = (1 - u 53) * 2 * (1 / 2) := by ring
        _ ≤ (1 - u 53) * 2 * ((1 + u 53) * (|y0 0| * ((cr8 : ℚ) : ℝ))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by linarith)
        _ = |y0 0| * (1 - u 53) * (2 * ((cr8 : ℚ) : ℝ) * (1 + u 53)) := by ring
        _ ≤ |∑ i ∈ range 8, y0 i| * (2 * ((cr8 : ℚ) : ℝ) * (1 + u 53)) :=
          mul_le_mul_of_nonneg_right hlo (by positivity)
    have h4 := (Rat.cast_le (K := ℝ)).mpr cLk
    push_cast at h4
    rw [hu] at h4
    have hE' := hE
    simp only [log8E, logE] at hE'
    have t1 : |∑ i ∈ range 8, y0 i| ≤ |L| + (((log8E0 : ℚ) : ℝ) + ((log8E1 : ℚ) : ℝ) * |L|) := by
      have h := abs_add_le L (∑ i ∈ range 8, y0 i - L)
      rw [add_sub_cancel] at h
      linarith
    refine le_of_mul_le_mul_right ?_ (by linarith : (0 : ℝ) < 1 + ((log8E1 : ℚ) : ℝ))
    linarith
  exact ⟨hrF, hRtop, htail, hLk⟩

/-- Theorem 42 (`thm:log`) at `n = 8` for a run with `k ≠ 0` and `|ln x| ≤ X = 745.2`, from the kernel's
evaluations of the groups of `k ≠ 0`: `r` is EXP's reduction of `-y_0`, the exponent `e` of step (2) selects a
group, the sign and the size of `r` an interval `[a, b]` of the group, and `log8_k1` applies on `[ℓ_k^-, X]` -/
theorem log8_run1 (hall : ∀ g ∈ log8Grp1, Log8Group1 log8Lk g ∧ Log8GroupT1 g)
    (hlast : Log8Group1 log8Lk log8Last1 ∧ Log8GroupT1 log8Last1)
    (hsh : Log8Shared) {S₁ S₂ Sx Sp Sc : ℝ → ℝ} (e : ℤ) (hS₁ : Scl 53 ((exp8Eta1 (e + 7).toNat : ℚ) : ℝ) S₁)
    (hS₂ : Scl 53 ((exp8Eta : ℚ) : ℝ) S₂) (hSx : Scl 53 ((2 * exp8Eta : ℚ) : ℝ) Sx)
    (hSc : Scl 53 ((exp8Eta : ℚ) : ℝ) Sc) (x : ℕ → ℝ)
    (hx : ∀ i < 8, F 53 (x i)) (hX0 : 0 < ∑ i ∈ range 8, x i) (hH : Htheta 53 8 2 x)
    (hX : |Real.log (∑ i ∈ range 8, x i)| ≤ 7452 / 10) (y0 : ℕ → ℝ)
    (hy0 : ∀ i < 8, F 53 (y0 i)) (hy1 : |y0 1| ≤ u 53 * |y0 0|) (hy2 : ∀ i, 2 ≤ i → y0 i = 0)
    (hE : |∑ i ∈ range 8, y0 i - Real.log (∑ i ∈ range 8, x i)| ≤ log8E |Real.log (∑ i ∈ range 8, x i)|)
    (k : ℤ) (hkd : k = expK 53 (-y0 0)) (hk : k ≠ 0) (r : ℕ → ℝ)
    (hrd : r = expR 53 8 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)))
    (hSp : ∑ i ∈ range 8, |expCore 53 8 S₁ S₂ e (e + 7).toNat r (fun k i => ((exp8F k i : ℚ) : ℝ))
      (exp8Deg (e - (e + 7).toNat)) i| ≤ 1 → Scl 53 ((2 * exp8Eta : ℚ) : ℝ) Sp)
    (hsel : ((2 : ℝ) ^ e ≤ expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) r ∧
        expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) r < (2 : ℝ) ^ (e + 1)) ∨
      (expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) r < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023))
    (hSx0 : 1 / 2 ≤ (2 : ℝ) ^ k * x 0 → (2 : ℝ) ^ k * x 0 ≤ 2 → Sx ((2 : ℝ) ^ k * x 0) = (2 : ℝ) ^ k * x 0)
    (eφ et ec : ℤ) (hUφ : ∑ i ∈ range 8, |logPhi 53 8 Sx k x i| < (2 : ℝ) ^ (eφ + 1))
    (hUt : ∑ i ∈ range 8, |expCore 53 8 S₁ S₂ e (e + 7).toNat r (fun k i => ((exp8F k i : ℚ) : ℝ))
      (exp8Deg (e - (e + 7).toNat)) i| < (2 : ℝ) ^ (et + 1))
    (hUc : ∑ i ∈ range 8, |logC 53 8 Sp 436 eφ et (logPhi 53 8 Sx k x)
      (expCore 53 8 S₁ S₂ e (e + 7).toNat r (fun k i => ((exp8F k i : ℚ) : ℝ))
        (exp8Deg (e - (e + 7).toNat))) i| < (2 : ℝ) ^ (ec + 1)) :
    |(logOp 53 8 Sx Sp Sc y0 x k (expCore 53 8 S₁ S₂ e (e + 7).toNat r (fun k i => ((exp8F k i : ℚ) : ℝ))
        (exp8Deg (e - (e + 7).toNat))) 436 eφ et ec (fun k i => ((log8F k i : ℚ) : ℝ)) 4).sum -
        Real.log (∑ i ∈ range 8, x i)| ≤
      9926 / 1000 * u 53 ^ 8 * |Real.log (∑ i ∈ range 8, x i)| + 1 / 2 ^ 509 := by
  obtain ⟨hF, hφF, hF', hφ'⟩ := log8_tables
  obtain ⟨-, cLk0, -, cX1, cA0, -, -, cSel, -⟩ := log8_consts1
  have hL : |Real.log (∑ i ∈ range 8, x i)| ≤ ((log8X : ℚ) : ℝ) := by
    refine hX.trans_eq ?_
    unfold log8X
    norm_num
  subst hkd
  obtain ⟨hrF, hRtop, htail, hLk⟩ := log8_red_facts y0 hy0 hy1 hy2 hE hL hk
  rw [← hrd] at hrF hRtop htail
  have hR0 : 0 ≤ |∑ i ∈ range 8, r i| := abs_nonneg _
  -- the exponent
  obtain ⟨hU, hsel2⟩ := log8_sel r e hsel
  have hlow : -436 ≤ e →
      (2 : ℝ) ^ e * (1 - 1 / 2 ^ 46) - 2 * ((log8Tail1 : ℚ) : ℝ) ≤ |∑ i ∈ range 8, r i| := by
    intro he
    obtain ⟨-, h1⟩ := hsel2 he
    have hs : ∑ i ∈ range 8, |r i| = |r 0| + ∑ i ∈ Ico 1 8, |r i| := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by norm_num)]
    have hr : ∑ i ∈ range 8, r i = r 0 + ∑ i ∈ Ico 1 8, r i := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by norm_num)]
    have h2 : |∑ i ∈ Ico 1 8, r i| ≤ ∑ i ∈ Ico 1 8, |r i| := abs_sum_le_sum_abs _ _
    have h3 := abs_sub_abs_le_abs_sub (r 0) (-∑ i ∈ Ico 1 8, r i)
    rw [abs_neg, sub_neg_eq_add, ← hr] at h3
    linarith
  have he2 : e ≤ -2 := by
    by_contra hcon
    have hl := hlow (by omega)
    have h6 : (2 : ℝ) ^ (-1 : ℤ) ≤ (2 : ℝ) ^ e := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h7 := (Rat.cast_lt (K := ℝ)).mpr cSel
    push_cast at h7
    have h8 := mul_le_mul_of_nonneg_right h6 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 46)
    linarith
  -- the group of `e`
  obtain ⟨g, last, ⟨hgG, hgT⟩, hgOk, hgm, hgd, hge, hgl⟩ := log8_pick1 hall hlast he2
  obtain ⟨-, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := hgOk
  obtain ⟨m, hm⟩ : ∃ m, m = (e + 7).toNat := ⟨_, rfl⟩
  rw [← hm] at hS₁ hSp hUt hUc hgm hgd ⊢
  obtain ⟨d', hd'⟩ : ∃ d', d' = exp8Deg (e - m) := ⟨_, rfl⟩
  rw [← hd'] at hSp hUt hUc hgd ⊢
  have hglo : ((g.lo : ℚ) : ℝ) ≤ |∑ i ∈ range 8, r i| := by
    cases last
    · simp only [Bool.false_eq_true, ↓reduceIte] at o3
      obtain ⟨he, hel⟩ := hgl rfl
      have h3 := (Rat.cast_le (K := ℝ)).mpr o3
      push_cast at h3
      refine h3.trans (max_le hR0 (le_trans ?_ (hlow he)))
      have h6 : (2 : ℝ) ^ g.elo ≤ (2 : ℝ) ^ e := zpow_le_zpow_right₀ (by norm_num) hel
      have h8 := mul_le_mul_of_nonneg_right h6 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 46)
      linarith
    · simp only [↓reduceIte] at o3
      rw [o3, Rat.cast_zero]
      exact hR0
  have hghi : |∑ i ∈ range 8, r i| ≤ ((g.hi : ℚ) : ℝ) := by
    have h3 := (Rat.cast_le (K := ℝ)).mpr o4
    push_cast at h3
    refine le_trans (le_min hRtop ?_) h3
    exact ((abs_sum_le_sum_abs _ _).trans hU.le).trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
  -- the sign and the interval of `|r|`
  obtain ⟨pos, hpos⟩ : ∃ pos : Bool, if pos then 0 ≤ ∑ i ∈ range 8, r i else ∑ i ∈ range 8, r i ≤ 0 := by
    rcases le_total 0 (∑ i ∈ range 8, r i) with h | h
    · exact ⟨true, by simpa using h⟩
    · exact ⟨false, by simpa using h⟩
  obtain ⟨bn, hbnG, ps, hbn1, hbn2, hbnc⟩ : ∃ bn : ℚ × ℚ × ℚ × ℚ, Log8Bin1 log8Lk pos g.m g.d bn ∧
      Log8Psi false pos g.m g.d bn.1 log8X bn.2.1 bn.2.2.2 ∧
      ((bn.1 : ℚ) : ℝ) ≤ |∑ i ∈ range 8, r i| ∧ |∑ i ∈ range 8, r i| ≤ ((bn.2.1 : ℚ) : ℝ) ∧
      bn.2.1 + log8Eq log8X + bn.2.2.2 ≤ 3 / 5 := by
    cases pos
    · obtain ⟨ab, hab, hab1, hab2⟩ := log8Cover_cover _ _ _ o8 (by simpa using o6) _ hglo hghi
      obtain ⟨bn, hbn, rfl⟩ := List.mem_map.mp hab
      exact ⟨bn, hgG.2 bn hbn, hgT.2 bn hbn, hab1, hab2, o10 bn hbn⟩
    · obtain ⟨ab, hab, hab1, hab2⟩ := log8Cover_cover _ _ _ o7 (by simpa using o5) _ hglo hghi
      obtain ⟨bn, hbn, rfl⟩ := List.mem_map.mp hab
      exact ⟨bn, hgG.1 bn hbn, hgT.1 bn hbn, hab1, hab2, o9 bn hbn⟩
  obtain ⟨ev₁, ev₂⟩ := hbnG
  rw [hgm, hgd] at ev₁ ev₂ ps
  -- the case
  have hbn2' := hbn2
  rw [hrd] at hbn2'
  obtain ⟨hδ, -⟩ := log8_red_run y0 hy0 hy1 hy2 hE hL cX1 cA0 hk hbn2'
  rw [← hrd] at hδ
  have hts := log8_tsum_k1 hS₁ hS₂ y0 hy0 hy1 hy2 cLk0 ⟨hLk, hL⟩ hE r hrF hrd hk cX1 cA0 bn.1 hbn1 bn.2.1 hbn2 pos
    hpos e hU d' (by rw [← hgd]; exact o2) hF hφF ps
  refine (log8_k1 hS₁ hS₂ hSx (hSp hts) hSc x hx hX0 hH y0 hy0 hy1 hy2 cLk0 ⟨hLk, hL⟩ hE r hrF hrd _ rfl hk cX1 cA0
    bn.1 hbn1 bn.2.1 hbn2 pos hpos e hU d' (by rw [← hgd]; exact o2) hF hφF
    (log8_pix hSx x hX0 hH _ _ _ hE hδ hbn1 hbn2 pos hpos) hSx0 eφ et ec hUφ hUt hUc hF' hφ' hsh ev₁ ev₂
    hbnc).trans ?_
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  exact le_add_of_nonneg_right (by positivity)

/-! ## The run of `LOG_{8,6,43,4}` after its start -/

/-- step (2)'s `r`: EXP's reduction of `-y_0` with multidouble's constants -/
noncomputable def ln8R (p : ℤ) (y0 : ℕ → ℝ) : ℕ → ℝ :=
  expR p 8 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ))

/-- step (2)'s `t`: EXP's core on `r`, with `m = max(0, e + 7)` and the degree of EXP's step (3); the scaling by
`2^{-m}`, where `m > 0`, and the scalings back are rounded by `S` -/
noncomputable def ln8T (p : ℤ) (S : ℝ → ℝ) (y0 : ℕ → ℝ) (e : ℤ) : ℕ → ℝ :=
  expCore p 8 (if (e + 7).toNat = 0 then id else S) S e (e + 7).toNat (ln8R p y0)
    (fun k i => ((exp8F k i : ℚ) : ℝ)) (exp8Deg (e - (e + 7).toNat))

/-- step (3)'s `φ = ADDF(x', -1)`, with `x' = 2^k x` scaled in two steps, by `2^{k₁}` and then by `2^{k₂}`, each
rounded by `S`: `logPhi`'s rounding is the pair, `w ↦ S(2^{k₂} S(2^{-k₂} w))` at `w = 2^{k₁ + k₂} x_i`
(`Scl.two_step_apply`) -/
noncomputable def ln8Phi (p : ℤ) (S : ℝ → ℝ) (k₁ k₂ : ℤ) (x : ℕ → ℝ) : ℕ → ℝ :=
  logPhi p 8 (fun w => S ((2 : ℝ) ^ k₂ * S ((2 : ℝ) ^ (-k₂) * w))) (k₁ + k₂) x

/-- step (4)'s `c`, with `B = 436`; the product `p` is scaled back in two steps, by `2^{e_φ}` and then by
`2^{e_t}`, each rounded by `S` -/
noncomputable def ln8C (p : ℤ) (S : ℝ → ℝ) (eφ et : ℤ) (φ t : ℕ → ℝ) : ℕ → ℝ :=
  logC p 8 (fun w => S ((2 : ℝ) ^ et * S ((2 : ℝ) ^ (-et) * w))) 436 eφ et φ t

/-- `LOG_{8,6,43,4}` after its start `y_0`: steps (2) to (5) with `B = 436`, the order `q = 4`, multidouble's
tables, and every scaling that can leave the normal range rounded by `S` -/
noncomputable def ln8 (p : ℤ) (S : ℝ → ℝ) (y0 x : ℕ → ℝ) (k₁ k₂ e eφ et ec : ℤ) : List ℝ :=
  logOp p 8 (fun w => S ((2 : ℝ) ^ k₂ * S ((2 : ℝ) ^ (-k₂) * w)))
    (fun w => S ((2 : ℝ) ^ et * S ((2 : ℝ) ^ (-et) * w))) S y0 x (k₁ + k₂) (ln8T p S y0 e) 436 eφ et ec
    (fun k i => ((log8F k i : ℚ) : ℝ)) 4

/-- Theorem 42 (`thm:log`) at `n = 8` and `p = 53` from the kernel's evaluations of the groups and its checks of
the parts of `t`, which `Log8/All.lean` and `Log8/PsiAll.lean` prove: `|y - ln x| ≤ 9.926u^8|ln x| + 2^{-509}`.
The hypotheses are those of `thm42_8`. -/
theorem log8_main (hall0 : ∀ g ∈ log8Grp0, Log8Group0 g ∧ Log8GroupT0 g)
    (hlast0 : Log8Group0 log8Last0 ∧ Log8GroupT0 log8Last0)
    (hall1 : ∀ g ∈ log8Grp1, Log8Group1 log8Lk g ∧ Log8GroupT1 g)
    (hlast1 : Log8Group1 log8Lk log8Last1 ∧ Log8GroupT1 log8Last1) (hsh : Log8Shared)
    (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℕ → ℝ) (hx : ∀ i < 8, F 53 (x i)) (hH : Htheta 53 8 2 x) (hX0 : 0 < ∑ i ∈ range 8, x i)
    (hX : |Real.log (∑ i ∈ range 8, x i)| ≤ 7452 / 10) (y0 : ℕ → ℝ) (hy0 : ∀ i < 8, F 53 (y0 i))
    (hy1 : |y0 1| ≤ u 53 * |y0 0|) (hy2 : ∀ i, 2 ≤ i → y0 i = 0)
    (hE : |∑ i ∈ range 8, y0 i - Real.log (∑ i ∈ range 8, x i)| ≤ log8E |Real.log (∑ i ∈ range 8, x i)|)
    (k₁ k₂ : ℤ) (hk : k₁ + k₂ = expK 53 (-y0 0)) (hk2 : k₂ ≤ 0) (e : ℤ)
    (hsel : ((2 : ℝ) ^ e ≤ expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R 53 y0) ∧
        expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R 53 y0) < (2 : ℝ) ^ (e + 1)) ∨
      (expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R 53 y0) < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023))
    (eφ et ec : ℤ) (hUφ : ∑ i ∈ range 8, |ln8Phi 53 S k₁ k₂ x i| < (2 : ℝ) ^ (eφ + 1))
    (hselt : ((2 : ℝ) ^ et ≤ expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T 53 S y0 e) ∧
        expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T 53 S y0 e) < (2 : ℝ) ^ (et + 1)) ∨
      (expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T 53 S y0 e) < (2 : ℝ) ^ (-1022 : ℤ) ∧ et = -1023))
    (hUc : ∑ i ∈ range 8, |ln8C 53 S eφ et (ln8Phi 53 S k₁ k₂ x) (ln8T 53 S y0 e) i| < (2 : ℝ) ^ (ec + 1)) :
    |(ln8 53 S y0 x k₁ k₂ e eφ et ec).sum - Real.log (∑ i ∈ range 8, x i)| ≤
      9926 / 1000 * u 53 ^ 8 * |Real.log (∑ i ∈ range 8, x i)| + 1 / 2 ^ 509 := by
  -- the scalings' roundings are in the class
  have hS0 := Scl.of_grid 53 rfl S hS
  have hS₂ : Scl 53 ((exp8Eta : ℚ) : ℝ) S := by
    rw [cast_exp8Eta]
    exact hS0
  have hS₁ : Scl 53 ((exp8Eta1 (e + 7).toNat : ℚ) : ℝ) (if (e + 7).toNat = 0 then id else S) := by
    rw [cast_exp8Eta1]
    unfold eta0m
    split_ifs
    · exact Scl.id 53
    · exact hS0
  have h2η : ((2 * exp8Eta : ℚ) : ℝ) = 2 * (2 : ℝ) ^ (-1075 : ℤ) := by
    push_cast
    rw [cast_exp8Eta]
  have hSx : Scl 53 ((2 * exp8Eta : ℚ) : ℝ) fun w => S ((2 : ℝ) ^ k₂ * S ((2 : ℝ) ^ (-k₂) * w)) := by
    rw [h2η]
    exact hS0.two_step 53 hk2
  -- step (4)'s pair of scalings is in the class where `e_t ≤ 0`, which `∑|t_i| ≤ 1` gives
  have hUt := (log8_sel (ln8T 53 S y0 e) et hselt).1
  have hSp : ∑ i ∈ range 8, |ln8T 53 S y0 e i| ≤ 1 →
      Scl 53 ((2 * exp8Eta : ℚ) : ℝ) fun w => S ((2 : ℝ) ^ et * S ((2 : ℝ) ^ (-et) * w)) := fun hts => by
    rw [h2η]
    exact hS0.two_step 53 (log8_et _ hts et hselt)
  have hSx0 : 1 / 2 ≤ (2 : ℝ) ^ (k₁ + k₂) * x 0 → (2 : ℝ) ^ (k₁ + k₂) * x 0 ≤ 2 →
      (fun w => S ((2 : ℝ) ^ k₂ * S ((2 : ℝ) ^ (-k₂) * w))) ((2 : ℝ) ^ (k₁ + k₂) * x 0) =
        (2 : ℝ) ^ (k₁ + k₂) * x 0 := fun h1 _ => log8_keep hS hk2 h1
  simp only [ln8, ln8T, ln8Phi, ln8C, ln8R] at hsel hUφ hUt hUc hSp ⊢
  by_cases hk0 : expK 53 (-y0 0) = 0
  · have hr : expR 53 8 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) = fun i => -y0 i := by
      unfold expR
      simp only [hk0, ↓reduceIte]
    rw [hk0] at hk
    rw [hk] at hUφ hUc hSx0 ⊢
    exact log8_run0 hall0 hlast0 hsh e hS₁ hS₂ hSx hS₂ x hx hX0 hH y0 hy0 hy1 hy2 hE hk0 _ hr hSp hsel hSx0 eφ et
      ec hUφ hUt hUc
  · exact log8_run1 hall1 hlast1 hsh e hS₁ hS₂ hSx hS₂ x hx hX0 hH hX y0 hy0 hy1 hy2 hE _ hk
      (by rw [hk]; exact hk0) _ rfl hSp hsel hSx0 eφ et ec hUφ hUt hUc

end ExpansionBounds
