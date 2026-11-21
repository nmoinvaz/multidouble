import ExpansionBounds.Renorm

/-!
# Theorem 9 (c): the bound is reached

For `c = (1, u, u², …, uⁿ)` VecSum returns `v = c` and `Ren_n` loses `E = uⁿ = B_0`: each `uⁱ + uⁱ⁺¹` is the
midpoint of `uⁱ` and its successor, and ties to even return `uⁱ`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

theorem u_pow (m : ℕ) : u p ^ m = (2 : ℝ) ^ (-p * m) := by
  unfold u
  rw [← zpow_natCast, ← zpow_mul]

theorem us_mul : us p * (1 + u p) = u p := by
  have h := u_pos p
  unfold us
  field_simp

/-- `B_0 = ūⁿ + ∑_{j=1}^n ū^{n+1-j} uʲ = uⁿ` -/
theorem B0_pow (n : ℕ) : us p ^ n + ∑ j ∈ Ioc 0 n, us p ^ (n + 1 - j) * u p ^ j = u p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Ioc_succ_top (by omega), show n + 1 + 1 - (n + 1) = 1 by omega, pow_one]
    have hs : ∑ j ∈ Ioc 0 n, us p ^ (n + 1 + 1 - j) * u p ^ j =
        us p * ∑ j ∈ Ioc 0 n, us p ^ (n + 1 - j) * u p ^ j := by
      rw [mul_sum]
      refine sum_congr rfl fun j hj => ?_
      rw [mem_Ioc] at hj
      rw [show n + 1 + 1 - j = n + 1 - j + 1 by omega, pow_succ]
      ring
    rw [hs]
    calc us p ^ (n + 1) + (us p * ∑ j ∈ Ioc 0 n, us p ^ (n + 1 - j) * u p ^ j + us p * u p ^ (n + 1))
        = us p * (us p ^ n + ∑ j ∈ Ioc 0 n, us p ^ (n + 1 - j) * u p ^ j) + us p * u p ^ (n + 1) := by ring
      _ = us p * u p ^ n * (1 + u p) := by rw [ih]; ring
      _ = u p ^ (n + 1) := by linear_combination u p ^ n * us_mul p

variable [Prec_gt_0 p]

omit [Prec_gt_0 p] in
/-- the magnitude of `2^e + 2^(e-p)` is `e + 1` -/
theorem mag_tie (hp : 1 < p) (e : ℤ) :
    FloatSpec.Core.Raux.mag 2 ((2 : ℝ) ^ e + (2 : ℝ) ^ (e - p)) = e + 1 := by
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (e - p) := zpow_pos (by norm_num) _
  have h2 : (2 : ℝ) ^ (e - p) < (2 : ℝ) ^ e := zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have h3 : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hpos : 0 < (2 : ℝ) ^ e + (2 : ℝ) ^ (e - p) := by linarith
  have h := FloatSpec.Core.Raux.mag_unique 2 ((2 : ℝ) ^ e + (2 : ℝ) ^ (e - p)) (e + 1) (by norm_num)
    (by rw [abs_of_pos hpos]; push_cast; rw [show e + 1 - 1 = e by ring]; linarith)
    (by rw [abs_of_pos hpos]; push_cast; rw [zpow_add_one₀ (by norm_num)]; linarith) trivial
  simpa [Std.Do.wp, Std.Do.PostCond.noThrow, pure] using h

omit [Prec_gt_0 p] in
/-- ties to even: `RN(2^e + 2^(e-p)) = 2^e`, the midpoint of `2^e` and its successor rounding to the even
significand `2^(p-1)` -/
theorem RN_tie (hp : 1 < p) (e : ℤ) : RN p ((2 : ℝ) ^ e + (2 : ℝ) ^ (e - p)) = (2 : ℝ) ^ e := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, p - 1 = (k : ℤ) + 1 := ⟨(p - 2).toNat, by omega⟩
  set N : ℤ := 2 ^ (k + 1) with hN
  have hNR : (N : ℝ) = (2 : ℝ) ^ (p - 1) := by
    rw [hN, hk]
    push_cast
    rw [← zpow_natCast]
    push_cast
    rfl
  have hc : FloatSpec.Core.Generic_fmt.cexp 2 (FloatSpec.Core.FLX.FLX_exp p) ((2 : ℝ) ^ e + (2 : ℝ) ^ (e - p)) =
      e + 1 - p := by
    show FloatSpec.Core.FLX.FLX_exp p (FloatSpec.Core.Raux.mag 2 _) = _
    rw [mag_tie p hp e]
    rfl
  have hsm : ((2 : ℝ) ^ e + (2 : ℝ) ^ (e - p)) * ((2 : ℤ) : ℝ) ^ (-(e + 1 - p)) = (N : ℝ) + 1 / 2 := by
    rw [hNR, add_mul]
    push_cast
    rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num), show e + -(e + 1 - p) = p - 1 by ring,
      show e - p + -(e + 1 - p) = -1 by ring]
    norm_num
  have hfloor : FloatSpec.Core.Raux.Zfloor ((N : ℝ) + 1 / 2) = N := by
    unfold FloatSpec.Core.Raux.Zfloor
    rw [Int.floor_eq_iff]
    constructor <;> linarith
  have heven : tieEven N = false := by
    unfold tieEven
    rw [hN, pow_succ]
    simp
  have hZ : FloatSpec.Core.Generic_fmt.Znearest tieEven ((N : ℝ) + 1 / 2) = N := by
    rw [FloatSpec.Core.Generic_fmt.Znearest_eq_choice_of_eq_half _ _ (by rw [hfloor]; ring), hfloor, heven]
    simp
  unfold RN FloatSpec.Core.Generic_fmt.roundR FloatSpec.Core.Generic_fmt.scaled_mantissa
  simp only []
  rw [hc, hsm, hZ, hNR]
  push_cast
  rw [← zpow_add₀ (by norm_num)]
  congr 1
  ring

/-- the powers of two are in `F p` -/
theorem F_two_zpow (e : ℤ) : F p ((2 : ℝ) ^ e) := by
  have hm : FloatSpec.Core.Raux.mag 2 ((2 : ℝ) ^ e) = e + 1 := by
    have h := FloatSpec.Core.Raux.mag_bpow 2 e (by norm_num) trivial
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, pure] using h
  have hp0 : 0 < p := Prec_gt_0.pos
  have h : RN p ((2 : ℝ) ^ e) = (2 : ℝ) ^ e :=
    roundR_eq_of_le (FloatSpec.Core.FLX.FLX_exp p) (FloatSpec.Core.Generic_fmt.Znearest tieEven)
      (E := e) ⟨1, by simp⟩ (by
        show FloatSpec.Core.FLX.FLX_exp p (FloatSpec.Core.Raux.mag 2 _) ≤ e
        rw [hm]
        unfold FloatSpec.Core.FLX.FLX_exp
        omega)
  have hF := F_RN p ((2 : ℝ) ^ e)
  rwa [h] at hF

/-- `TwoSum(uⁱ, uⁱ⁺¹) = (uⁱ, uⁱ⁺¹)` -/
theorem twoSum_pow (hp : 1 < p) (i : ℕ) : twoSum p (u p ^ i) (u p ^ (i + 1)) = (u p ^ i, u p ^ (i + 1)) := by
  have hs : (twoSum p (u p ^ i) (u p ^ (i + 1))).1 = u p ^ i := by
    show RN p (u p ^ i + u p ^ (i + 1)) = u p ^ i
    rw [u_pow, u_pow, show -p * ((i + 1 : ℕ) : ℤ) = -p * i - p by push_cast; ring]
    exact RN_tie p hp _
  have hadd := twoSum_add p hp (a := u p ^ i) (b := u p ^ (i + 1)) (by rw [u_pow]; exact F_two_zpow p _)
    (by rw [u_pow]; exact F_two_zpow p _)
  refine Prod.ext hs ?_
  show (twoSum p (u p ^ i) (u p ^ (i + 1))).2 = u p ^ (i + 1)
  linarith

/-- VecSum of `(uⁱ, uⁱ⁺¹, …)` returns its terms -/
theorem vecSum_pow (hp : 1 < p) (m : ℕ) : ∀ (c : ℕ → ℝ) (i : ℕ), (∀ k, c k = u p ^ (i + k)) →
    ∀ j ≤ m, vecSum p m c j = u p ^ (i + j) := by
  induction m with
  | zero =>
    intro c i hc j hj
    obtain rfl : j = 0 := by omega
    simp [vecSum_zero, hc]
  | succ m ih =>
    intro c i hc j hj
    have hc' : ∀ k, (fun k => c (k + 1)) k = u p ^ (i + 1 + k) := fun k => by
      simp only [hc]
      ring_nf
    have hw0 := ih _ (i + 1) hc' 0 (by omega)
    have hts : twoSum p (c 0) (vecSum p m (fun k => c (k + 1)) 0) = (u p ^ i, u p ^ (i + 1)) := by
      rw [hw0, hc, add_zero, add_zero]
      exact twoSum_pow p hp i
    rcases j with _ | _ | j
    · rw [vecSum_succ_zero, hts, add_zero]
    · rw [vecSum_succ_one, hts]
    · rw [vecSum_succ_add_two, ih _ (i + 1) hc' (j + 1) (by omega)]
      ring_nf

/-- the second pass on `uⁱ, uⁱ⁺¹, …, u^{i+b+1}` emits `uⁱ, …, u^{i+b-1}` and ends with `u^{i+b}` -/
theorem renPass_pow (hp : 1 < p) (b : ℕ) : ∀ i : ℕ,
    (renPass p b (u p ^ i) ((List.range (b + 1)).map fun j => u p ^ (i + 1 + j))).sum =
      ∑ j ∈ range (b + 1), u p ^ (i + j) := by
  induction b with
  | zero =>
    intro i
    simp [renPass, twoSum_pow p hp i]
  | succ b ih =>
    intro i
    have hlist : (List.range (b + 1 + 1)).map (fun j => u p ^ (i + 1 + j)) =
        u p ^ (i + 1) :: (List.range (b + 1)).map (fun j => u p ^ (i + 1 + 1 + j)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      exact List.map_congr_left fun j _ => by simp only [Function.comp, Nat.succ_eq_add_one]; ring_nf
    have hts := twoSum_pow p hp i
    have he : (twoSum p (u p ^ i) (u p ^ (i + 1))).2 ≠ 0 := by
      rw [hts]
      exact (pow_pos (u_pos p) _).ne'
    rw [hlist]
    simp only [renPass]
    split_ifs with hc
    · rw [hts]
      simp only [Nat.add_sub_cancel, List.sum_cons]
      rw [ih (i + 1), sum_range_succ' (fun j => u p ^ (i + j)) (b + 1), add_zero, add_comm]
      congr 1
      exact sum_congr rfl fun j _ => by ring_nf
    · exact absurd ⟨by omega, he⟩ hc

theorem renErr_pow (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n) : renErr p n (fun m => u p ^ m) = u p ^ n := by
  have hv := vecSum_pow p hp n (fun m => u p ^ m) 0 (fun k => by simp)
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
  unfold renErr ren
  have hlist : (List.range (b + 1)).map (fun j => vecSum p (b + 1) (fun m => u p ^ m) (j + 1)) =
      (List.range (b + 1)).map (fun j => u p ^ (0 + 1 + j)) :=
    List.map_congr_left fun j hj => by
      rw [hv (j + 1) (by simp at hj; omega)]
      ring_nf
  rw [hlist, hv 0 (by omega), show b + 1 - 1 = b by omega, renPass_pow p hp b 0, sum_range_succ _ (b + 1)]
  simp

/-- Theorem 9 (c): for `c = (1, u, u², …, uⁿ)`, `v = c` and `|E| = B_0 = uⁿ` -/
theorem ren_sharp (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n) :
    (∀ j ≤ n, vecSum p n (fun m => u p ^ m) j = u p ^ j) ∧ |renErr p n (fun m => u p ^ m)| = u p ^ n ∧
      us p ^ n * |vecSum p n (fun m => u p ^ m) 0| +
        ∑ j ∈ Ioc 0 n, us p ^ (n + 1 - j) * |vecSum p n (fun m => u p ^ m) j| = u p ^ n := by
  have hv : ∀ j ≤ n, vecSum p n (fun m => u p ^ m) j = u p ^ j := fun j hj => by
    simpa using vecSum_pow p hp n (fun m => u p ^ m) 0 (fun k => by simp) j hj
  refine ⟨hv, ?_, ?_⟩
  · rw [renErr_pow p hp n hn, abs_of_pos (pow_pos (u_pos p) n)]
  · have hsum : ∑ j ∈ Ioc 0 n, us p ^ (n + 1 - j) * |vecSum p n (fun m => u p ^ m) j| =
        ∑ j ∈ Ioc 0 n, us p ^ (n + 1 - j) * u p ^ j :=
      sum_congr rfl fun j hj => by rw [hv j (mem_Ioc.mp hj).2, abs_of_pos (pow_pos (u_pos p) j)]
    rw [hsum, hv 0 (by omega), pow_zero, abs_one, mul_one]
    exact B0_pow p n

end ExpansionBounds
