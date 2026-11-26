import ExpansionBounds.Closed
import ExpansionBounds.DDOps
import ExpansionBounds.DWord
import ExpansionBounds.Facts
import ExpansionBounds.Red

/-!
# The greedy expansion of a real number

`recip::ratio_parts` gives `p/q` as its greedy expansion: `r_0 = RN(x)` and `r_i = RN(x - r_0 - ... - r_{i-1})`.
Each part is at most `u` times the one before (`gPart_succ_le`), so the first `n` parts lie on `H(1)`
(`gPart_H`), and they leave at most `u^n (1 + u)|x|` of `x` (`greedy_err`).
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) [Prec_gt_0 p]

/-- what the first `n` greedy parts leave of `x` -/
noncomputable def gRem (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => gRem x n - RN p (gRem x n)

/-- the greedy expansion's part `n`: `RN` of what the parts before it leave of `x` -/
noncomputable def gPart (x : ℝ) (n : ℕ) : ℝ := RN p (gRem p x n)

omit [Prec_gt_0 p] in
theorem gRem_succ (x : ℝ) (n : ℕ) : gRem p x (n + 1) = gRem p x n - gPart p x n := rfl

omit [Prec_gt_0 p] in
/-- `x` is its first `n` parts plus what they leave -/
theorem gRem_sum (x : ℝ) (n : ℕ) : x = ∑ i ∈ range n, gPart p x i + gRem p x n := by
  induction n with
  | zero => simp [gRem]
  | succ n ih => rw [sum_range_succ, gRem_succ]; linarith

theorem F_gPart (x : ℝ) (n : ℕ) : F p (gPart p x n) := F_RN p _

/-- what part `n` leaves is at most `u` times it -/
theorem gRem_succ_le (x : ℝ) (n : ℕ) : |gRem p x (n + 1)| ≤ u p * |gPart p x n| := by
  rw [gRem_succ, abs_sub_comm]
  exact abs_RN_sub_le_u_RN p _

/-- each part is at most `u` times the one before -/
theorem gPart_succ_le (x : ℝ) (n : ℕ) : |gPart p x (n + 1)| ≤ u p * |gPart p x n| := by
  have hc : F p (u p * |gPart p x n|) := by
    have h := F_zpow_mul p (-p) (F_abs p (F_gPart p x n))
    unfold u
    simpa using h
  exact abs_RN_le_of_F p hc (gRem_succ_le p x n)

/-- part `n` is at most `u^n` times the first -/
theorem gPart_le_pow (x : ℝ) (n : ℕ) : |gPart p x n| ≤ u p ^ n * |gPart p x 0| := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc |gPart p x (n + 1)| ≤ u p * |gPart p x n| := gPart_succ_le p x n
      _ ≤ u p * (u p ^ n * |gPart p x 0|) := mul_le_mul_of_nonneg_left ih (u_pos p).le
      _ = u p ^ (n + 1) * |gPart p x 0| := by ring

/-- the first `n` parts lie on `H(1)` -/
theorem gPart_H (n : ℕ) (x : ℝ) : Htheta p n 1 (gPart p x) := by
  intro i _ _
  simpa using gPart_le_pow p x i

/-- the first `n ≥ 1` parts leave at most `u^n (1 + u)|x|` of `x` -/
theorem greedy_err (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    |x - ∑ i ∈ range n, gPart p x i| ≤ u p ^ n * (1 + u p) * |x| := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := gRem_sum p x (m + 1)
  have e : x - ∑ i ∈ range (m + 1), gPart p x i = gRem p x (m + 1) := by linarith
  rw [e]
  have h0 : |gPart p x 0| ≤ (1 + u p) * |x| := abs_RN_le p x
  calc |gRem p x (m + 1)| ≤ u p * |gPart p x m| := gRem_succ_le p x m
    _ ≤ u p * (u p ^ m * |gPart p x 0|) := mul_le_mul_of_nonneg_left (gPart_le_pow p x m) (u_pos p).le
    _ ≤ u p * (u p ^ m * ((1 + u p) * |x|)) := by
      have := (u_pos p).le
      gcongr
    _ = u p ^ (m + 1) * (1 + u p) * |x| := by ring

omit [Prec_gt_0 p] in
/-- a nonzero real lies in a binade: `2^{E + p - 1} ≤ |a| < 2^{E + p}` -/
theorem exists_binade {a : ℝ} (ha : a ≠ 0) :
    ∃ E : ℤ, (2 : ℝ) ^ (E + p - 1) ≤ |a| ∧ |a| < (2 : ℝ) ^ (E + p) := by
  refine ⟨FloatSpec.Core.Raux.mag 2 a - p, ?_, ?_⟩
  · have := FloatSpec.Core.Raux.bpow_mag_le 2 a (by norm_num) ha
    convert this using 2
    ring
  · have := FloatSpec.Core.Raux.bpow_mag_gt 2 a (by norm_num)
    convert this using 2
    ring

/-- above a float `a`, below or at a float `h > a`, lies a float `s` whose distance from `a` is twice a float: the
next float, at the grid of `a`'s binade or, below a negative power of two, of the binade under it -/
theorem exists_next (hp : 1 < p) {a h : ℝ} (ha : F p a) (hh : F p h) (hah : a < h) :
    ∃ s : ℝ, F p s ∧ a < s ∧ s ≤ h ∧ F p ((s - a) / 2) := by
  rcases lt_trichotomy a 0 with hneg | hz | hpos
  · obtain ⟨E, hlo, hhi⟩ := exists_binade p hneg.ne
    have hmA : Mult E a := mult_of_F p ha hlo
    have habs : |a| = -a := abs_of_neg hneg
    have hmA' : Mult E (-a) := by simpa using Mult.sub (⟨0, by simp⟩ : Mult E 0) hmA
    have hE : (0 : ℝ) < (2 : ℝ) ^ E := by positivity
    rcases hlo.lt_or_eq with hgt | heq
    · -- `a` above the bottom of its binade: the next float is `a + 2^E`
      have hmB : Mult E ((2 : ℝ) ^ (E + p - 1)) := Mult.zpow (by omega)
      have hstep := Mult.le_sub hmB hmA' (by rwa [habs] at hgt)
      have hmS : Mult E (a + (2 : ℝ) ^ E) := Mult.add hmA (Mult.zpow le_rfl)
      have hB : (0 : ℝ) < (2 : ℝ) ^ (E + p - 1) := by positivity
      refine ⟨a + (2 : ℝ) ^ E, F_of_mult_le p hmS ?_, by linarith, ?_, ?_⟩
      · rw [abs_of_neg (by linarith)]
        rw [habs] at hhi
        linarith
      · by_contra hlt
        push Not at hlt
        have hmH : Mult E h := mult_of_F p hh (by rw [abs_of_neg (by linarith)]; linarith)
        have := Mult.le_sub hmA hmH hah
        linarith
      · have := F_two_zpow p (E - 1)
        convert this using 1
        rw [zpow_sub₀ two_ne_zero, zpow_one]
        ring
    · -- `a = -2^{E + p - 1}`: the next float is `a + 2^{E - 1}`, on the grid of the binade below
      have hmA1 : Mult (E - 1) a := hmA.mono (by omega)
      have hmS : Mult (E - 1) (a + (2 : ℝ) ^ (E - 1)) := Mult.add hmA1 (Mult.zpow le_rfl)
      have ha' : a = -(2 : ℝ) ^ (E + p - 1) := by rw [heq, habs]; ring
      have h2 : (2 : ℝ) ^ (E + p - 1) = 2 * (2 : ℝ) ^ (E + p - 2) := by
        rw [show E + p - 1 = (E + p - 2) + 1 by ring, zpow_add_one₀ two_ne_zero]; ring
      have h3 : (2 : ℝ) ^ (E - 1) ≤ (2 : ℝ) ^ (E + p - 2) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h4 : (2 : ℝ) ^ (E - 1 + p) = (2 : ℝ) ^ (E + p - 1) := by ring_nf
      have h5 : (0 : ℝ) < (2 : ℝ) ^ (E - 1) := by positivity
      refine ⟨a + (2 : ℝ) ^ (E - 1), F_of_mult_le p hmS ?_, by linarith, ?_, ?_⟩
      · rw [abs_of_neg (by linarith), h4]
        linarith
      · by_contra hlt
        push Not at hlt
        have hmH : Mult (E - 1) h := mult_of_F p hh (by
          rw [abs_of_neg (by linarith), show E - 1 + p - 1 = E + p - 2 by ring]
          linarith)
        have := Mult.le_sub hmA1 hmH hah
        linarith
      · have := F_two_zpow p (E - 2)
        convert this using 1
        rw [show E - 2 = (E - 1) - 1 by ring, zpow_sub₀ two_ne_zero (E - 1) 1, zpow_one]
        ring
  · subst hz
    refine ⟨h, hh, hah, le_rfl, ?_⟩
    have := F_zpow_mul p (-1) hh
    simpa [div_eq_mul_inv, zpow_neg, zpow_one, mul_comm] using this
  · obtain ⟨E, hlo, hhi⟩ := exists_binade p hpos.ne'
    have hmA : Mult E a := mult_of_F p ha hlo
    have hmS : Mult E (a + (2 : ℝ) ^ E) := Mult.add hmA (Mult.zpow le_rfl)
    have habs : |a| = a := abs_of_pos hpos
    have hmT : Mult E ((2 : ℝ) ^ (E + p)) := Mult.zpow (by omega)
    have htop := Mult.le_sub hmA hmT (by rwa [habs] at hhi)
    have hmH : Mult E h := mult_of_F p hh (by
      rw [abs_of_pos (hpos.trans hah)]; rw [habs] at hlo; linarith)
    have hnext := Mult.le_sub hmA hmH hah
    have hE : (0 : ℝ) < (2 : ℝ) ^ E := by positivity
    refine ⟨a + (2 : ℝ) ^ E, F_of_mult_le p hmS ?_, by linarith, by linarith, ?_⟩
    · rw [abs_of_pos (by linarith)]
      linarith
    · have := F_two_zpow p (E - 1)
      convert this using 1
      rw [zpow_sub₀ two_ne_zero, zpow_one]
      ring

/-- where `x` and `y` round to floats `a < b`, some float is within `|x - y|` of `x - a` -/
theorem near_of_lt (hp : 1 < p) {x y : ℝ} (hxy : RN p x < RN p y) :
    ∃ g : ℝ, F p g ∧ |(x - RN p x) - g| ≤ |x - y| := by
  set a := RN p x with ha_def
  set b := RN p y with hb_def
  have hFa : F p a := F_RN p x
  have hFb : F p b := F_RN p y
  -- `x` is no farther from `a` than from `b`, and `y` no farther from `b` than from `a`
  have hx : (a - x) ^ 2 ≤ (b - x) ^ 2 := sq_le_sq.mpr ((RN_nearest p x).2 b hFb)
  have hy : (b - y) ^ 2 ≤ (a - y) ^ 2 := sq_le_sq.mpr ((RN_nearest p y).2 a hFa)
  have hx2 : 2 * x ≤ a + b := by nlinarith
  have hy2 : a + b ≤ 2 * y := by nlinarith
  rcases le_or_gt x a with hxa | hxa
  · refine ⟨0, F_zero p, ?_⟩
    rw [sub_zero, abs_of_nonpos (by linarith), abs_of_neg (by linarith)]
    linarith
  · obtain ⟨s, hFs, has, hsb, hFg⟩ := exists_next p hp hFa hFb hxy
    have hxs : (a - x) ^ 2 ≤ (s - x) ^ 2 := sq_le_sq.mpr ((RN_nearest p x).2 s hFs)
    have hx3 : 2 * x ≤ a + s := by nlinarith
    refine ⟨(s - a) / 2, hFg, ?_⟩
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- where `x` and `y` round to different floats, some float is within `|x - y|` of `x - RN(x)` -/
theorem near_of_ne (hp : 1 < p) {x y : ℝ} (hxy : RN p x ≠ RN p y) :
    ∃ g : ℝ, F p g ∧ |(x - RN p x) - g| ≤ |x - y| := by
  rcases lt_or_gt_of_ne hxy with h | h
  · exact near_of_lt p hp h
  · have h' : RN p (-x) < RN p (-y) := by rw [RN_neg, RN_neg]; linarith
    obtain ⟨g, hg, hle⟩ := near_of_lt p hp h'
    refine ⟨-g, F_neg p hg, ?_⟩
    rw [RN_neg] at hle
    calc |(x - RN p x) - -g| = |(-x - -RN p x) - g| := by rw [← abs_neg]; ring_nf
      _ ≤ |-x - -y| := hle
      _ = |x - y| := by rw [← abs_neg]; ring_nf

/-- a two-sum of floats is a double word of their sum -/
theorem twoSum_dw (hp : 1 < p) {a b : ℝ} (ha : F p a) (hb : F p b) :
    DW p (twoSum p a b) ∧ (twoSum p a b).1 + (twoSum p a b).2 = a + b := by
  have hs := twoSum_add p hp ha hb
  refine ⟨⟨F_twoSum_fst p a b, F_twoSum_snd p a b, ?_⟩, hs⟩
  rw [hs]
  rfl

/-- the first two greedy parts are as near `x` as any double word -/
theorem greedy_dw_nearest (hp : 1 < p) (x : ℝ) {h l : ℝ} (hd : DW p (h, l)) :
    |x - (gPart p x 0 + gPart p x 1)| ≤ |x - (h + l)| := by
  have h0 : gPart p x 0 = RN p x := rfl
  have h1 : gPart p x 1 = RN p (x - RN p x) := rfl
  have hl : |x - (gPart p x 0 + gPart p x 1)| = |RN p (x - RN p x) - (x - RN p x)| := by
    rw [h0, h1, ← abs_neg]; ring_nf
  rw [hl]
  obtain ⟨-, hFl, hrn⟩ := hd
  by_cases hha : h = RN p x
  · have := (RN_nearest p (x - RN p x)).2 l hFl
    calc |RN p (x - RN p x) - (x - RN p x)| ≤ |l - (x - RN p x)| := this
      _ = |x - (h + l)| := by rw [hha, ← abs_neg]; ring_nf
  · have hne : RN p x ≠ RN p (h + l) := by rw [hrn]; exact Ne.symm hha
    obtain ⟨g, hg, hle⟩ := near_of_ne p hp hne
    calc |RN p (x - RN p x) - (x - RN p x)| ≤ |g - (x - RN p x)| := (RN_nearest p _).2 g hg
      _ = |(x - RN p x) - g| := abs_sub_comm _ _
      _ ≤ |x - (h + l)| := hle

/-- the double-double greedy constant: the two-sum of the first two parts is a double word, within
`u^2 (1 + u)|x|` of `x`, and no double word is nearer `x` -/
theorem greedy_dd (hp : 1 < p) (x : ℝ) :
    DW p (twoSum p (gPart p x 0) (gPart p x 1)) ∧
      |x - ((twoSum p (gPart p x 0) (gPart p x 1)).1 + (twoSum p (gPart p x 0) (gPart p x 1)).2)| ≤
        u p ^ 2 * (1 + u p) * |x| ∧
      ∀ h l : ℝ, DW p (h, l) →
        |x - ((twoSum p (gPart p x 0) (gPart p x 1)).1 + (twoSum p (gPart p x 0) (gPart p x 1)).2)| ≤
          |x - (h + l)| := by
  obtain ⟨hdw, hsum⟩ := twoSum_dw p hp (F_gPart p x 0) (F_gPart p x 1)
  have he := greedy_err p x 2 (by norm_num)
  simp only [sum_range_succ, sum_range_zero, zero_add] at he
  refine ⟨hdw, ?_, fun h l hd => ?_⟩
  · rw [hsum]; exact he
  · rw [hsum]; exact greedy_dw_nearest p hp x hd

end ExpansionBounds
