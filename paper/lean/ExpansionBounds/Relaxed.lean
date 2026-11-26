import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The squares of `series::Relaxed` cover each term once

`Relaxed::step(e)` forms, for the least side `s_0 = 2^a`, the squares of side `s = 2^p ≥ s_0` with `(m + 1)s = e - 1`,
`m ≥ 1`: the indices `i ∈ [ms + 1, (m + 1)s]`, `j ∈ [s + 1, 2s]` of the terms `x_i y_j`, and for `m ≥ 2` the transpose
(`relStep`). Each term with `i, j ≥ s_0 + 1` lies in exactly one square of one step (`relaxed_cover`): with
`i' = i - 1`, `j' = j - 1`, the square of side `2^{⌊log₂ j'⌋}` where `⌊log₂ i'⌋ ≥ ⌊log₂ j'⌋`, and otherwise the
transpose of side `2^{⌊log₂ i'⌋}`. A square of step `e` takes coefficients below `e` and gives terms of order at least
`e + 1` (`relStep_terms`), so it is formed before its terms are read. `Relaxed::sum` adds the terms with `i < d` or
`j < d`, `d = s_0 + 1`, directly, two ranges that do not meet for `k ≥ 2d` (`relaxed_direct`).
-/

namespace ExpansionBounds

/-- the squares of step `e` as `(s, m, transposed)`: for each side `s = 2^{a+k}` with `2s ≤ e - 1` and `s | e - 1`,
`m = (e - 1)/s - 1`, the square and, for `m ≥ 2`, its transpose -/
def relStep (a e : ℕ) : List (ℕ × ℕ × Bool) :=
  (List.range e).flatMap fun k =>
    if 2 * 2 ^ (a + k) ≤ e - 1 ∧ (e - 1) % 2 ^ (a + k) = 0 then
      (2 ^ (a + k), (e - 1) / 2 ^ (a + k) - 1, false) ::
        (if 2 ≤ (e - 1) / 2 ^ (a + k) - 1 then [(2 ^ (a + k), (e - 1) / 2 ^ (a + k) - 1, true)] else [])
    else []

/-- the term `x_i y_j` lies in the square `(s, m, t)` -/
def relCovers (q : ℕ × ℕ × Bool) (i j : ℕ) : Prop :=
  if q.2.2 then q.1 + 1 ≤ i ∧ i ≤ 2 * q.1 ∧ q.2.1 * q.1 + 1 ≤ j ∧ j ≤ q.2.1 * q.1 + q.1
  else q.2.1 * q.1 + 1 ≤ i ∧ i ≤ q.2.1 * q.1 + q.1 ∧ q.1 + 1 ≤ j ∧ j ≤ 2 * q.1

instance (q : ℕ × ℕ × Bool) (i j : ℕ) : Decidable (relCovers q i j) := by
  unfold relCovers
  infer_instance

/-- the squares of step `e` are those of side `2^p`, `p ≥ a`, with `e = (m + 1)2^p + 1`, `m ≥ 1`, and `m ≥ 2` for a
transpose -/
theorem mem_relStep (a e s m : ℕ) (t : Bool) :
    (s, m, t) ∈ relStep a e ↔
      ∃ p, a ≤ p ∧ s = 2 ^ p ∧ 1 ≤ m ∧ e = (m + 1) * s + 1 ∧ (t = true → 2 ≤ m) := by
  unfold relStep
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨k, -, hk⟩
    by_cases hc : 2 * 2 ^ (a + k) ≤ e - 1 ∧ (e - 1) % 2 ^ (a + k) = 0
    · rw [ite_eq_left hc] at hk
      have hs : 0 < 2 ^ (a + k) := by positivity
      obtain ⟨h2, hd⟩ := hc
      have hq : 2 ≤ (e - 1) / 2 ^ (a + k) := (Nat.le_div_iff_mul_le hs).mpr (by linarith)
      have he : (e - 1) / 2 ^ (a + k) * 2 ^ (a + k) = e - 1 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hd)
      have key : ∀ t' : Bool, (s, m, t) = (2 ^ (a + k), (e - 1) / 2 ^ (a + k) - 1, t') →
          (t' = true → 2 ≤ (e - 1) / 2 ^ (a + k) - 1) →
            ∃ p, a ≤ p ∧ s = 2 ^ p ∧ 1 ≤ m ∧ e = (m + 1) * s + 1 ∧ (t = true → 2 ≤ m) := by
        intro t' h ht'
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨a + k, by omega, rfl, by omega, ?_, ht'⟩
        have : (e - 1) / 2 ^ (a + k) - 1 + 1 = (e - 1) / 2 ^ (a + k) := by omega
        rw [this, he]
        omega
      rcases List.mem_cons.mp hk with h | h
      · exact key false h (by simp)
      · by_cases hm : 2 ≤ (e - 1) / 2 ^ (a + k) - 1
        · rw [ite_eq_left hm] at h
          exact key true (List.mem_singleton.mp h) (fun _ => hm)
        · rw [ite_eq_right hm] at h
          simp at h
    · rw [ite_eq_right hc] at hk
      simp at hk
  · rintro ⟨p, hap, rfl, hm, rfl, ht⟩
    have hs : 0 < 2 ^ p := by positivity
    have h2p : p < 2 ^ p := Nat.lt_two_pow_self
    have hle : 2 ^ p ≤ (m + 1) * 2 ^ p := Nat.le_mul_of_pos_left _ (by omega)
    refine ⟨p - a, List.mem_range.mpr (by omega), ?_⟩
    have hp : a + (p - a) = p := by omega
    rw [hp, Nat.add_sub_cancel, Nat.mul_div_cancel _ hs, Nat.add_sub_cancel]
    have hc : 2 * 2 ^ p ≤ (m + 1) * 2 ^ p ∧ (m + 1) * 2 ^ p % 2 ^ p = 0 :=
      ⟨Nat.mul_le_mul_right _ (by omega), Nat.mul_mod_left _ _⟩
    rw [ite_eq_left hc]
    cases t
    · exact List.mem_cons_self
    · rw [ite_eq_left (ht rfl)]
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem log2_eq_of_bounds {n p : ℕ} (h1 : 2 ^ p ≤ n) (h2 : n < 2 ^ (p + 1)) : Nat.log2 n = p := by
  have hn : n ≠ 0 := by have : 0 < 2 ^ p := by positivity
                        omega
  have a1 := Nat.log2_self_le hn
  have a2 := Nat.lt_log2_self (n := n)
  rcases lt_trichotomy (Nat.log2 n) p with h | h | h
  · have : 2 ^ (Nat.log2 n + 1) ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · exact h
  · have : 2 ^ (p + 1) ≤ 2 ^ Nat.log2 n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem le_log2 {n a : ℕ} (h : 2 ^ a ≤ n) : a ≤ Nat.log2 n := by
  have hn : n ≠ 0 := by have : 0 < 2 ^ a := by positivity
                        omega
  by_contra hc
  have := Nat.lt_log2_self (n := n)
  have : 2 ^ (Nat.log2 n + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- the square at `(ms + 1, s + 1)` of side `s` holds `(i, j)` exactly where `m = ⌊(i - 1)/s⌋` and
`s ≤ j - 1 < 2s` -/
theorem covers_iff {s m i : ℕ} (hs : 0 < s) (hi : 1 ≤ i) :
    (m * s + 1 ≤ i ∧ i ≤ m * s + s) ↔ m = (i - 1) / s := by
  constructor
  · rintro ⟨h1, h2⟩
    exact (Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul, one_mul]; omega)).symm
  · rintro rfl
    have h1 := Nat.div_mul_le_self (i - 1) s
    have h2 := Nat.lt_div_mul_add (a := i - 1) hs
    constructor <;> omega

/-- each term `x_i y_j` with `i, j ≥ 2^a + 1` lies in exactly one square of one step -/
theorem relaxed_cover (a i j : ℕ) (hi : 2 ^ a + 1 ≤ i) (hj : 2 ^ a + 1 ≤ j) :
    ∃! q : ℕ × (ℕ × ℕ × Bool), q.2 ∈ relStep a q.1 ∧ relCovers q.2 i j := by
  set I := i - 1 with hI
  set J := j - 1 with hJ
  have hIa : 2 ^ a ≤ I := by omega
  have hJa : 2 ^ a ≤ J := by omega
  have hI0 : I ≠ 0 := by have : 0 < 2 ^ a := by positivity
                         omega
  have hJ0 : J ≠ 0 := by have : 0 < 2 ^ a := by positivity
                         omega
  set P := Nat.log2 I
  set Q := Nat.log2 J
  have hP1 : 2 ^ P ≤ I := Nat.log2_self_le hI0
  have hP2 : I < 2 ^ (P + 1) := Nat.lt_log2_self
  have hQ1 : 2 ^ Q ≤ J := Nat.log2_self_le hJ0
  have hQ2 : J < 2 ^ (Q + 1) := Nat.lt_log2_self
  have haP : a ≤ P := le_log2 hIa
  have haQ : a ≤ Q := le_log2 hJa
  rcases le_or_gt Q P with hQP | hPQ
  · -- the square of side `2^Q`
    have hs : 0 < 2 ^ Q := by positivity
    have hsI : 2 ^ Q ≤ I := le_trans (Nat.pow_le_pow_right (by norm_num) hQP) hP1
    have hm : 1 ≤ I / 2 ^ Q := (Nat.le_div_iff_mul_le hs).mpr (by omega)
    refine ⟨((I / 2 ^ Q + 1) * 2 ^ Q + 1, (2 ^ Q, I / 2 ^ Q, false)), ⟨?_, ?_⟩, ?_⟩
    · exact (mem_relStep a _ _ _ _).mpr ⟨Q, haQ, rfl, hm, rfl, by simp⟩
    · simp only [relCovers, Bool.false_eq_true, ↓reduceIte]
      have := (covers_iff (m := I / 2 ^ Q) hs (by omega : 1 ≤ i)).mpr rfl
      rw [pow_succ] at hQ2
      exact ⟨this.1, this.2, by omega, by omega⟩
    · rintro ⟨e', s', m', t'⟩ ⟨hmem, hcov⟩
      obtain ⟨p', hap', rfl, hm', rfl, ht'⟩ := (mem_relStep a _ _ _ _).mp hmem
      have hs' : 0 < 2 ^ p' := by positivity
      cases t'
      · simp only [relCovers, Bool.false_eq_true, ↓reduceIte] at hcov
        obtain ⟨c1, c2, c3, c4⟩ := hcov
        have hp' : Q = p' := log2_eq_of_bounds (by omega) (by rw [pow_succ]; omega)
        subst hp'
        have hm'' : m' = I / 2 ^ Q := (covers_iff hs (by omega : 1 ≤ i)).mp ⟨c1, c2⟩
        subst hm''
        rfl
      · -- a transpose would need `⌊log₂ j'⌋ > ⌊log₂ i'⌋`
        simp only [relCovers, ↓reduceIte] at hcov
        obtain ⟨c1, c2, c3, c4⟩ := hcov
        have hp' : P = p' := log2_eq_of_bounds (by omega) (by rw [pow_succ]; omega)
        have hm2 := ht' rfl
        have hJ2 : 2 ^ (p' + 1) ≤ J := by
          have : 2 * 2 ^ p' ≤ m' * 2 ^ p' := Nat.mul_le_mul_right _ hm2
          rw [pow_succ]
          omega
        have := le_log2 hJ2
        omega
  · -- the transpose of side `2^P`
    have hs : 0 < 2 ^ P := by positivity
    have hsJ : 2 ^ (P + 1) ≤ J := le_trans (Nat.pow_le_pow_right (by norm_num) hPQ) hQ1
    have hm : 2 ≤ J / 2 ^ P := (Nat.le_div_iff_mul_le hs).mpr (by rw [pow_succ] at hsJ; omega)
    refine ⟨((J / 2 ^ P + 1) * 2 ^ P + 1, (2 ^ P, J / 2 ^ P, true)), ⟨?_, ?_⟩, ?_⟩
    · exact (mem_relStep a _ _ _ _).mpr ⟨P, haP, rfl, by omega, rfl, fun _ => hm⟩
    · simp only [relCovers, ↓reduceIte]
      have := (covers_iff (m := J / 2 ^ P) hs (by omega : 1 ≤ j)).mpr rfl
      rw [pow_succ] at hP2
      exact ⟨by omega, by omega, this.1, this.2⟩
    · rintro ⟨e', s', m', t'⟩ ⟨hmem, hcov⟩
      obtain ⟨p', hap', rfl, hm', rfl, ht'⟩ := (mem_relStep a _ _ _ _).mp hmem
      have hs' : 0 < 2 ^ p' := by positivity
      cases t'
      · -- a square would need `⌊log₂ i'⌋ ≥ ⌊log₂ j'⌋`
        simp only [relCovers, Bool.false_eq_true, ↓reduceIte] at hcov
        obtain ⟨c1, c2, c3, c4⟩ := hcov
        have hp' : Q = p' := log2_eq_of_bounds (by omega) (by rw [pow_succ]; omega)
        have hI2 : 2 ^ p' ≤ I := by
          have : 1 * 2 ^ p' ≤ m' * 2 ^ p' := Nat.mul_le_mul_right _ hm'
          omega
        have := le_log2 hI2
        omega
      · simp only [relCovers, ↓reduceIte] at hcov
        obtain ⟨c1, c2, c3, c4⟩ := hcov
        have hp' : P = p' := log2_eq_of_bounds (by omega) (by rw [pow_succ]; omega)
        subst hp'
        have hm'' : m' = J / 2 ^ P := (covers_iff hs (by omega : 1 ≤ j)).mp ⟨c3, c4⟩
        subst hm''
        rfl

/-- a square of step `e` takes coefficients below `e` and gives terms of order at least `e + 1` -/
theorem relStep_terms {a e i j : ℕ} {q : ℕ × ℕ × Bool} (hq : q ∈ relStep a e) (hc : relCovers q i j) :
    e + 1 ≤ i + j ∧ i < e ∧ j < e := by
  obtain ⟨s, m, t⟩ := q
  obtain ⟨p, -, rfl, hm, rfl, -⟩ := (mem_relStep a e _ _ _).mp hq
  have hle : 2 ^ p ≤ m * 2 ^ p := by
    have := Nat.mul_le_mul_right (2 ^ p) hm
    omega
  have hexp : (m + 1) * 2 ^ p = m * 2 ^ p + 2 ^ p := by ring
  rw [hexp]
  cases t <;> simp only [relCovers, Bool.false_eq_true, ↓reduceIte] at hc <;>
    (generalize m * 2 ^ p = X at *; omega)

/-- `Relaxed::sum` at order `k ≥ 2d` over `lo ≤ d` to `hi ≥ k - d`: each index lies in exactly one of the direct
ranges `[lo, d - 1]` and `[k + 1 - d, hi]` or in the squares' range `[d, k - d]`, which lies within `[lo, hi]` -/
theorem relaxed_direct {d k lo hi i : ℕ} (hk : 2 * d ≤ k) (hlo : lo ≤ d) (hhi : k ≤ hi + d) :
    ((lo ≤ i ∧ i ≤ hi) ↔ ((lo ≤ i ∧ i < d) ∨ (d ≤ i ∧ i + d ≤ k) ∨ (k + 1 ≤ i + d ∧ i ≤ hi))) ∧
      ¬ ((i < d ∧ d ≤ i) ∨ (i < d ∧ k + 1 ≤ i + d) ∨ (i + d ≤ k ∧ k + 1 ≤ i + d)) := by
  omega

end ExpansionBounds
