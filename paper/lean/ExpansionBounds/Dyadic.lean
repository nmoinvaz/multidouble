import ExpansionBounds.RoundEval

/-!
# Dyadic rationals as pairs

What the kernel evaluates is stored as pairs `(m, k)` for `m/2^k`: the terms of Proposition 28, the coefficients of
the series, and the states of Horner's runs. `dyQ` and `dyFn` read them, and `dyF_of_all` puts data that `rnQ`
leaves as it is in `F p`.
-/

namespace ExpansionBounds

/-- `m/2^k` -/
def dyQ (mk : ℤ × ℕ) : ℚ := mk.1 / 2 ^ mk.2

/-- a list of dyadic rationals as a function, zero past its end -/
def dyFn (l : List (ℤ × ℕ)) : ℕ → ℚ := fun i => dyQ (l.getD i (0, 0))

theorem dyQ_zero : dyQ (0, 0) = 0 := by simp [dyQ]

theorem dyFn_of_le (l : List (ℤ × ℕ)) {i : ℕ} (h : l.length ≤ i) : dyFn l i = 0 := by
  unfold dyFn
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  simp only [Option.getD_none, dyQ_zero]

variable (p : ℤ) [Prec_gt_0 p]

/-- dyadic data that `rnQ` leaves as it is lies in `F p`, as do the zeros past a term's end -/
theorem dyF_of_all (T : List (List (ℤ × ℕ))) (h : ∀ t ∈ T, ∀ q ∈ t, rnQ p (dyQ q) = dyQ q) :
    ∀ t ∈ T, ∀ l, F p (dyFn t l : ℝ) := by
  intro t ht l
  unfold dyFn
  rw [List.getD_eq_getElem?_getD]
  cases hq : t[l]? with
  | none =>
    simp only [Option.getD_none, dyQ_zero, Rat.cast_zero]
    exact F_zero p
  | some q =>
    simp only [Option.getD_some]
    exact (F_iff_rn p _).mpr (h t ht q (List.mem_of_getElem? hq))

end ExpansionBounds
