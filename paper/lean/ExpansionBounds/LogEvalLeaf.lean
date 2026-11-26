import ExpansionBounds.LogEvalCert

/-!
# The exponentials of Theorem 42's bound on rational arguments

`logBoundC_cert` takes rational bounds of `ξ`, of `φ̄` and of the three combinations of exponentials of step (4).
Here they are, on the enclosure of `e^z` by 16 terms of its series for `|z| ≤ 1` (`exp_enclosure`): `logXiQ`,
`logPhiBQ`, `logXsQ`, `logCsQ` and `logXdQ` at rational bounds of `E`, `a`, `b` and `δ` are at least `ξ`, the convex
`φ̄`, `2(e^{b̂} - 1 - b̂) + e^{b̂}(e^{E+δ} - 1)`, `e^E - 1` and `e^E(e^δ - 1)`.
-/

namespace ExpansionBounds

/-- `ξ` on the enclosure of `e^z`, at rational bounds of `E`, `b`, `δ` from above and of `a` from below -/
def logXiQ (D : ℚ) (pos : Bool) (E a b δ : ℚ) : ℚ :=
  (if pos then expUpQ (E + δ - a) else expUpQ (E + b + δ)) + D

/-- the convex `φ̄ = max(ξ - 1, E + b + δ + D)` at rational bounds -/
def logPhiBQ (D : ℚ) (pos : Bool) (E a b δ : ℚ) : ℚ := max (logXiQ D pos E a b δ - 1) (E + b + δ + D)

/-- `2(e^{b̂} - 1 - b̂) + e^{b̂}(e^{E+δ} - 1)` on the enclosure of `e^z`, with `b̂ = b + δ` -/
def logXsQ (E b δ : ℚ) : ℚ := 2 * (expUpQ (b + δ) - 1 - (b + δ)) + expUpQ (b + δ) * (expUpQ (E + δ) - 1)

/-- `e^E - 1` on the enclosure of `e^z` -/
def logCsQ (E : ℚ) : ℚ := expUpQ E - 1

/-- `e^E(e^δ - 1)` on the enclosure of `e^z` -/
def logXdQ (E δ : ℚ) : ℚ := expUpQ E * (expUpQ δ - 1)

/-- `e^z ≤ expUpQ z_q` for `z ≤ z_q` and `|z_q| ≤ 1`. -/
theorem exp_le_expUpQ {z : ℝ} {zq : ℚ} (hz : z ≤ ((zq : ℚ) : ℝ)) (h1 : |zq| ≤ 1) :
    Real.exp z ≤ ((expUpQ zq : ℚ) : ℝ) :=
  (Real.exp_le_exp.mpr hz).trans (exp_enclosure zq h1).2

/-- `ξ` is at most `logXiQ` at rational bounds of its arguments. -/
theorem logXi_le {D E a b δ : ℝ} {Dq Eq aq bq δq : ℚ} (hD : D ≤ ((Dq : ℚ) : ℝ)) (hE : E ≤ ((Eq : ℚ) : ℝ))
    (ha : ((aq : ℚ) : ℝ) ≤ a) (hb : b ≤ ((bq : ℚ) : ℝ)) (hδ : δ ≤ ((δq : ℚ) : ℝ)) (pos : Bool)
    (h1 : |Eq + δq - aq| ≤ 1) (h2 : |Eq + bq + δq| ≤ 1) :
    logXi D pos E a b δ ≤ ((logXiQ Dq pos Eq aq bq δq : ℚ) : ℝ) := by
  cases pos with
  | true =>
    simp only [logXi, logXiQ, ↓reduceIte]
    have e := exp_le_expUpQ (z := E + δ - a) (zq := Eq + δq - aq) (by push_cast; linarith) h1
    push_cast
    linarith
  | false =>
    simp only [logXi, logXiQ, Bool.false_eq_true, ↓reduceIte]
    have e := exp_le_expUpQ (z := E + b + δ) (zq := Eq + bq + δq) (by push_cast; linarith) h2
    push_cast
    linarith

/-- The convex `φ̄` is at most `logPhiBQ` at rational bounds of its arguments. -/
theorem logPhiBC_le {D E a b δ : ℝ} {Dq Eq aq bq δq : ℚ} (hD : D ≤ ((Dq : ℚ) : ℝ)) (hE : E ≤ ((Eq : ℚ) : ℝ))
    (ha : ((aq : ℚ) : ℝ) ≤ a) (hb : b ≤ ((bq : ℚ) : ℝ)) (hδ : δ ≤ ((δq : ℚ) : ℝ)) (pos : Bool)
    (h1 : |Eq + δq - aq| ≤ 1) (h2 : |Eq + bq + δq| ≤ 1) :
    logPhiBC D pos E a b δ ≤ ((logPhiBQ Dq pos Eq aq bq δq : ℚ) : ℝ) := by
  have hξ := logXi_le hD hE ha hb hδ pos h1 h2
  simp only [logPhiBC, logPhiBQ]
  rw [Rat.cast_max]
  refine max_le_max ?_ ?_
  · push_cast
    linarith
  · push_cast
    linarith

/-- `e^E - 1` is at most `logCsQ` at a rational bound of `E`. -/
theorem logCs_le {E : ℝ} {Eq : ℚ} (hE : E ≤ ((Eq : ℚ) : ℝ)) (h1 : |Eq| ≤ 1) :
    Real.exp E - 1 ≤ ((logCsQ Eq : ℚ) : ℝ) := by
  have e := exp_le_expUpQ hE h1
  simp only [logCsQ]
  push_cast
  linarith

/-- `e^E(e^δ - 1)` is at most `logXdQ` at rational bounds of `E` and `δ ≥ 0`. -/
theorem logXd_le {E δ : ℝ} {Eq δq : ℚ} (hE : E ≤ ((Eq : ℚ) : ℝ)) (hδ0 : 0 ≤ δ) (hδ : δ ≤ ((δq : ℚ) : ℝ))
    (h1 : |Eq| ≤ 1) (h2 : |δq| ≤ 1) : Real.exp E * (Real.exp δ - 1) ≤ ((logXdQ Eq δq : ℚ) : ℝ) := by
  have e1 := exp_le_expUpQ hE h1
  have e2 := exp_le_expUpQ hδ h2
  have e3 := Real.one_le_exp hδ0
  simp only [logXdQ]
  push_cast
  exact mul_le_mul e1 (by linarith) (by linarith) ((Real.exp_pos E).le.trans e1)

/-- `2(e^{b̂} - 1 - b̂) + e^{b̂}(e^{E+δ} - 1)` is at most `logXsQ` at rational bounds, for `b̂ = b + δ ≥ 0` and
`E + δ ≥ 0`. -/
theorem logXs_le {E b δ : ℝ} {Eq bq δq : ℚ} (hE : E ≤ ((Eq : ℚ) : ℝ)) (hb : b ≤ ((bq : ℚ) : ℝ))
    (hδ : δ ≤ ((δq : ℚ) : ℝ)) (hbδ0 : 0 ≤ b + δ) (hEδ0 : 0 ≤ E + δ) (h1 : |bq + δq| ≤ 1) (h2 : |Eq + δq| ≤ 1) :
    2 * (Real.exp (b + δ) - 1 - (b + δ)) + Real.exp (b + δ) * (Real.exp (E + δ) - 1) ≤
      ((logXsQ Eq bq δq : ℚ) : ℝ) := by
  have hz : b + δ ≤ (((bq + δq : ℚ)) : ℝ) := by
    push_cast
    linarith
  have hw : E + δ ≤ (((Eq + δq : ℚ)) : ℝ) := by
    push_cast
    linarith
  have m1 := expm1_sub_mono hbδ0 hz
  have e1 := (exp_enclosure (bq + δq) h1).2
  have e2 := exp_le_expUpQ hz h1
  have e3 := exp_le_expUpQ hw h2
  have e4 := Real.one_le_exp hEδ0
  have hm := mul_le_mul e2 (by linarith : Real.exp (E + δ) - 1 ≤ ((expUpQ (Eq + δq) : ℚ) : ℝ) - 1) (by linarith)
    ((Real.exp_pos (b + δ)).le.trans e2)
  simp only [logXsQ]
  push_cast at m1 e1 ⊢
  linarith

end ExpansionBounds
