import ExpansionBounds.ExpRed

/-!
# The double-word operations of Proposition 44 (`prop:ddexplog`), as hypotheses

`DD::exp` and `DD::ln` run EXP and LOG on double words with four operations of Joldes, Muller and Popescu (2017):
AccurateDWPlusDW (their Algorithm 6, the ADD), DWPlusFP (Algorithm 4, the ADDF), DWTimesFP3 (Algorithm 9, the MULF) and
DWTimesDW2 (Algorithm 11, the MUL). Proposition 44 uses of each only that it returns a double word within a relative
error of its exact result: `e_A = 3u²/(1 - 4u)`, `e_F = 2u²`, `e_M = 2u²` and `e_P = 5u²/(1 + u)²`.

Here the four operations are functions on pairs (`DWOps`) and these bounds are hypotheses on them (`DWSpec`), as the
bounds of the double-word start are hypotheses of Theorem 22 in `SqrtDD.lean`. The exponent range is unbounded, which
is (A2′) for the four operations: none of them loses anything to the subnormals, and `η_0` enters only where a scaling
by a power of two or the start's quotient rounds.
-/

namespace ExpansionBounds

variable (p : ℤ)

/-- a double word `(x_h, x_l)`: two floats with `x_h = RN(x_h + x_l)`, as `FastTwoSum` returns them -/
def DW (x : ℝ × ℝ) : Prop := F p x.1 ∧ F p x.2 ∧ RN p (x.1 + x.2) = x.1

/-- the value `x_h + x_l` of a pair -/
def dwVal (x : ℝ × ℝ) : ℝ := x.1 + x.2

/-- `e_A = 3u²/(1 - 4u)`, the relative error of AccurateDWPlusDW (Theorem 3.1 of Joldes, Muller and Popescu) -/
noncomputable def eA : ℝ := 3 * u p ^ 2 / (1 - 4 * u p)

/-- `e_F = 2u²`, the relative error of DWPlusFP -/
noncomputable def eF : ℝ := 2 * u p ^ 2

/-- `e_M = 2u²`, the relative error of DWTimesFP3 -/
noncomputable def eM : ℝ := 2 * u p ^ 2

/-- `e_P = 5u²/(1 + u)²`, the relative error of DWTimesDW2 (Muller and Rideau, 2022) -/
noncomputable def eP : ℝ := 5 * u p ^ 2 / (1 + u p) ^ 2

/-- the four double-word operations: `add` is AccurateDWPlusDW (ADD), `addF` DWPlusFP (ADDF), `mulF` DWTimesFP3 (MULF)
and `mul` DWTimesDW2 (MUL) -/
structure DWOps where
  /-- AccurateDWPlusDW, the sum of two double words -/
  add : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ
  /-- DWPlusFP, the sum of a double word and a float -/
  addF : ℝ × ℝ → ℝ → ℝ × ℝ
  /-- DWTimesFP3, the product of a double word by a float -/
  mulF : ℝ × ℝ → ℝ → ℝ × ℝ
  /-- DWTimesDW2, the product of two double words -/
  mul : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ

/-- the published bounds, as hypotheses: on double words, and floats for the second operand of `addF` and `mulF`, each
operation returns a double word within `e_OP` of its exact result, relatively -/
structure DWSpec (O : DWOps) : Prop where
  add_dw : ∀ x y, DW p x → DW p y → DW p (O.add x y)
  add_err : ∀ x y, DW p x → DW p y → |dwVal (O.add x y) - (dwVal x + dwVal y)| ≤ eA p * |dwVal x + dwVal y|
  addF_dw : ∀ x y, DW p x → F p y → DW p (O.addF x y)
  addF_err : ∀ x y, DW p x → F p y → |dwVal (O.addF x y) - (dwVal x + y)| ≤ eF p * |dwVal x + y|
  mulF_dw : ∀ x y, DW p x → F p y → DW p (O.mulF x y)
  mulF_err : ∀ x y, DW p x → F p y → |dwVal (O.mulF x y) - dwVal x * y| ≤ eM p * |dwVal x * y|
  mul_dw : ∀ x y, DW p x → DW p y → DW p (O.mul x y)
  mul_err : ∀ x y, DW p x → DW p y → |dwVal (O.mul x y) - dwVal x * dwVal y| ≤ eP p * |dwVal x * dwVal y|

/-- `e_F ≥ 0` -/
theorem eF_nonneg : 0 ≤ eF p := by
  unfold eF
  positivity

/-- `e_M ≥ 0` -/
theorem eM_nonneg : 0 ≤ eM p := by
  unfold eM
  positivity

/-- `e_P ≥ 0` -/
theorem eP_nonneg : 0 ≤ eP p := by
  unfold eP
  positivity

/-- `e_A ≥ 0` where `4u < 1` -/
theorem eA_nonneg (hu : 4 * u p < 1) : 0 ≤ eA p := by
  unfold eA
  exact div_nonneg (by positivity) (by linarith)

/-- an operation within `e` of its exact result `Z`, relatively, with `|Z| ≤ Z̄`: its error is at most `e Z̄`, the
proposition's reading of `G_OP`, and its result at most `Z̄ + e Z̄` -/
theorem dw_err_le {e v Z Zb : ℝ} (he : 0 ≤ e) (h : |v - Z| ≤ e * |Z|) (hZ : |Z| ≤ Zb) :
    |v - Z| ≤ e * Zb ∧ |v| ≤ Zb + e * Zb := by
  have h1 : |v - Z| ≤ e * Zb := h.trans (mul_le_mul_of_nonneg_left hZ he)
  refine ⟨h1, ?_⟩
  calc |v| = |Z + (v - Z)| := by ring_nf
    _ ≤ |Z| + |v - Z| := abs_add_le _ _
    _ ≤ Zb + e * Zb := add_le_add hZ h1

end ExpansionBounds
