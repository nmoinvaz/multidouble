import ExpansionBounds.LogConvexBound
import ExpansionBounds.LogRange

/-!
# Theorem 42 for a case on an interval of `ℓ`, by its chord

Theorem 42's proof (`thm:log`), paragraph "Convexity": for a fixed case the convex variant of `𝓔` is convex in
`ℓ = |ln x|` on an interval `[ℓ₁, ℓ₂]`, so two values at the ends that lie below `Φ + εℓ` put it below `Φ + εℓ` on
the interval. `thm42_chord` joins this to `thm42_case_ladder`: for a run of LOG in the case, with `|ln x|` in the
interval, `|y - ln x| ≤ ε|ln x| + Φ`. `Φ = 0` is the paper's chord on `[ℓ₁, ℓ₂]` with `ℓ₁ > 0`, and `ℓ₁ = 0` its
chord from `𝓔(0)`. The hypotheses `b' < d' + 2`, `e^{b'} ≤ 2` where the scaling can round, `C < 1` and
`b + E + δ ≤ 3/5` are asked at `ℓ₂` only, of the convex variants, which grow with `ℓ`.
-/

namespace ExpansionBounds

open Finset Set

variable (p : ℤ) [Prec_gt_0 p] (n : ℕ)

/-- Theorem 42 (`thm:log`) for a case on an interval, by the chord of the paragraph "Convexity": with the start's
bound `E`, the case's `b` and `δ` and the part bounds `π`, `π^y`, `π^x` nonnegative, nondecreasing and convex
functions of `ℓ` on `[ℓ₁, ℓ₂]`, `0 ≤ ℓ₁`, that bound the run's quantities at `ℓ = |ln x|`, and the convex variant of
`𝓔` at most `Φ + εℓ` at both ends, LOG's result satisfies `|y - ln x| ≤ Φ + ε|ln x|`. The scaling of step (3) need
keep `2^k x_0` only where it lies in `[1/2, 2]`, which Lemma 41's range proves -/
theorem thm42_chord (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {η₁ η₂ ηx ηp ηc : ℝ}
    {S₁ S₂ Sx Sp Sc : ℝ → ℝ} (hS₁ : Scl p η₁ S₁) (hS₂ : Scl p η₂ S₂) (hSx : Scl p ηx Sx) (hSp : Scl p ηp Sp)
    (hSc : Scl p ηc Sc) (x : ℕ → ℝ)
    (hx : ∀ i < n, F p (x i)) (hX0 : 0 < ∑ i ∈ range n, x i) (θ : ℝ) (hθ : 0 ≤ θ) (hρ : θ * u p ≤ 1 / 100)
    (hH : Htheta p n θ x) (y0 : ℕ → ℝ) (hy0 : ∀ i < n, F p (y0 i))
    {l₁ l₂ : ℝ} (h0 : 0 ≤ l₁) (hl : |Real.log (∑ i ∈ range n, x i)| ∈ Icc l₁ l₂)
    {E b δ : ℝ → ℝ} {πy π πx : ℝ → ℕ → ℝ} (hEc : Cvx (Icc l₁ l₂) E) (hbc : Cvx (Icc l₁ l₂) b)
    (hδc : Cvx (Icc l₁ l₂) δ) (hπyc : ∀ i, Cvx (Icc l₁ l₂) fun l => πy l i)
    (hπc : ∀ i, Cvx (Icc l₁ l₂) fun l => π l i) (hπxc : ∀ i, Cvx (Icc l₁ l₂) fun l => πx l i)
    (hπy : ∀ i < n, |y0 i| ≤ πy |Real.log (∑ i ∈ range n, x i)| i)
    (hE : |∑ i ∈ range n, y0 i - Real.log (∑ i ∈ range n, x i)| ≤ E |Real.log (∑ i ∈ range n, x i)|)
    (r : ℕ → ℝ) (hr : ∀ i < n, F p (r i)) (k : ℤ)
    (hδ : |∑ i ∈ range n, r i - (-∑ i ∈ range n, y0 i - k * Real.log 2)| ≤ δ |Real.log (∑ i ∈ range n, x i)|)
    (a : ℝ) (ha : a ≤ |∑ i ∈ range n, r i|) (hb : |∑ i ∈ range n, r i| ≤ b |Real.log (∑ i ∈ range n, x i)|)
    (hc : b l₂ + E l₂ + δ l₂ ≤ 3 / 5) (hπ : ∀ i < n, |r i| ≤ π |Real.log (∑ i ∈ range n, x i)| i)
    (pos : Bool) (hsgn : if pos then 0 ≤ ∑ i ∈ range n, r i else ∑ i ∈ range n, r i ≤ 0)
    (e : ℤ) (hU : ∑ i ∈ range n, |r i| < (2 : ℝ) ^ (e + 1)) (m d' : ℕ) (hd : 1 ≤ d')
    (hbd : coreBpC n m (b l₂) η₁ < d' + 2) (hb2 : 0 < η₁ → Real.exp (coreBpC n m (b l₂) η₁) ≤ 2)
    (Fk : ℕ → ℕ → ℝ) (hF : ∀ k, ∀ i < n, F p (Fk k i))
    (φF : ℕ → ℝ) (hφF : ∀ k, |∑ i ∈ range n, Fk k i - invF k| ≤ φF k)
    (hπx : ∀ i < n, |Sx ((2 : ℝ) ^ k * x i)| ≤ πx |Real.log (∑ i ∈ range n, x i)| i)
    (hSx0 : 1 / 2 ≤ (2 : ℝ) ^ k * x 0 → (2 : ℝ) ^ k * x 0 ≤ 2 → Sx ((2 : ℝ) ^ k * x 0) = (2 : ℝ) ^ k * x 0)
    (B eφ et ec : ℤ)
    (hUφ : ∑ i ∈ range n, |logPhi p n Sx k x i| < (2 : ℝ) ^ (eφ + 1))
    (hUt : ∑ i ∈ range n, |expCore p n S₁ S₂ e m r Fk d' i| < (2 : ℝ) ^ (et + 1))
    (hUc : ∑ i ∈ range n, |logC p n Sp B eφ et (logPhi p n Sx k x) (expCore p n S₁ S₂ e m r Fk d') i| <
      (2 : ℝ) ^ (ec + 1))
    (F' : ℕ → ℕ → ℝ) (hF' : ∀ k, ∀ i < n, F p (F' k i)) (φ' : ℕ → ℝ)
    (hφ' : ∀ k, |∑ i ∈ range n, F' k i - logFe k| ≤ φ' k) (q : ℕ) (hq : 2 ≤ q)
    (hC : Real.exp (E l₂) - 1 +
      (logCase4C p n η₁ η₂ ηx ηp (E l₂) pos m a (b l₂) (δ l₂) (π l₂) Fk φF d' (πx l₂) B).1 < 1)
    {ε Φ : ℝ}
    (h₁ : logBoundC p n η₁ η₂ ηx ηp ηc l₁ (E l₁) (πy l₁) pos m a (b l₁) (δ l₁) (π l₁) Fk φF d' (πx l₁) F' φ' q B ≤
      Φ + ε * l₁)
    (h₂ : logBoundC p n η₁ η₂ ηx ηp ηc l₂ (E l₂) (πy l₂) pos m a (b l₂) (δ l₂) (π l₂) Fk φF d' (πx l₂) F' φ' q B ≤
      Φ + ε * l₂) :
    |(logOp p n Sx Sp Sc y0 x k (expCore p n S₁ S₂ e m r Fk d') B eφ et ec F' q).sum -
        Real.log (∑ i ∈ range n, x i)| ≤ Φ + ε * |Real.log (∑ i ∈ range n, x i)| := by
  obtain ⟨ℓ, hℓd⟩ : ∃ ℓ, ℓ = |Real.log (∑ i ∈ range n, x i)| := ⟨_, rfl⟩
  rw [← hℓd] at hl hπy hE hδ hb hπ hπx ⊢
  have hs : Convex ℝ (Icc l₁ l₂) := convex_Icc l₁ l₂
  have h12 : l₁ ≤ l₂ := hl.1.trans hl.2
  have hr2 : l₂ ∈ Icc l₁ l₂ := right_mem_Icc.mpr h12
  have hη₁ := Scl.nonneg p hS₁
  have hη₂ := Scl.nonneg p hS₂
  have hηx := Scl.nonneg p hSx
  have hηp := Scl.nonneg p hSp
  have hηc := Scl.nonneg p hSc
  have hφF0 : ∀ k, 0 ≤ φF k := fun k => (abs_nonneg _).trans (hφF k)
  have hφ'0 : ∀ k, 0 ≤ φ' k := fun k => (abs_nonneg _).trans (hφ' k)
  -- the hypotheses at `ℓ` from those at `ℓ₂`: the convex variants grow with `ℓ`
  have hbpC := coreBpC_cvx n hs m hbc hη₁
  have hbdl : ∀ l ∈ Icc l₁ l₂, coreBpC n m (b l) η₁ < d' + 2 := fun l h => (hbpC.mono h hr2 h.2).trans_lt hbd
  obtain ⟨hEcC, -⟩ := logCase4C_cvx p n hA3 hs hη₁ hη₂ hηx hηp hEc pos m a hbc hδc hπc Fk hφF0 d' hπxc B hbdl
  have hCl : Real.exp (E ℓ) - 1 +
      (logCase4C p n η₁ η₂ ηx ηp (E ℓ) pos m a (b ℓ) (δ ℓ) (π ℓ) Fk φF d' (πx ℓ) B).1 < 1 :=
    ((hEc.exp_sub_one.add hEcC).mono hl hr2 hl.2).trans_lt hC
  have hcl : b ℓ + E ℓ + δ ℓ ≤ 3 / 5 := (((hbc.add hEc).add hδc).mono hl hr2 hl.2).trans hc
  have hE0 := hEc.nonneg ℓ hl
  have hb0 := hbc.nonneg ℓ hl
  have hδ0 := hδc.nonneg ℓ hl
  have hπ0 : ∀ i, 0 ≤ π ℓ i := fun i => (hπc i).nonneg ℓ hl
  have hπy0 : ∀ i, 0 ≤ πy ℓ i := fun i => (hπyc i).nonneg ℓ hl
  have hπx0 : ∀ i, 0 ≤ πx ℓ i := fun i => (hπxc i).nonneg ℓ hl
  -- the bounds of `thm42_case` are at most their convex variants
  have hbp2 : coreBp n e m (b ℓ) η₁ ≤ coreBpC n m (b l₂) η₁ :=
    (coreBp_sand n e m (Sand.refl hb0) hη₁).le.trans (hbpC.mono hl hr2 hl.2)
  obtain ⟨hEc4, -⟩ := logCase4_sand p n hA3 hη₁ hη₂ hηx hηp hE0 pos e m a hb0 hδ0 hπ0 Fk hφF0 d' hπx0 B
    (hbdl ℓ hl)
  have hCp : Real.exp (E ℓ) - 1 +
      (logCase4 p n η₁ η₂ ηx ηp (E ℓ) pos e m a (b ℓ) (δ ℓ) (π ℓ) Fk φF d' (πx ℓ) B).1 < 1 := by
    linarith only [hEc4.le, hCl]
  obtain ⟨hx1, hx2⟩ := log_range_half_two p n hn θ hθ hρ x hH hX0 _ _ k (E ℓ) (δ ℓ) (b ℓ) hE hδ hb hcl
  have h := thm42_case_ladder p n hp hn hA3 hS₁ hS₂ hSx hSp hSc x hx hX0 θ hθ hρ hH y0 hy0 (πy ℓ) hπy ℓ (E ℓ)
    hℓd.ge hE r hr k (δ ℓ) hδ a (b ℓ) ha hb hcl (π ℓ) hπ pos hsgn e hU m d' hd (hbp2.trans_lt hbd)
    (fun h1 => (Real.exp_le_exp.mpr hbp2).trans (hb2 h1)) Fk hF φF hφF (πx ℓ) hπx0 hπx (hSx0 hx1 hx2) B eφ et ec
    hUφ hUt hUc F' hF' φ' hφ' q hq hCp
  have hs1 := logBound_sand p n hA3 hη₁ hη₂ hηx hηp hηc (h0.trans hl.1) hE0 hπy0 pos e m a hb0 hδ0 hπ0 Fk hφF0
    d' hπx0 F' hφ'0 q B (hbdl ℓ hl) hCl
  -- the chord
  have hcv := logBoundC_cvx_Icc p n hA3 h0 h12 hη₁ hη₂ hηx hηp hηc hEc hπyc pos m a hbc hδc hπc Fk hφF0 d' hπxc
    F' hφ'0 q B hbd hC
  exact h.trans (hs1.le.trans (chord_affine hcv.convex h₁ h₂ hl))

end ExpansionBounds
