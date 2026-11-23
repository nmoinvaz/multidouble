import ExpansionBounds.SharpDiv

/-!
# Theorem 21: SQRT

SQRT_{n,J} scales `x` by `s = 2^⌊log₂ RN(√x_0)⌋` to `a = x/s²` and `h = a/2`, starts from
`r = (RN(1/RN(√a_0)), 0, …, 0)` and takes `J` Newton steps on the reciprocal root: `m = MUL(r, r)`, `g = MUL(h, m)`,
`c = ADDF(-g, 1/2)`, `d = MUL(c, r)` and `r ← ADD(r, d)`; it returns `MUL(r, a)` scaled by `s`. With `y = a^{-1/2}`,
`r = y(1 + e)` and the exact Newton map `N(r) = y(1 - 3e²/2 - e³/2)`, the five rounding errors of a step are bounded by
`G_MUL`, `G_ADDF` and `G_ADD` in units of `y`, `y²`, `1` and `a`, which gives `E_{k+1}` and the part bounds of the next
`r`. The scalings by powers of two are exact.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ)

/-- a list's parts as a function -/
def lf (l : List ℝ) (i : ℕ) : ℝ := l.getD i 0

/-- `G_ADDF(α, β_0; Z̄, λ_0)`'s part bounds with the leading level bound `λ_0` given -/
noncomputable def GaddfP' (α : ℕ → ℝ) (lam0 Zb : ℝ) : ℕ → ℝ := gParts p n (addfX p n α lam0) Zb 0

/-- the first half of a Newton step: `m = MUL(r, r)`, `g = MUL(h, m)` and `c = ADDF(-g, 1/2)` -/
noncomputable def sqrtCop (h r : ℕ → ℝ) : ℕ → ℝ :=
  lf (addfOp p n (fun i => -lf (mulOp p n h (lf (mulOp p n r r))) i) (1 / 2))

/-- one Newton step of SQRT: `c` of `sqrtCop`, `d = MUL(c, r)` and `ADD(r, d)` -/
noncomputable def sqrtStep (h r : ℕ → ℝ) : ℕ → ℝ := lf (addOp p n r (lf (mulOp p n (sqrtCop p n h r) r)))

/-- `e = ⌊log₂ RN(√x_0)⌋`, so that `s = 2^e` -/
noncomputable def sqrtE (x0 : ℝ) : ℤ := ⌊Real.log (RN p (Real.sqrt x0)) / Real.log 2⌋

/-- the scaled operand `a = x/s²` -/
noncomputable def sqrtA (x : ℕ → ℝ) (i : ℕ) : ℝ := (2 : ℝ) ^ (-2 * sqrtE p (x 0)) * x i

/-- the start `r = (RN(1/RN(√a_0)), 0, …, 0)` -/
noncomputable def sqrtR0 (a0 : ℝ) (i : ℕ) : ℝ := if i = 0 then RN p (1 / RN p (Real.sqrt a0)) else 0

/-- SQRT_{n,J}: `J` steps from `sqrtR0`, then `MUL(r, a)` scaled by `s` -/
noncomputable def sqrtOp (J : ℕ) (x : ℕ → ℝ) : List ℝ :=
  (mulOp p n ((sqrtStep p n fun i => sqrtA p x i / 2)^[J] (sqrtR0 p (sqrtA p x 0))) (sqrtA p x)).map
    fun v => (2 : ℝ) ^ sqrtE p (x 0) * v

/-- `ε_m = G_MUL(π, π; (1 + E)²)`, the error of `m` in units of `y²` -/
noncomputable def sqrtEm (E : ℝ) (π : ℕ → ℝ) : ℝ := GmulE p n π π ((1 + E) ^ 2)

/-- `ε_g` of `G_MUL(h̄, μ; ((1 + E)² + ε_m)/2)`, `μ` the part bounds of `m` -/
noncomputable def sqrtEg (hb : ℕ → ℝ) (E : ℝ) (π : ℕ → ℝ) : ℝ :=
  GmulE p n hb (GmulP p n π π ((1 + E) ^ 2)) (((1 + E) ^ 2 + sqrtEm p n E π) / 2)

/-- `π^g`, the part bounds of `g` -/
noncomputable def sqrtPg (hb : ℕ → ℝ) (E : ℝ) (π : ℕ → ℝ) : ℕ → ℝ :=
  GmulP p n hb (GmulP p n π π ((1 + E) ^ 2)) (((1 + E) ^ 2 + sqrtEm p n E π) / 2)

/-- `Z̄_c = (2E + E²)/2 + ε_m/2 + ε_g`, the bound on the exact value of the ADDF -/
noncomputable def sqrtZc (hb : ℕ → ℝ) (E : ℝ) (π : ℕ → ℝ) : ℝ :=
  (2 * E + E ^ 2) / 2 + sqrtEm p n E π / 2 + sqrtEg p n hb E π

/-- `λ_0 = Z̄_c + ∑_{i ≥ 1} π^g_i` -/
noncomputable def sqrtL0 (hb : ℕ → ℝ) (E : ℝ) (π : ℕ → ℝ) : ℝ :=
  sqrtZc p n hb E π + ∑ i ∈ Ico 1 n, sqrtPg p n hb E π i

/-- `ε_c` of `G_ADDF(π^g, 1/2; Z̄_c, λ_0)` -/
noncomputable def sqrtEc (hb : ℕ → ℝ) (E : ℝ) (π : ℕ → ℝ) : ℝ :=
  GaddfE' p n (sqrtPg p n hb E π) (sqrtL0 p n hb E π) (sqrtZc p n hb E π)

/-- `χ`, the part bounds of `c` -/
noncomputable def sqrtChi (hb : ℕ → ℝ) (E : ℝ) (π : ℕ → ℝ) : ℕ → ℝ :=
  GaddfP' p n (sqrtPg p n hb E π) (sqrtL0 p n hb E π) (sqrtZc p n hb E π)

/-- one step's bounds `(E_{k+1}, π^{(k+1)})` from `(E_k, π^{(k)})`, with `h̄` the part bounds of `h` in units of `a` -/
noncomputable def sqrtB (hb : ℕ → ℝ) (E : ℝ) (π : ℕ → ℝ) : ℝ × (ℕ → ℝ) :=
  let εmgc := sqrtEm p n E π / 2 + sqrtEg p n hb E π + sqrtEc p n hb E π
  let cb := sqrtZc p n hb E π + sqrtEc p n hb E π
  let εd := GmulE p n (sqrtChi p n hb E π) π (cb * (1 + E))
  let δ := GmulP p n (sqrtChi p n hb E π) π (cb * (1 + E))
  let Zr := (1 + E) + cb * (1 + E) + εd
  (3 / 2 * E ^ 2 + E ^ 3 / 2 + (1 + E) * εmgc + εd + GaddE p n π δ Zr, GaddP p n π δ Zr)

variable [Prec_gt_0 p]

/-- `G_ADDF` with `λ_0` given bounds ADDF -/
theorem addf_G' (hp : 1 < p) (hn : 1 ≤ n) (a : ℕ → ℝ) (b : ℝ) (α : ℕ → ℝ) (ha : ∀ i < n, F p (a i))
    (hb : F p b) (hα : ∀ i < n, |a i| ≤ α i) (lam0 : ℝ) (hlam : |a 0 + b| ≤ lam0) (Zb : ℝ)
    (hZ : |∑ i ∈ range n, a i + b| ≤ Zb) :
    |(∑ i ∈ range n, a i + b) - (addfOp p n a b).sum| ≤ GaddfE' p n α lam0 Zb ∧
      (∀ i, |(addfOp p n a b).getD i 0| ≤ GaddfP' p n α lam0 Zb i) ∧ (∀ i, F p ((addfOp p n a b).getD i 0)) ∧
      (addfOp p n a b).length ≤ n := by
  obtain ⟨r1, r2, r3, -, -⟩ := lemma13_addf p hp hn a b ha hb α hα _ hlam Zb hZ
  have hF : ∀ i ≤ n, F p (addfLevels p n a b i) := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hch := addf_chain p (n' + 1) hp a b ha hb α hα _ hlam
    intro i hi
    rcases Nat.lt_or_ge i (n' + 1) with hlt | hge
    · simp only [addfLevels, hlt, ite_true]
      exact F_twoSum_fst p _ _
    · obtain rfl : i = n' + 1 := by omega
      simp only [addfLevels, lt_irrefl, ite_false, ite_true]
      exact (hch n' (by omega)).2.2.1
  obtain ⟨l1, l2, -⟩ := ren_spec p n hn _ hF
  refine ⟨?_, gParts_le p n _ _ _ _ l1 (by simpa using r2) r3, l2, l1⟩
  simpa [GaddfE', gErr] using r1

theorem F_half : F p (1 / 2) := by
  have h := F_two_zpow p (-1)
  rwa [zpow_neg, zpow_one, ← one_div] at h

/-- the first half of a Newton step: from `r` within `Ey` of `y = a^{-1/2}` with parts within `yπ`, and `h` with
parts within `ah̄` and sum `a/2`, `c = ADDF(-MUL(h, MUL(r, r)), 1/2)` is within `ε_m/2 + ε_g + ε_c` of
`1/2 - (a/2)r²`, within `Z̄_c + ε_c` of zero, with parts within `χ` -/
theorem sqrt_c (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {A y : ℝ} (hy : 0 < y)
    (hAy : A * y ^ 2 = 1) (h hb : ℕ → ℝ) (hh : ∀ i < n, F p (h i)) (hhb : ∀ i < n, |h i| ≤ A * hb i)
    (hb0 : ∀ i, 0 ≤ hb i) (hH : ∑ i ∈ range n, h i = A / 2) (r : ℕ → ℝ) (E : ℝ) (π : ℕ → ℝ) (hE : 0 ≤ E)
    (hπ : ∀ i, 0 ≤ π i) (hr : ∀ i < n, F p (r i)) (hrπ : ∀ i < n, |r i| ≤ y * π i)
    (hR : |∑ i ∈ range n, r i - y| ≤ E * y) :
    (∀ i < n, F p (sqrtCop p n h r i)) ∧ (∀ i < n, |sqrtCop p n h r i| ≤ sqrtChi p n hb E π i) ∧
      (∀ i, 0 ≤ sqrtChi p n hb E π i) ∧
      |∑ i ∈ range n, sqrtCop p n h r i - (1 / 2 - A / 2 * ((∑ i ∈ range n, r i) * ∑ i ∈ range n, r i))| ≤
        sqrtEm p n E π / 2 + sqrtEg p n hb E π + sqrtEc p n hb E π ∧
      |∑ i ∈ range n, sqrtCop p n h r i| ≤ sqrtZc p n hb E π + sqrtEc p n hb E π ∧
      0 ≤ sqrtEm p n E π ∧ 0 ≤ sqrtEg p n hb E π ∧ 0 ≤ sqrtEc p n hb E π ∧ 0 ≤ sqrtZc p n hb E π := by
  have hu := u_pos p
  have hA : 0 < A := by
    by_contra hc
    have : A * y ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) (sq_nonneg y)
    linarith
  set R := ∑ i ∈ range n, r i with hRd
  have hRb : |R| ≤ (1 + E) * y := by
    have := abs_sub_abs_le_abs_sub R y
    rw [abs_of_pos hy] at this
    linarith
  -- (1) `m = MUL(r, r)`, in units of `y²`
  set εm := sqrtEm p n E π with hεm
  set μ := GmulP p n π π ((1 + E) ^ 2) with hμ
  obtain ⟨hεm0, hμ0⟩ := Gmul_nonneg p n hA3 hπ hπ (sq_nonneg (1 + E))
  have hEy : 0 ≤ (1 + E) * y := mul_nonneg (by linarith) hy.le
  have hRR : |R * R| ≤ y * y * (1 + E) ^ 2 := by
    rw [abs_mul]
    calc |R| * |R| ≤ (1 + E) * y * ((1 + E) * y) := mul_le_mul hRb hRb (abs_nonneg _) hEy
      _ = y * y * (1 + E) ^ 2 := by ring
  obtain ⟨m1, m2, m3, m4⟩ := mul_G p n hp hn hA3 r r (fun i => y * π i) (fun j => y * π j) hr hr hrπ hrπ _ hRR
  obtain ⟨s1, s2⟩ := Gmul_smul p n π π ((1 + E) ^ 2) hy.le hy.le
  rw [s1] at m1
  set m := lf (mulOp p n r r) with hm
  have hmF : ∀ i < n, F p (m i) := fun i _ => m3 i
  have hmb : ∀ i < n, |m i| ≤ y * y * μ i := fun i _ => by rw [← s2 i]; exact m2 i
  set M := ∑ i ∈ range n, m i with hMd
  have hMs : M = (mulOp p n r r).sum := (list_sum_getD _ n m4).symm
  rw [← hMs] at m1
  replace m1 : |R * R - M| ≤ y * y * εm := m1
  -- (2) `g = MUL(h, m)`, in units of `ay² = 1`
  set εg := sqrtEg p n hb E π with hεg
  set πg := sqrtPg p n hb E π with hπg
  obtain ⟨hεg0, hπg0⟩ := Gmul_nonneg p n hA3 hb0 hμ0 (div_nonneg (add_nonneg (sq_nonneg _) hεm0) zero_le_two)
  have hHM : |(∑ i ∈ range n, h i) * M| ≤ A * (y * y) * (((1 + E) ^ 2 + εm) / 2) := by
    rw [hH, abs_mul, abs_of_pos (half_pos hA)]
    have hM : |M| ≤ y * y * ((1 + E) ^ 2 + εm) := by
      have := abs_sub_abs_le_abs_sub M (R * R)
      rw [abs_sub_comm] at m1
      linarith only [this, m1, hRR]
    calc A / 2 * |M| ≤ A / 2 * (y * y * ((1 + E) ^ 2 + εm)) := mul_le_mul_of_nonneg_left hM (half_pos hA).le
      _ = A * (y * y) * (((1 + E) ^ 2 + εm) / 2) := by ring
  obtain ⟨g1, g2, g3, g4⟩ := mul_G p n hp hn hA3 h m (fun i => A * hb i) (fun j => y * y * μ j) hh hmF hhb hmb _
    hHM
  obtain ⟨t1, t2⟩ := Gmul_smul p n hb μ (((1 + E) ^ 2 + εm) / 2) hA.le (mul_nonneg hy.le hy.le)
  have hAyy : A * (y * y) = 1 := by rw [← hAy]; ring
  rw [t1, hAyy, one_mul] at g1
  set g := lf (mulOp p n h m) with hg
  have hgF : ∀ i < n, F p (g i) := fun i _ => g3 i
  have hgb : ∀ i < n, |g i| ≤ πg i := fun i _ => by
    have := g2 i
    rw [t2 i, hAyy, one_mul] at this
    exact this
  set G := ∑ i ∈ range n, g i with hGd
  have hGs : G = (mulOp p n h m).sum := (list_sum_getD _ n g4).symm
  rw [← hGs, hH] at g1
  -- (3) `c = ADDF(-g, 1/2)`
  set e := R / y - 1 with he
  have hRe : R = y * (1 + e) := by rw [he]; field_simp; ring
  have heE : |e| ≤ E := by
    rw [he, show R / y - 1 = (R - y) / y by field_simp, abs_div, abs_of_pos hy, div_le_iff₀ hy]
    exact hR
  set Zc := sqrtZc p n hb E π with hZc
  have h2 : |A / 2 * (R * R - M)| ≤ εm / 2 := by
    rw [abs_mul, abs_of_pos (half_pos hA), abs_sub_comm]
    calc A / 2 * |M - R * R| ≤ A / 2 * (y * y * εm) := by
          rw [abs_sub_comm]; exact mul_le_mul_of_nonneg_left m1 (half_pos hA).le
      _ = εm / 2 := by rw [show A / 2 * (y * y * εm) = A * (y * y) * εm / 2 by ring, hAyy]; ring
  have h3 : |A / 2 * M - G| ≤ εg := g1
  have hhalf : |1 / 2 - G| ≤ Zc := by
    have hsplit : 1 / 2 - G = (1 / 2 - A / 2 * (R * R)) + A / 2 * (R * R - M) + (A / 2 * M - G) := by ring
    have h1 : |1 / 2 - A / 2 * (R * R)| ≤ (2 * E + E ^ 2) / 2 := by
      have hid : 1 / 2 - A / 2 * (R * R) = -(2 * e + e ^ 2) / 2 := by
        rw [hRe]
        linear_combination (-(1 + e) ^ 2 / 2) * hAy
      rw [hid, abs_div, abs_neg, abs_two]
      have : |2 * e + e ^ 2| ≤ 2 * E + E ^ 2 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_two, abs_pow]
        have h2 : |e| ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ (abs_nonneg e) heE 2
        exact add_le_add (mul_le_mul_of_nonneg_left heE zero_le_two) h2
      exact div_le_div_of_nonneg_right this zero_le_two
    rw [hsplit]
    calc _ ≤ |1 / 2 - A / 2 * (R * R)| + |A / 2 * (R * R - M)| + |A / 2 * M - G| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add h1 h2) h3
  set lam0 := sqrtL0 p n hb E π with hlam0
  have hng : ∑ i ∈ range n, (fun i => -g i) i + 1 / 2 = 1 / 2 - G := by
    simp only [sum_neg_distrib, hGd]
    ring
  have hlam : |(fun i => -g i) 0 + 1 / 2| ≤ lam0 := by
    have hs : G = g 0 + ∑ i ∈ Ico 1 n, g i := by
      rw [hGd, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
    have h1 : |∑ i ∈ Ico 1 n, g i| ≤ ∑ i ∈ Ico 1 n, πg i :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => hgb i (mem_Ico.mp hi).2)
    rw [show (fun i => -g i) 0 + 1 / 2 = (1 / 2 - G) + ∑ i ∈ Ico 1 n, g i by simp only; rw [hs]; ring]
    exact (abs_add_le _ _).trans (add_le_add hhalf h1)
  obtain ⟨c1, c2, c3, c4⟩ := addf_G' p n hp hn (fun i => -g i) (1 / 2) πg (fun i hi => F_neg p (hgF i hi))
    (F_half p) (fun i hi => by simp only [abs_neg]; exact hgb i hi) lam0 hlam Zc (by rw [hng]; exact hhalf)
  rw [hng] at c1
  set εc := sqrtEc p n hb E π with hεc
  have hεc0 : 0 ≤ εc := (abs_nonneg _).trans c1
  have hZc0 : 0 ≤ Zc := (abs_nonneg _).trans hhalf
  have hχ0 : ∀ i, 0 ≤ sqrtChi p n hb E π i := gParts_nonneg p n (addfX_nonneg p n hπg0
    (add_nonneg hZc0 (sum_nonneg fun i _ => hπg0 i))) hZc0 le_rfl
  have hcop : sqrtCop p n h r = lf (addfOp p n (fun i => -g i) (1 / 2)) := rfl
  rw [hcop]
  set c := lf (addfOp p n (fun i => -g i) (1 / 2)) with hc
  set C := ∑ i ∈ range n, c i with hCd
  have hCs : C = (addfOp p n (fun i => -g i) (1 / 2)).sum := (list_sum_getD _ n c4).symm
  rw [← hCs] at c1
  refine ⟨fun i _ => c3 i, fun i _ => c2 i, hχ0, ?_, ?_, hεm0, hεg0, hεc0, hZc0⟩
  · have hsplit : C - (1 / 2 - A / 2 * (R * R)) = (C - (1 / 2 - G)) + (A / 2 * M - G) + A / 2 * (R * R - M) := by
      ring
    rw [hsplit]
    calc _ ≤ |C - (1 / 2 - G)| + |A / 2 * M - G| + |A / 2 * (R * R - M)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ εc + εg + εm / 2 := add_le_add (add_le_add (by rw [abs_sub_comm]; exact c1) h3) h2
      _ = _ := by ring
  · calc |C| = |(1 / 2 - G) + (C - (1 / 2 - G))| := by congr 1; ring
      _ ≤ |1 / 2 - G| + |C - (1 / 2 - G)| := abs_add_le _ _
      _ ≤ Zc + εc := add_le_add hhalf (by rw [abs_sub_comm]; exact c1)

/-- one Newton step: from `r` within `Ey` of `y = a^{-1/2}` with parts within `yπ`, the next `r` is within
`E_{k+1}y` of `y` with parts within `yπ^{(k+1)}`; `h` has parts within `ah̄` and sum `a/2` -/
theorem sqrt_step (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {A y : ℝ} (hy : 0 < y)
    (hAy : A * y ^ 2 = 1) (h hb : ℕ → ℝ) (hh : ∀ i < n, F p (h i)) (hhb : ∀ i < n, |h i| ≤ A * hb i)
    (hb0 : ∀ i, 0 ≤ hb i) (hH : ∑ i ∈ range n, h i = A / 2) (r : ℕ → ℝ) (E : ℝ) (π : ℕ → ℝ) (hE : 0 ≤ E)
    (hπ : ∀ i, 0 ≤ π i) (hr : ∀ i < n, F p (r i)) (hrπ : ∀ i < n, |r i| ≤ y * π i)
    (hR : |∑ i ∈ range n, r i - y| ≤ E * y) :
    (∀ i < n, F p (sqrtStep p n h r i)) ∧ (∀ i < n, |sqrtStep p n h r i| ≤ y * (sqrtB p n hb E π).2 i) ∧
      |∑ i ∈ range n, sqrtStep p n h r i - y| ≤ (sqrtB p n hb E π).1 * y ∧ 0 ≤ (sqrtB p n hb E π).1 ∧
      ∀ i, 0 ≤ (sqrtB p n hb E π).2 i := by
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
  -- (4) `d = MUL(c, r)`, in units of `y`
  set εd := GmulE p n χ π (cb * (1 + E)) with hεd
  set δ := GmulP p n χ π (cb * (1 + E)) with hδ
  obtain ⟨hεd0, hδ0⟩ := Gmul_nonneg p n hA3 hχ0 hπ (mul_nonneg hcb0 h1E)
  have hCR : |C * R| ≤ 1 * y * (cb * (1 + E)) := by
    rw [abs_mul]
    calc |C| * |R| ≤ cb * ((1 + E) * y) := mul_le_mul hCb hRb (abs_nonneg _) hcb0
      _ = 1 * y * (cb * (1 + E)) := by ring
  obtain ⟨d1, d2, d3, d4⟩ := mul_G p n hp hn hA3 c r (fun i => 1 * χ i) (fun j => y * π j) c3 hr
    (fun i hi => by rw [one_mul]; exact c2 i hi) hrπ _ hCR
  obtain ⟨u1, u2⟩ := Gmul_smul p n χ π (cb * (1 + E)) zero_le_one hy.le
  rw [u1, one_mul] at d1
  set d := lf (mulOp p n c r) with hd
  set D := ∑ i ∈ range n, d i with hDd
  have hDs : D = (mulOp p n c r).sum := (list_sum_getD _ n d4).symm
  rw [← hDs] at d1
  have hdb : ∀ i < n, |d i| ≤ y * δ i := fun i _ => by
    have := d2 i
    rw [u2 i, one_mul] at this
    exact this
  -- (5) `r' = ADD(r, d)`, in units of `y`
  set Zr := (1 + E) + cb * (1 + E) + εd with hZr
  have hRD : |R + D| ≤ y * Zr := by
    have : |D| ≤ |C * R| + y * εd := by
      have := abs_sub_abs_le_abs_sub D (C * R)
      rw [abs_sub_comm] at d1
      linarith
    calc |R + D| ≤ |R| + |D| := abs_add_le _ _
      _ ≤ (1 + E) * y + (1 * y * (cb * (1 + E)) + y * εd) := add_le_add hRb (this.trans (by linarith))
      _ = y * Zr := by rw [hZr]; ring
  obtain ⟨a1, a2, a3, a4⟩ := add_G p n hp hn hA3 r d (fun i => y * π i) (fun j => y * δ j) hr (fun i _ => d3 i)
    hrπ hdb _ hRD
  obtain ⟨v1, v2⟩ := Gadd_smul p n π δ Zr hy.le
  rw [v1] at a1
  have hB : sqrtB p n hb E π = (3 / 2 * E ^ 2 + E ^ 3 / 2 + (1 + E) * εmgc + εd + GaddE p n π δ Zr,
      GaddP p n π δ Zr) := rfl
  have hstep : sqrtStep p n h r = lf (addOp p n r d) := rfl
  have hZr0 : 0 ≤ Zr := add_nonneg (add_nonneg h1E (mul_nonneg hcb0 h1E)) hεd0
  obtain ⟨hεr0, hπ'0⟩ := Gadd_nonneg p n hA3 hπ hδ0 hZr0
  have hE'0 : 0 ≤ 3 / 2 * E ^ 2 + E ^ 3 / 2 + (1 + E) * εmgc + εd + GaddE p n π δ Zr :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg (by positivity) (div_nonneg (pow_nonneg hE 3) zero_le_two))
      (mul_nonneg h1E hεmgc0)) hεd0) hεr0
  rw [hB, hstep]
  refine ⟨fun i _ => a3 i, fun i _ => by rw [← v2 i]; exact a2 i, ?_, hE'0, hπ'0⟩
  -- (6) `r' - y = (N(r) - y) + r(c - c_e) + ε̂_d + ε̂_r`, `c_e = 1/2 - (a/2)r²`
  have hRs : ∑ i ∈ range n, lf (addOp p n r d) i = (addOp p n r d).sum := (list_sum_getD _ n a4).symm
  rw [hRs]
  set R' := (addOp p n r d).sum with hR'
  set e := R / y - 1 with he
  have hRe : R = y * (1 + e) := by rw [he]; field_simp; ring
  have heE : |e| ≤ E := by
    rw [he, show R / y - 1 = (R - y) / y by field_simp, abs_div, abs_of_pos hy, div_le_iff₀ hy]
    exact hR
  have hid : R' - y = -y * (3 / 2 * e ^ 2 + e ^ 3 / 2) + R * (C - (1 / 2 - A / 2 * (R * R))) + (D - C * R) -
      ((R + D) - R') := by
    have hN : R + R * (1 / 2 - A / 2 * (R * R)) - y = -y * (3 / 2 * e ^ 2 + e ^ 3 / 2) := by
      rw [hRe]
      linear_combination (-(y * (1 + e) ^ 3) / 2) * hAy
    linear_combination hN
  rw [hid]
  have hN : |-y * (3 / 2 * e ^ 2 + e ^ 3 / 2)| ≤ y * (3 / 2 * E ^ 2 + E ^ 3 / 2) := by
    rw [abs_mul, abs_neg, abs_of_pos hy]
    refine mul_le_mul_of_nonneg_left ?_ hy.le
    have h2 : e ^ 2 ≤ E ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg e) heE 2
    have h3 : |e| ^ 3 ≤ E ^ 3 := pow_le_pow_left₀ (abs_nonneg e) heE 3
    have h4 : |3 / 2 * e ^ 2 + e ^ 3 / 2| ≤ 3 / 2 * e ^ 2 + |e| ^ 3 / 2 := by
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_of_nonneg (by positivity), abs_div, abs_pow, abs_two]
    exact h4.trans (add_le_add (mul_le_mul_of_nonneg_left h2 (by norm_num)) (div_le_div_of_nonneg_right h3 zero_le_two))
  have hmid : |R * (C - (1 / 2 - A / 2 * (R * R)))| ≤ (1 + E) * y * εmgc := by
    rw [abs_mul]
    exact mul_le_mul hRb hce (abs_nonneg _) hEy
  have hd' : |D - C * R| ≤ y * εd := by rw [abs_sub_comm]; exact d1
  calc _ ≤ |-y * (3 / 2 * e ^ 2 + e ^ 3 / 2)| + |R * (C - (1 / 2 - A / 2 * (R * R)))| + |D - C * R| +
        |(R + D) - R'| :=
        (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ y * (3 / 2 * E ^ 2 + E ^ 3 / 2) + (1 + E) * y * εmgc + y * εd + y * GaddE p n π δ Zr :=
        add_le_add (add_le_add (add_le_add hN hmid) hd') a1
    _ = _ := by ring

omit [Prec_gt_0 p] in
/-- `ā_i = ρ^i(1 - ρ)/(1 - 2ρ)`, the part bounds of (eq:abar) in units of the value -/
noncomputable def abar (ρ : ℝ) (i : ℕ) : ℝ := ρ ^ i * ((1 - ρ) / (1 - 2 * ρ))

omit [Prec_gt_0 p] in
/-- `E_0 = max((1 + 2u)/(1 - ρ) - 1, 1 - (1 - 2u)(1 - 2ρ)/(1 - ρ))` -/
noncomputable def sqrtE0 (ρ : ℝ) : ℝ := max ((1 + 2 * u p) / (1 - ρ) - 1) (1 - (1 - 2 * u p) * (1 - 2 * ρ) / (1 - ρ))

omit [Prec_gt_0 p] in
/-- `(E_k, π^{(k)})`: `π^{(0)} = (1 + E_0, 0, …, 0)` and one `sqrtB` per step, with `h̄ = ā/2` -/
noncomputable def sqrtBk (ρ : ℝ) : ℕ → ℝ × (ℕ → ℝ)
  | 0 => (sqrtE0 p ρ, fun i => if i = 0 then 1 + sqrtE0 p ρ else 0)
  | k + 1 => sqrtB p n (fun i => abar ρ i / 2) (sqrtBk ρ k).1 (sqrtBk ρ k).2

omit [Prec_gt_0 p] in
/-- `δ_J = E_J + ε_z` with `(ε_z, ·) = G_MUL(π^{(J)}, ā; 1 + E_J)` -/
noncomputable def sqrtDelta (ρ : ℝ) (J : ℕ) : ℝ :=
  (sqrtBk p n ρ J).1 + GmulE p n (sqrtBk p n ρ J).2 (abar ρ) (1 + (sqrtBk p n ρ J).1)

/-- the start: `r_0 = RN(1/RN(√a_0))` with `a_0(1 - 2ρ)/(1 - ρ) ≤ a ≤ a_0/(1 - ρ)` is within `E_0` of `1/√a`,
relatively -/
theorem sqrt_start {ρ a0 A : ℝ} (hρ0 : 0 ≤ ρ) (hρ : 2 * ρ < 1) (ha0 : 0 < a0)
    (hlo : (1 - 2 * ρ) / (1 - ρ) * a0 ≤ A) (hhi : A ≤ a0 / (1 - ρ)) :
    |RN p (1 / RN p (Real.sqrt a0)) - (Real.sqrt A)⁻¹| ≤ sqrtE0 p ρ * (Real.sqrt A)⁻¹ := by
  have hu := u_pos p
  have hus : us p = u p / (1 + u p) := rfl
  have h1ρ : 0 < 1 - ρ := by linarith
  have h12 : 0 < 1 - 2 * ρ := by linarith
  have hA : 0 < A := lt_of_lt_of_le (by positivity) hlo
  have hsa : 0 < Real.sqrt a0 := Real.sqrt_pos.mpr ha0
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  set v := RN p (Real.sqrt a0) with hv
  set w := RN p (1 / v) with hw
  have hus1 : us p < 1 := by rw [hus, div_lt_one (by linarith)]; linarith
  have hv1 := abs_RN_sub_le_us p (Real.sqrt a0)
  rw [← hv, abs_of_pos hsa] at hv1
  have hvlo : (1 - us p) * Real.sqrt a0 ≤ v := by linarith [(abs_le.mp hv1).1]
  have hvhi : v ≤ (1 + us p) * Real.sqrt a0 := by linarith [(abs_le.mp hv1).2]
  have hvpos : 0 < v := lt_of_lt_of_le (mul_pos (by linarith) hsa) hvlo
  have hw1 := abs_RN_sub_le_us p (1 / v)
  rw [← hw, abs_of_pos (by positivity : 0 < 1 / v)] at hw1
  have hwlo : (1 - us p) * (1 / v) ≤ w := by linarith [(abs_le.mp hw1).1]
  have hwhi : w ≤ (1 + us p) * (1 / v) := by linarith [(abs_le.mp hw1).2]
  -- `t = √(a/a_0)` between `(1 - 2ρ)/(1 - ρ)` and `1/(1 - ρ)`
  set t := Real.sqrt A / Real.sqrt a0 with ht
  have htsq : t = Real.sqrt (A / a0) := (Real.sqrt_div' A ha0.le).symm
  have hU1 : 1 ≤ 1 / (1 - ρ) := by rw [le_div_iff₀ h1ρ]; linarith
  have hL1 : (1 - 2 * ρ) / (1 - ρ) ≤ 1 := by rw [div_le_iff₀ h1ρ]; linarith
  have hL0 : 0 ≤ (1 - 2 * ρ) / (1 - ρ) := div_nonneg h12.le h1ρ.le
  have hAa : A / a0 ≤ 1 / (1 - ρ) := by rw [div_le_iff₀ ha0]; calc A ≤ a0 / (1 - ρ) := hhi
    _ = 1 / (1 - ρ) * a0 := by ring
  have hAa' : (1 - 2 * ρ) / (1 - ρ) ≤ A / a0 := by rw [le_div_iff₀ ha0]; exact hlo
  have htU : t ≤ 1 / (1 - ρ) := by
    rw [htsq]
    calc Real.sqrt (A / a0) ≤ Real.sqrt ((1 / (1 - ρ)) ^ 2) := Real.sqrt_le_sqrt (hAa.trans (by nlinarith))
      _ = 1 / (1 - ρ) := Real.sqrt_sq (by linarith)
  have htL : (1 - 2 * ρ) / (1 - ρ) ≤ t := by
    rw [htsq]
    calc (1 - 2 * ρ) / (1 - ρ) = Real.sqrt (((1 - 2 * ρ) / (1 - ρ)) ^ 2) := (Real.sqrt_sq hL0).symm
      _ ≤ Real.sqrt (A / a0) := Real.sqrt_le_sqrt ((by nlinarith : ((1 - 2 * ρ) / (1 - ρ)) ^ 2 ≤
          (1 - 2 * ρ) / (1 - ρ)).trans hAa')
  have hratio : (1 + us p) / (1 - us p) = 1 + 2 * u p := by
    rw [hus]
    have : (1 : ℝ) + u p ≠ 0 := by linarith
    field_simp
    ring
  have hratio' : (1 - us p) / (1 + us p) = 1 / (1 + 2 * u p) := by
    rw [← hratio, one_div_div]
  have hd1 : 0 < (1 - us p) * Real.sqrt a0 := mul_pos (by linarith) hsa
  have hd2 : 0 < (1 + us p) * Real.sqrt a0 := mul_pos (by linarith [us_nonneg p]) hsa
  have hhi' : w * Real.sqrt A ≤ (1 + 2 * u p) / (1 - ρ) := by
    calc w * Real.sqrt A ≤ (1 + us p) * (1 / v) * Real.sqrt A := mul_le_mul_of_nonneg_right hwhi hsA.le
      _ ≤ (1 + us p) * (1 / ((1 - us p) * Real.sqrt a0)) * Real.sqrt A := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by linarith [us_nonneg p])) hsA.le
          exact one_div_le_one_div_of_le hd1 hvlo
      _ = (1 + us p) / (1 - us p) * t := by rw [ht]; field_simp
      _ = (1 + 2 * u p) * t := by rw [hratio]
      _ ≤ (1 + 2 * u p) * (1 / (1 - ρ)) := mul_le_mul_of_nonneg_left htU (by linarith)
      _ = (1 + 2 * u p) / (1 - ρ) := by ring
  have hlo' : (1 - 2 * u p) * (1 - 2 * ρ) / (1 - ρ) ≤ w * Real.sqrt A := by
    calc (1 - 2 * u p) * (1 - 2 * ρ) / (1 - ρ) ≤ 1 / (1 + 2 * u p) * ((1 - 2 * ρ) / (1 - ρ)) := by
          rw [mul_div_assoc]
          refine mul_le_mul_of_nonneg_right ?_ hL0
          rw [le_div_iff₀ (by linarith)]
          nlinarith
      _ ≤ 1 / (1 + 2 * u p) * t := mul_le_mul_of_nonneg_left htL (by positivity)
      _ = (1 - us p) / (1 + us p) * t := by rw [hratio']
      _ = (1 - us p) * (1 / ((1 + us p) * Real.sqrt a0)) * Real.sqrt A := by rw [ht]; field_simp
      _ ≤ (1 - us p) * (1 / v) * Real.sqrt A := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by linarith)) hsA.le
          exact one_div_le_one_div_of_le hvpos hvhi
      _ ≤ w * Real.sqrt A := mul_le_mul_of_nonneg_right hwlo hsA.le
  have hsplit : w - (Real.sqrt A)⁻¹ = (Real.sqrt A)⁻¹ * (w * Real.sqrt A - 1) := by field_simp
  rw [hsplit, abs_mul, abs_of_pos (inv_pos.mpr hsA), mul_comm]
  refine mul_le_mul_of_nonneg_right (abs_le.mpr ⟨?_, ?_⟩) (inv_pos.mpr hsA).le
  · have := le_max_right ((1 + 2 * u p) / (1 - ρ) - 1) (1 - (1 - 2 * u p) * (1 - 2 * ρ) / (1 - ρ))
    unfold sqrtE0
    linarith
  · have := le_max_left ((1 + 2 * u p) / (1 - ρ) - 1) (1 - (1 - 2 * u p) * (1 - 2 * ρ) / (1 - ρ))
    unfold sqrtE0
    linarith

omit [Prec_gt_0 p] in
theorem list_sum_map_mul (c : ℝ) (l : List ℝ) : (l.map fun v => c * v).sum = c * l.sum := by
  induction l with
  | nil => simp
  | cons v l ih => rw [List.map_cons, List.sum_cons, List.sum_cons, ih]; ring

/-- the scaled operand `a = 2^{-2e}x` of SQRT: exact, on `H(θ)` with `a_0 > 0`, between `a_0(1 - 2ρ)/(1 - ρ)` and
`a_0/(1 - ρ)`, with parts within `aā_i` and halves in `F`, and `√x = 2^e√a` -/
theorem sqrt_setup (hn : 1 ≤ n) {θ : ℝ} (hθ : 0 ≤ θ) (hρ : 2 * (θ * u p) < 1) (x : ℕ → ℝ)
    (hx : ∀ i < n, F p (x i)) (hH : Htheta p n θ x) (hx0 : 0 < x 0) :
    (∀ i < n, F p (sqrtA p x i)) ∧ 0 < sqrtA p x 0 ∧
      (∀ i < n, |sqrtA p x i| ≤ (θ * u p) ^ i * sqrtA p x 0) ∧
      (1 - 2 * (θ * u p)) / (1 - θ * u p) * sqrtA p x 0 ≤ ∑ i ∈ range n, sqrtA p x i ∧
      ∑ i ∈ range n, sqrtA p x i ≤ sqrtA p x 0 / (1 - θ * u p) ∧ 0 < ∑ i ∈ range n, sqrtA p x i ∧
      (∀ i < n, |sqrtA p x i| ≤ (∑ i ∈ range n, sqrtA p x i) * abar (θ * u p) i) ∧
      (∀ i < n, F p (sqrtA p x i / 2)) ∧
      Real.sqrt (∑ i ∈ range n, x i) = (2 : ℝ) ^ sqrtE p (x 0) * Real.sqrt (∑ i ∈ range n, sqrtA p x i) := by
  have hu := u_pos p
  set ρ := θ * u p with hρd
  have hρ0 : 0 ≤ ρ := mul_nonneg hθ hu.le
  have h1ρ : 0 < 1 - ρ := by linarith
  have h12 : 0 < 1 - 2 * ρ := by linarith
  set e := sqrtE p (x 0) with he
  set σ : ℝ := (2 : ℝ) ^ (-2 * e) with hσ
  have hσ0 : 0 < σ := by positivity
  set a := sqrtA p x with ha
  have haσ : ∀ i, a i = σ * x i := fun i => rfl
  have haF : ∀ i < n, F p (a i) := fun i hi => F_zpow_mul p _ (hx i hi)
  have ha0 : 0 < a 0 := by rw [haσ]; positivity
  have haH : ∀ i < n, |a i| ≤ ρ ^ i * a 0 := fun i hi => by
    rw [haσ, haσ, abs_mul, abs_of_pos hσ0]
    have := Htheta_le p n hH i hi
    rw [abs_of_pos hx0] at this
    nlinarith
  set A := ∑ i ∈ range n, a i with hAd
  have hAσ : A = σ * ∑ i ∈ range n, x i := by
    rw [hAd, mul_sum]
    exact sum_congr rfl fun i _ => haσ i
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have htail : |∑ i ∈ range k, a (i + 1)| ≤ a 0 * (ρ / (1 - ρ)) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ range k, |a (i + 1)| ≤ ∑ i ∈ range k, a 0 * ρ ^ (i + 1) :=
          sum_le_sum fun i hi => by rw [mul_comm]; exact haH (i + 1) (by simp at hi; omega)
      _ = a 0 * ∑ i ∈ range k, ρ ^ (i + 1) := by rw [mul_sum]
      _ ≤ a 0 * (ρ / (1 - ρ)) := mul_le_mul_of_nonneg_left (geom_tail_le hρ0 (by linarith) k) ha0.le
  have hAsplit : A = a 0 + ∑ i ∈ range k, a (i + 1) := by rw [hAd, sum_range_succ']; ring
  have hlo : (1 - 2 * ρ) / (1 - ρ) * a 0 ≤ A := by
    have : (1 - 2 * ρ) / (1 - ρ) * a 0 = a 0 - a 0 * (ρ / (1 - ρ)) := by field_simp; ring
    rw [this, hAsplit]
    linarith [(abs_le.mp htail).1]
  have hhi : A ≤ a 0 / (1 - ρ) := by
    have : a 0 / (1 - ρ) = a 0 + a 0 * (ρ / (1 - ρ)) := by field_simp; ring
    rw [this, hAsplit]
    linarith [(abs_le.mp htail).2]
  have hA : 0 < A := lt_of_lt_of_le (by positivity) hlo
  have hab : ∀ i < k + 1, |a i| ≤ A * abar ρ i := fun i hi => by
    have h1 : a 0 ≤ (1 - ρ) / (1 - 2 * ρ) * A := by
      rw [div_mul_eq_mul_div, le_div_iff₀ h12]
      have := hlo
      rw [div_mul_eq_mul_div, div_le_iff₀ h1ρ] at this
      linarith
    calc |a i| ≤ ρ ^ i * a 0 := haH i hi
      _ ≤ ρ ^ i * ((1 - ρ) / (1 - 2 * ρ) * A) := mul_le_mul_of_nonneg_left h1 (pow_nonneg hρ0 i)
      _ = A * abar ρ i := by rw [abar]; ring
  have hhF : ∀ i < k + 1, F p (a i / 2) := fun i hi => by
    have := F_zpow_mul p (-1) (haF i hi)
    rwa [zpow_neg, zpow_one, ← div_eq_inv_mul] at this
  have hσs : Real.sqrt (∑ i ∈ range (k + 1), x i) = (2 : ℝ) ^ e * Real.sqrt A := by
    have hx' : ∑ i ∈ range (k + 1), x i = ((2 : ℝ) ^ e) ^ 2 * A := by
      rw [hAσ, hσ, ← mul_assoc, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ (by norm_num)]
      push_cast
      ring_nf
      simp
    rw [hx', Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  exact ⟨haF, ha0, haH, hlo, hhi, hA, hab, hhF, hσs⟩

/-- the end of SQRT: from `r` within `Ey` of `y = a^{-1/2}` with parts within `yπ`, `MUL(r, a)` scaled by `2^e` is
within `(E + ε_z)√x` of `√x`, `(ε_z, ·) = G_MUL(π, ā; 1 + E)` -/
theorem sqrt_final (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {θ : ℝ} (hθ : 0 ≤ θ)
    (hρ : 2 * (θ * u p) < 1) (x : ℕ → ℝ) (hx : ∀ i < n, F p (x i)) (hH : Htheta p n θ x) (hx0 : 0 < x 0)
    (r : ℕ → ℝ) (E : ℝ) (π : ℕ → ℝ) (hr : ∀ i < n, F p (r i))
    (hrπ : ∀ i < n, |r i| ≤ (Real.sqrt (∑ i ∈ range n, sqrtA p x i))⁻¹ * π i)
    (hR : |∑ i ∈ range n, r i - (Real.sqrt (∑ i ∈ range n, sqrtA p x i))⁻¹| ≤
      E * (Real.sqrt (∑ i ∈ range n, sqrtA p x i))⁻¹) :
    |Real.sqrt (∑ i ∈ range n, x i) - ((mulOp p n r (sqrtA p x)).map fun v => (2 : ℝ) ^ sqrtE p (x 0) * v).sum| ≤
      (E + GmulE p n π (abar (θ * u p)) (1 + E)) * Real.sqrt (∑ i ∈ range n, x i) := by
  obtain ⟨haF, -, -, -, -, hA, hab, -, hσs⟩ := sqrt_setup p n hn hθ hρ x hx hH hx0
  set A := ∑ i ∈ range n, sqrtA p x i with hAd
  set y := (Real.sqrt A)⁻¹ with hy
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hy0 : 0 < y := inv_pos.mpr hsA
  set R := ∑ i ∈ range n, r i with hRd
  have hRb : |R| ≤ (1 + E) * y := by
    have := abs_sub_abs_le_abs_sub R y
    rw [abs_of_pos hy0] at this
    linarith
  have hZ : |R * A| ≤ y * A * (1 + E) := by
    rw [abs_mul, abs_of_pos hA]
    calc |R| * A ≤ (1 + E) * y * A := mul_le_mul_of_nonneg_right hRb hA.le
      _ = y * A * (1 + E) := by ring
  obtain ⟨z1, -, -, -⟩ := mul_G p n hp hn hA3 r (sqrtA p x) (fun i => y * π i) (fun j => A * abar (θ * u p) j) hr haF
    hrπ hab _ hZ
  obtain ⟨w1, -⟩ := Gmul_smul p n π (abar (θ * u p)) (1 + E) hy0.le hA.le
  rw [w1] at z1
  have hyA : y * A = Real.sqrt A := by
    rw [hy]
    field_simp
    rw [Real.sq_sqrt hA.le]
  rw [hyA] at z1
  rw [list_sum_map_mul, hσs]
  have hRy : |R * A - Real.sqrt A| ≤ E * Real.sqrt A := by
    rw [show R * A - Real.sqrt A = A * (R - y) by rw [← hyA]; ring, abs_mul, abs_of_pos hA, ← hyA]
    calc A * |R - y| ≤ A * (E * y) := mul_le_mul_of_nonneg_left hR hA.le
      _ = E * (y * A) := by ring
  have hdiff : |Real.sqrt A - (mulOp p n r (sqrtA p x)).sum| ≤
      (E + GmulE p n π (abar (θ * u p)) (1 + E)) * Real.sqrt A := by
    calc |Real.sqrt A - (mulOp p n r (sqrtA p x)).sum| ≤
          |R * A - Real.sqrt A| + |R * A - (mulOp p n r (sqrtA p x)).sum| := by
          rw [abs_sub_comm (R * A)]
          exact abs_sub_le _ _ _
      _ ≤ E * Real.sqrt A + Real.sqrt A * GmulE p n π (abar (θ * u p)) (1 + E) := add_le_add hRy z1
      _ = _ := by ring
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
  calc (2 : ℝ) ^ sqrtE p (x 0) * |Real.sqrt A - (mulOp p n r (sqrtA p x)).sum| ≤
        (2 : ℝ) ^ sqrtE p (x 0) * ((E + GmulE p n π (abar (θ * u p)) (1 + E)) * Real.sqrt A) :=
        mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = _ := by ring

/-- Theorem 21: SQRT_{n,J} of `x` on `H(θ)` with `0 ≤ θ`, `2θu < 1`, `x_0 > 0` and `(n² + n)u < 1` is within `δ_J√x`
of `√x` -/
theorem thm21 (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {θ : ℝ} (hθ : 0 ≤ θ)
    (hρ : 2 * (θ * u p) < 1) (x : ℕ → ℝ) (hx : ∀ i < n, F p (x i)) (hH : Htheta p n θ x) (hx0 : 0 < x 0)
    (J : ℕ) :
    |Real.sqrt (∑ i ∈ range n, x i) - (sqrtOp p n J x).sum| ≤
      sqrtDelta p n (θ * u p) J * Real.sqrt (∑ i ∈ range n, x i) := by
  have hu := u_pos p
  obtain ⟨haF, ha0, -, hlo, hhi, hA, hab, hhF, -⟩ := sqrt_setup p n hn hθ hρ x hx hH hx0
  set ρ := θ * u p with hρd
  have hρ0 : 0 ≤ ρ := mul_nonneg hθ hu.le
  have h1ρ : 0 < 1 - ρ := by linarith
  have h12 : 0 < 1 - 2 * ρ := by linarith
  set a := sqrtA p x with ha
  set A := ∑ i ∈ range n, a i with hAd
  set y := (Real.sqrt A)⁻¹ with hy
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hy0 : 0 < y := inv_pos.mpr hsA
  have hAy : A * y ^ 2 = 1 := by
    rw [hy, inv_pow, Real.sq_sqrt hA.le]
    field_simp
  set h : ℕ → ℝ := fun i => a i / 2 with hh
  have hhb : ∀ i < n, |h i| ≤ A * (abar ρ i / 2) := fun i hi => by
    simp only [hh, abs_div, abs_two]
    have := hab i hi
    linarith
  have hhb0 : ∀ i, 0 ≤ abar ρ i / 2 := fun i => by
    rw [abar]; exact div_nonneg (mul_nonneg (pow_nonneg hρ0 i) (div_nonneg h1ρ.le h12.le)) zero_le_two
  have hHs : ∑ i ∈ range n, h i = A / 2 := by rw [hh, ← sum_div]
  have hstart := sqrt_start p hρ0 (by linarith) ha0 hlo hhi
  have hiter : ∀ j, (∀ i < n, F p (((sqrtStep p n h)^[j] (sqrtR0 p (a 0))) i)) ∧
      (∀ i < n, |((sqrtStep p n h)^[j] (sqrtR0 p (a 0))) i| ≤ y * (sqrtBk p n ρ j).2 i) ∧
      |∑ i ∈ range n, ((sqrtStep p n h)^[j] (sqrtR0 p (a 0))) i - y| ≤ (sqrtBk p n ρ j).1 * y ∧
      0 ≤ (sqrtBk p n ρ j).1 ∧ ∀ i, 0 ≤ (sqrtBk p n ρ j).2 i := by
    intro j
    induction j with
    | zero =>
      have hE0 : 0 ≤ sqrtE0 p ρ := by
        unfold sqrtE0
        refine le_max_of_le_left ?_
        rw [sub_nonneg, le_div_iff₀ h1ρ]
        linarith
      have hsum : ∑ i ∈ range n, sqrtR0 p (a 0) i = RN p (1 / RN p (Real.sqrt (a 0))) := by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        rw [sum_range_succ']
        simp [sqrtR0]
      refine ⟨fun i _ => ?_, fun i _ => ?_, ?_, hE0, fun i => ?_⟩
      · simp only [Function.iterate_zero, id, sqrtR0]
        split_ifs
        · exact F_RN p _
        · exact F_zero p
      · simp only [Function.iterate_zero, id, sqrtR0, sqrtBk]
        split_ifs
        · have := abs_sub_abs_le_abs_sub (RN p (1 / RN p (Real.sqrt (a 0)))) y
          rw [abs_of_pos hy0] at this
          nlinarith
        · simp
      · simp only [Function.iterate_zero, id]
        rw [hsum]
        exact hstart
      · simp only [sqrtBk]
        split_ifs
        · linarith
        · exact le_rfl
    | succ j ih =>
      obtain ⟨i1, i2, i3, i4, i5⟩ := ih
      rw [Function.iterate_succ_apply']
      exact sqrt_step p n hp hn hA3 hy0 hAy h _ hhF hhb hhb0 hHs _ _ _ i4 i5 i1 i2 i3
  obtain ⟨f1, f2, f3, -, -⟩ := hiter J
  have h := sqrt_final p n hp hn hA3 hθ hρ x hx hH hx0 _ _ _ f1 f2 f3
  exact h

end ExpansionBounds
