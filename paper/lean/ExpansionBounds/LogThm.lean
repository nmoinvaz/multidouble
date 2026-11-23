import ExpansionBounds.ExpThm
import ExpansionBounds.FExact
import ExpansionBounds.Sqrt

/-!
# Theorem 42 (`thm:log`): LOG, for a case

LOG's steps (2) to (5) after its start `y_0`: `(k, t)` by EXP's reduction and core on `-y_0`, `x' = 2^k x`,
`φ = ADDF(x', -1)`, `c` from `φ` and `t`, Horner's rule for `log(1 + c)` and the last ADD. The products of steps (4) and
(5) are formed on a factor scaled by a power of two; the exponent range is unbounded, so the scalings are exact and
`η_0 = 0`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ) [Prec_gt_0 p]

omit [Prec_gt_0 p] in
/-- `2^e MUL(2^{-e}a, b)`: LOG's product with the factor `a` scaled near 1 -/
noncomputable def smulOp (e : ℤ) (a b : ℕ → ℝ) : List ℝ :=
  (mulOp p n (fun i => (2 : ℝ) ^ (-e) * a i) b).map fun v => (2 : ℝ) ^ e * v

omit [Prec_gt_0 p] in
theorem getD_map_mul (l : List ℝ) (c : ℝ) (i : ℕ) : (l.map fun v => c * v).getD i 0 = c * l.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

omit [Prec_gt_0 p] in
theorem sum_map_mul (l : List ℝ) (c : ℝ) : (l.map fun v => c * v).sum = c * l.sum := by
  induction l <;> simp [*, mul_add]

/-- the scaled product is within `G_MUL`'s bounds, which scale with the factor -/
theorem smulOp_within (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (e : ℤ) :
    MulWithin p n (smulOp p n e) 0 := by
  intro a b α β Zb ha hb hα hβ hZ
  have hc : (0 : ℝ) < (2 : ℝ) ^ (-e) := by positivity
  have hce : (2 : ℝ) ^ e * (2 : ℝ) ^ (-e) = 1 := by rw [← zpow_add₀ two_ne_zero]; simp
  have h := mul_G p n hp hn hA3 (fun i => (2 : ℝ) ^ (-e) * a i) b (fun i => (2 : ℝ) ^ (-e) * α i) β
    (fun i hi => F_zpow_mul p _ (ha i hi)) hb
    (fun i hi => by rw [abs_mul, abs_of_pos hc]; exact mul_le_mul_of_nonneg_left (hα i hi) hc.le) hβ
    ((2 : ℝ) ^ (-e) * Zb) (by
      rw [← mul_sum, mul_assoc, abs_mul, abs_of_pos hc]; exact mul_le_mul_of_nonneg_left hZ hc.le)
  have hG := Gmul_smul p n α β Zb hc.le zero_le_one
  simp only [one_mul, mul_one] at hG
  rw [hG.1] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [mul_zero, add_zero, smulOp]
  refine ⟨?_, fun i => ?_, fun i => ?_, by rw [List.length_map]; exact h4⟩
  · rw [sum_map_mul]
    have e1 : (∑ i ∈ range n, a i) * (∑ j ∈ range n, b j) -
        (2 : ℝ) ^ e * (mulOp p n (fun i => (2 : ℝ) ^ (-e) * a i) b).sum =
        (2 : ℝ) ^ e * ((∑ i ∈ range n, (2 : ℝ) ^ (-e) * a i) * (∑ j ∈ range n, b j) -
          (mulOp p n (fun i => (2 : ℝ) ^ (-e) * a i) b).sum) := by
      rw [← mul_sum, mul_sub, ← mul_assoc, ← mul_assoc, hce, one_mul]
    rw [e1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ e)]
    calc (2 : ℝ) ^ e * |_| ≤ (2 : ℝ) ^ e * ((2 : ℝ) ^ (-e) * GmulE p n α β Zb) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = GmulE p n α β Zb := by rw [← mul_assoc, hce, one_mul]
  · rw [getD_map_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ e)]
    calc (2 : ℝ) ^ e * |_| ≤ (2 : ℝ) ^ e * ((2 : ℝ) ^ (-e) * GmulP p n α β Zb i) :=
          mul_le_mul_of_nonneg_left ((h2 i).trans_eq (hG.2 i)) (by positivity)
      _ = GmulP p n α β Zb i := by rw [← mul_assoc, hce, one_mul]
  · rw [getD_map_mul]; exact F_zpow_mul p _ (h3 i)

/-! ## The series of `log(1 + c)` -/

omit [Prec_gt_0 p] in
/-- `|log(1 + c) - S_q(c)| ≤ |c|^{q+1}/((q + 1)(1 - |c|))`, `S_q(c) = -∑_{i<q} (-c)^{i+1}/(i + 1)` -/
theorem log_tail {c : ℝ} (hc : |c| < 1) (q : ℕ) :
    |Real.log (1 + c) + ∑ i ∈ range q, (-c) ^ (i + 1) / (i + 1)| ≤ |c| ^ (q + 1) / ((q + 1) * (1 - |c|)) := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := -c) (by rwa [abs_neg])
  rw [sub_neg_eq_add] at hs
  have ht := (hasSum_nat_add_iff' q).mpr hs
  have hq : (0 : ℝ) < q + 1 := by positivity
  have hg : HasSum (fun i : ℕ => |c| ^ (q + 1) / (q + 1) * |c| ^ i) (|c| ^ (q + 1) / (q + 1) * (1 - |c|)⁻¹) :=
    (hasSum_geometric_of_lt_one (abs_nonneg c) hc).mul_left _
  have hle : ∀ i : ℕ, ‖(-c) ^ (i + q + 1) / ((i + q : ℕ) + 1 : ℝ)‖ ≤ |c| ^ (q + 1) / (q + 1) * |c| ^ i := by
    intro i
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (i + q : ℕ) + 1),
      show i + q + 1 = (q + 1) + i by ring, pow_add, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_left (by positivity) hq ?_
    push_cast
    linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have h := ht.norm_le_of_bounded hg hle
  rw [Real.norm_eq_abs, show -Real.log (1 + c) - ∑ i ∈ range q, (-c) ^ (i + 1) / ((i : ℝ) + 1) =
    -(Real.log (1 + c) + ∑ i ∈ range q, (-c) ^ (i + 1) / ((i : ℝ) + 1)) by ring, abs_neg] at h
  refine h.trans_eq ?_
  rw [div_mul_eq_div_div, div_eq_mul_inv (|c| ^ (q + 1) / ((q : ℝ) + 1))]

omit [Prec_gt_0 p] in
/-- `|log(1 + x) - log(1 + y)| ≤ |x - y|/(1 - C)` for `|x|, |y| ≤ C < 1` -/
theorem log_lip {x y C : ℝ} (hx : |x| ≤ C) (hy : |y| ≤ C) (hC : C < 1) :
    |Real.log (1 + x) - Real.log (1 + y)| ≤ |x - y| / (1 - C) := by
  have hx1 : 0 < 1 + x := by linarith [neg_abs_le x]
  have hy1 : 0 < 1 + y := by linarith [neg_abs_le y]
  have hC0 : 0 < 1 - C := by linarith
  rw [abs_le]
  constructor
  · have h := Real.log_le_sub_one_of_pos (div_pos hy1 hx1)
    rw [Real.log_div hy1.ne' hx1.ne'] at h
    have h2 : (1 + y) / (1 + x) - 1 ≤ |x - y| / (1 - C) := by
      rw [div_sub_one hx1.ne', show 1 + y - (1 + x) = y - x by ring]
      calc (y - x) / (1 + x) ≤ |x - y| / (1 + x) := div_le_div_of_nonneg_right (by
            rw [abs_sub_comm]; exact le_abs_self _) hx1.le
        _ ≤ |x - y| / (1 - C) := div_le_div_of_nonneg_left (abs_nonneg _) hC0 (by linarith [neg_abs_le x])
    linarith
  · have h := Real.log_le_sub_one_of_pos (div_pos hx1 hy1)
    rw [Real.log_div hx1.ne' hy1.ne'] at h
    have h2 : (1 + x) / (1 + y) - 1 ≤ |x - y| / (1 - C) := by
      rw [div_sub_one hy1.ne', show 1 + x - (1 + y) = x - y by ring]
      calc (x - y) / (1 + y) ≤ |x - y| / (1 + y) := div_le_div_of_nonneg_right (le_abs_self _) hy1.le
        _ ≤ |x - y| / (1 - C) := div_le_div_of_nonneg_left (abs_nonneg _) hC0 (by linarith [neg_abs_le y])
    linarith

/-! ## Step (5): `log(1 + c)` -/

omit [Prec_gt_0 p] in
/-- `(-1)^{i+1}/i`, the coefficients of `log(1 + c)` -/
noncomputable def logFe (i : ℕ) : ℝ := (-1) ^ (i + 1) / i

omit [Prec_gt_0 p] in
/-- `v_i = ∑_{l ≤ q - i} C^l/(i + l)`: `v_q = 1/q` and `v_i = 1/i + Cv_{i+1}` -/
noncomputable def logV (C : ℝ) (q i : ℕ) : ℝ := ∑ l ∈ range (q + 1 - i), C ^ l / ((i + l : ℕ) : ℝ)

/-- step (5): `y_c = c` where `e_c < -B - 13`; otherwise `h` by Horner's rule on the `F'_i` with
`c ⊗ v = 2^{e_c}MUL(2^{-e_c}c, v)`, and `y_c = c ⊗ ADDF(c ⊗ h, 1)` -/
noncomputable def logYc (B ec : ℤ) (c : ℕ → ℝ) (F' : ℕ → ℕ → ℝ) (q : ℕ) : ℕ → ℝ :=
  if ec < -B - 13 then c else
    pt (smulOp p n ec c (pt (addfOp p n (pt (smulOp p n ec c (hornerP p n (smulOp p n ec) c F' q (q - 2)))) 1)))

omit [Prec_gt_0 p] in
/-- step (5)'s bounds: `(e_2, π^h_2)` of Lemma 33 for `z = c`, `z̄ = C`, `π^z = χ`;
`(ε^h, ω^h) = G_MUL(χ, π^h_2; C(v_2 + e_2))`, `h̄ = C(v_2 + e_2) + ε^h`,
`(ε^g, ω^g) = G_ADDF(ω^h, 1; 1 + h̄, 1 + h̄ + ∑_{j≥1}ω^h_j)`, `(ε^r, ω'_r) = G_MUL(χ, ω^g; C(1 + h̄ + ε^g))`,
`ω_r = max(ω'_r, χ)` and `P = ε^r + C(ε^g + ε^h + Ce_2) + max(C^{q+1}/(q + 1), 2^{-B-13}C)/(1 - C) + E_c/(1 - C)` -/
noncomputable def logP (χ : ℕ → ℝ) (C Ec : ℝ) (F' : ℕ → ℕ → ℝ) (φ' : ℕ → ℝ) (q : ℕ) (B : ℤ) : ℝ × (ℕ → ℝ) :=
  let H := hornerB p n χ C 0 0 F' φ' (logV C q) q (q - 2)
  let Zh := C * (logV C q 2 + H.1)
  let ωh := GmulP p n χ H.2 Zh
  let hb := Zh + GmulE p n χ H.2 Zh
  let εg := GaddfE' p n ωh (1 + hb + ∑ j ∈ Ico 1 n, ωh j) (1 + hb)
  let ωg := GaddfP' p n ωh (1 + hb + ∑ j ∈ Ico 1 n, ωh j) (1 + hb)
  let Zr := C * (1 + hb + εg)
  (GmulE p n χ ωg Zr + C * (εg + GmulE p n χ H.2 Zh + C * H.1) +
      max (C ^ (q + 1) / (q + 1)) ((2 : ℝ) ^ (-B - 13) * C) / (1 - C) + Ec / (1 - C),
    fun i => max (GmulP p n χ ωg Zr i) (χ i))

omit [Prec_gt_0 p] in
theorem logV_nonneg {C : ℝ} (hC : 0 ≤ C) (q i : ℕ) : 0 ≤ logV C q i :=
  sum_nonneg fun l _ => div_nonneg (pow_nonneg hC l) (Nat.cast_nonneg _)

omit [Prec_gt_0 p] in
/-- `|∑_{l ≤ q - k} (-1)^{k+l+1} z^l/(k + l)| ≤ v_k` for `|z| ≤ C` -/
theorem logV_bound {z C : ℝ} (hz : |z| ≤ C) (q k : ℕ) : |hornerE logFe z q k| ≤ logV C q k := by
  unfold hornerE logV
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ => ?_)
  rw [logFe, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_pow, Nat.cast_add, abs_of_nonneg
    (by positivity : (0 : ℝ) ≤ (k : ℝ) + l), div_mul_eq_mul_div, one_mul]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg z) hz l) (by positivity)

omit [Prec_gt_0 p] in
/-- `S_q(c) = -∑_{i<q} (-c)^{i+1}/(i + 1) = c + c²H(c)`, `H(c) = ∑_{l ≤ q-2} (-1)^{l+3} c^l/(l + 2)` -/
theorem logS_eq (z : ℝ) (q : ℕ) (hq : 2 ≤ q) :
    -∑ i ∈ range q, (-z) ^ (i + 1) / ((i : ℝ) + 1) = z + z ^ 2 * hornerE logFe z q 2 := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
  unfold hornerE logFe
  rw [show q' + 2 + 1 - 2 = q' + 1 by omega, show q' + 2 = (q' + 1) + 1 by ring, sum_range_succ', mul_sum, neg_add]
  simp only [Nat.cast_zero, zero_add, pow_one, div_one, neg_neg]
  rw [add_comm]
  congr 1
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun l _ => ?_
  push_cast
  rw [show (2 : ℝ) + l = (l : ℝ) + 1 + 1 by ring, show (2 + l + 1) = l + 1 + 1 + 1 by ring]
  rw [neg_pow]
  ring

/-- step (5) without the drop: `|y_c - S_q(c)| ≤ ε^r + C(ε^g + ε^h + Ce_2)` for `|c| ≤ C`, with the parts of `y_c`
within `ω'_r` -/
theorem log_horner (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (c : ℕ → ℝ)
    (hc : ∀ i < n, F p (c i)) (χ : ℕ → ℝ) (hχ0 : ∀ i, 0 ≤ χ i) (hχ : ∀ i < n, |c i| ≤ χ i) (C : ℝ)
    (hcC : |∑ i ∈ range n, c i| ≤ C) (F' : ℕ → ℕ → ℝ) (hF' : ∀ k, ∀ i < n, F p (F' k i)) (φ' : ℕ → ℝ)
    (hφ' : ∀ k, |∑ i ∈ range n, F' k i - logFe k| ≤ φ' k) (q : ℕ) (hq : 2 ≤ q) (ec : ℤ) :
    let H := hornerB p n χ C 0 0 F' φ' (logV C q) q (q - 2)
    let Zh := C * (logV C q 2 + H.1)
    let ωh := GmulP p n χ H.2 Zh
    let hb := Zh + GmulE p n χ H.2 Zh
    let εg := GaddfE' p n ωh (1 + hb + ∑ j ∈ Ico 1 n, ωh j) (1 + hb)
    let ωg := GaddfP' p n ωh (1 + hb + ∑ j ∈ Ico 1 n, ωh j) (1 + hb)
    let Zr := C * (1 + hb + εg)
    let yc := pt (smulOp p n ec c (pt (addfOp p n (pt (smulOp p n ec c (hornerP p n (smulOp p n ec) c F' q (q - 2))))
      1)))
    |∑ i ∈ range n, yc i - -∑ i ∈ range q, (-∑ i ∈ range n, c i) ^ (i + 1) / ((i : ℝ) + 1)| ≤
        GmulE p n χ ωg Zr + C * (εg + GmulE p n χ H.2 Zh + C * H.1) ∧
      (∀ i < n, |yc i| ≤ GmulP p n χ ωg Zr i) ∧ ∀ i < n, F p (yc i) := by
  intro H Zh ωh hb εg ωg Zr yc
  have hM := smulOp_within p n hp hn hA3 ec
  set cs := ∑ i ∈ range n, c i with hcsd
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hcC
  have hφ0 : ∀ k, 0 ≤ φ' k := fun k => (abs_nonneg _).trans (hφ' k)
  -- Lemma 33 at `k = 2`
  obtain ⟨hh1, hh2, hh3⟩ := horner_step p n hp hn hA3 hM c hc χ hχ cs C 0 hcC le_rfl (by simp [hcsd]) F' hF' logFe
    φ' (logV C q) hφ' q 2 (fun k _ _ => logV_bound hcC q k) (q - 2) le_rfl
  rw [show q - (q - 2) = 2 by omega] at hh1
  obtain ⟨hH0, hH20⟩ := hornerB_nonneg p n hA3 hχ0 (le_trans (abs_nonneg _) hcC) le_rfl le_rfl F' hφ0
    (logV_nonneg hC0 q) q (q - 2)
  set h := hornerP p n (smulOp p n ec) c F' q (q - 2) with hhd
  set He := hornerE logFe cs q 2 with hHe
  set Hs := ∑ i ∈ range n, h i with hHs
  have hHe2 : |He| ≤ logV C q 2 := logV_bound hcC q 2
  have hHs : |Hs| ≤ logV C q 2 + H.1 := by
    have := abs_sub_abs_le_abs_sub Hs He
    linarith
  -- `ĥ = c ⊗ h`
  have hZh : |cs * Hs| ≤ Zh := by
    rw [abs_mul]; exact mul_le_mul hcC hHs (abs_nonneg _) hC0
  obtain ⟨m1, m2, m3, m4⟩ := hM c h χ H.2 Zh hc hh3 hχ hh2 hZh
  simp only [mul_zero, add_zero] at m1 m2
  set hh := smulOp p n ec c h with hhhd
  have hhs : hh.sum = ∑ i ∈ range n, pt hh i := list_sum_getD hh n m4
  set hs := hh.sum with hsd
  have hsb : |hs| ≤ hb := by
    have := abs_sub_abs_le_abs_sub (cs * Hs) hs
    rw [abs_sub_comm] at m1
    have := abs_sub_abs_le_abs_sub hs (cs * Hs)
    linarith
  -- `g = ADDF(ĥ, 1)`
  have hlam : |pt hh 0 + 1| ≤ 1 + hb + ∑ j ∈ Ico 1 n, ωh j := by
    have h0 : pt hh 0 = hs - ∑ j ∈ Ico 1 n, pt hh j := by
      rw [hhs, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]; ring
    rw [h0]
    have : |∑ j ∈ Ico 1 n, pt hh j| ≤ ∑ j ∈ Ico 1 n, ωh j :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => m2 j)
    calc |hs - ∑ j ∈ Ico 1 n, pt hh j + 1| ≤ 1 + |hs| + |∑ j ∈ Ico 1 n, pt hh j| := by
          have := abs_add_le (hs - ∑ j ∈ Ico 1 n, pt hh j) 1
          have := abs_sub hs (∑ j ∈ Ico 1 n, pt hh j)
          rw [abs_one] at *; linarith
      _ ≤ 1 + hb + ∑ j ∈ Ico 1 n, ωh j := by linarith
  have hZg : |∑ i ∈ range n, pt hh i + 1| ≤ 1 + hb := by
    rw [← hhs]; have := abs_add_le hs 1; rw [abs_one] at this; linarith
  obtain ⟨g1, g2, g3, g4⟩ := addf_G' p n hp hn (pt hh) 1 ωh (fun i _ => m3 i) (F_one p) (fun i _ => m2 i) _ hlam
    (1 + hb) hZg
  set g := addfOp p n (pt hh) 1 with hgd
  have hgs : g.sum = ∑ i ∈ range n, pt g i := list_sum_getD g n g4
  have hGb : |g.sum| ≤ 1 + hb + εg := by
    have g1' : |g.sum - (∑ i ∈ range n, pt hh i + 1)| ≤ εg := by rw [abs_sub_comm]; exact g1
    have := abs_sub_abs_le_abs_sub g.sum (∑ i ∈ range n, pt hh i + 1)
    linarith
  -- `y_c = c ⊗ g`
  have hZr : |cs * ∑ i ∈ range n, pt g i| ≤ Zr := by
    rw [← hgs, abs_mul]; exact mul_le_mul hcC hGb (abs_nonneg _) hC0
  obtain ⟨r1, r2, r3, r4⟩ := hM c (pt g) χ ωg Zr hc (fun i _ => g3 i) hχ (fun i _ => g2 i) hZr
  simp only [mul_zero, add_zero] at r1 r2
  have hys : (smulOp p n ec c (pt g)).sum = ∑ i ∈ range n, yc i := list_sum_getD _ n r4
  refine ⟨?_, fun i _ => r2 i, fun i _ => r3 i⟩
  rw [logS_eq cs q hq, ← hys]
  rw [← hgs] at r1
  rw [← hhs] at g1
  have e : (smulOp p n ec c (pt g)).sum - (cs + cs ^ 2 * He) =
      -(cs * g.sum - (smulOp p n ec c (pt g)).sum) - cs * (hs + 1 - g.sum) + cs * (hs - cs * Hs) +
        cs ^ 2 * (Hs - He) := by ring
  rw [e]
  set X1 := cs * g.sum - (smulOp p n ec c (pt g)).sum
  set X2 := hs + 1 - g.sum
  set X3 := hs - cs * Hs
  set X4 := Hs - He
  have t : |-X1 - cs * X2 + cs * X3 + cs ^ 2 * X4| ≤ |X1| + |cs| * |X2| + |cs| * |X3| + |cs| ^ 2 * |X4| :=
    calc |-X1 - cs * X2 + cs * X3 + cs ^ 2 * X4| ≤ |-X1 - cs * X2 + cs * X3| + |cs ^ 2 * X4| := abs_add_le _ _
      _ ≤ |-X1 - cs * X2| + |cs * X3| + |cs ^ 2 * X4| := by gcongr; exact abs_add_le _ _
      _ ≤ |-X1| + |cs * X2| + |cs * X3| + |cs ^ 2 * X4| := by gcongr; exact abs_sub _ _
      _ = |X1| + |cs| * |X2| + |cs| * |X3| + |cs| ^ 2 * |X4| := by rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_pow]
  have b1 : |X1| ≤ GmulE p n χ ωg Zr := r1
  have b2 : |cs| * |X2| ≤ C * εg := mul_le_mul hcC g1 (abs_nonneg _) hC0
  have b3 : |cs| * |X3| ≤ C * GmulE p n χ H.2 Zh :=
    mul_le_mul hcC (by rw [abs_sub_comm]; exact m1) (abs_nonneg _) hC0
  have b4 : |cs| ^ 2 * |X4| ≤ C ^ 2 * H.1 :=
    mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hcC 2) hh1 (abs_nonneg _) (by positivity)
  calc _ ≤ |X1| + |cs| * |X2| + |cs| * |X3| + |cs| ^ 2 * |X4| := t
    _ ≤ GmulE p n χ ωg Zr + C * εg + C * GmulE p n χ H.2 Zh + C ^ 2 * H.1 := by linarith
    _ = GmulE p n χ ωg Zr + C * (εg + GmulE p n χ H.2 Zh + C * H.1) := by ring

/-- step (5): for `c` within `E_c` of `c*`, `|c*| ≤ c̄*` and `C = c̄* + E_c < 1`, `y_c` is within `P` of `log(1 + c*)`,
with parts within `ω_r` -/
theorem log_step5 (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (c : ℕ → ℝ)
    (hc : ∀ i < n, F p (c i)) (χ : ℕ → ℝ) (hχ0 : ∀ i, 0 ≤ χ i) (hχ : ∀ i < n, |c i| ≤ χ i) (cs cb Ec : ℝ)
    (hcs : |cs| ≤ cb) (hEc : |∑ i ∈ range n, c i - cs| ≤ Ec) (hC : cb + Ec < 1) (F' : ℕ → ℕ → ℝ)
    (hF' : ∀ k, ∀ i < n, F p (F' k i)) (φ' : ℕ → ℝ) (hφ' : ∀ k, |∑ i ∈ range n, F' k i - logFe k| ≤ φ' k)
    (q : ℕ) (hq : 2 ≤ q) (B ec : ℤ) (γ : ℝ) (hγ : (1 + u p) ^ n ≤ 1 + γ)
    (hU : expU p n γ c < (2 : ℝ) ^ (ec + 1)) :
    |∑ i ∈ range n, logYc p n B ec c F' q i - Real.log (1 + cs)| ≤ (logP p n χ (cb + Ec) Ec F' φ' q B).1 ∧
      (∀ i < n, |logYc p n B ec c F' q i| ≤ (logP p n χ (cb + Ec) Ec F' φ' q B).2 i) ∧
      ∀ i < n, F p (logYc p n B ec c F' q i) := by
  set C := cb + Ec with hCd
  set S := ∑ i ∈ range n, c i with hSd
  have hEc0 : 0 ≤ Ec := (abs_nonneg _).trans hEc
  have hcb0 : 0 ≤ cb := (abs_nonneg _).trans hcs
  have hC0 : 0 ≤ C := by linarith
  have hC1 : 0 < 1 - C := by linarith
  have hSC : |S| ≤ C := by
    have := abs_sub_abs_le_abs_sub S cs
    linarith
  have hcsC : |cs| ≤ C := by linarith
  have hlip : |Real.log (1 + S) - Real.log (1 + cs)| ≤ Ec / (1 - C) :=
    (log_lip hSC hcsC hC).trans (div_le_div_of_nonneg_right hEc hC1.le)
  have hφ0 : ∀ k, 0 ≤ φ' k := fun k => (abs_nonneg _).trans (hφ' k)
  obtain ⟨hH0, hH20⟩ := hornerB_nonneg p n hA3 hχ0 hC0 le_rfl le_rfl F' hφ0 (logV_nonneg hC0 q) q (q - 2)
  set H := hornerB p n χ C 0 0 F' φ' (logV C q) q (q - 2) with hHd
  set Zh := C * (logV C q 2 + H.1) with hZh
  have hZh0 : 0 ≤ Zh := mul_nonneg hC0 (add_nonneg (logV_nonneg hC0 q 2) hH0)
  obtain ⟨hεh0, hωh0⟩ := Gmul_nonneg p n hA3 hχ0 hH20 hZh0
  set ωh := GmulP p n χ H.2 Zh with hωh
  set hb := Zh + GmulE p n χ H.2 Zh with hhb
  have hhb0 : 0 ≤ hb := by linarith
  have hlam0 : 0 ≤ 1 + hb + ∑ j ∈ Ico 1 n, ωh j := by
    have := sum_nonneg fun j (_ : j ∈ Ico 1 n) => hωh0 j
    linarith
  have hX := addfX_nonneg p n hωh0 hlam0
  set εg := GaddfE' p n ωh (1 + hb + ∑ j ∈ Ico 1 n, ωh j) (1 + hb) with hεg
  set ωg := GaddfP' p n ωh (1 + hb + ∑ j ∈ Ico 1 n, ωh j) (1 + hb) with hωg
  have hεg0 : 0 ≤ εg := gErr_nonneg p n hX (by linarith) le_rfl
  have hωg0 : ∀ i, 0 ≤ ωg i := gParts_nonneg p n hX (by linarith) le_rfl
  set Zr := C * (1 + hb + εg) with hZr
  obtain ⟨hεr0, -⟩ := Gmul_nonneg p n hA3 hχ0 hωg0 (Zb := Zr) (mul_nonneg hC0 (by linarith))
  set M := max (C ^ (q + 1) / (q + 1)) ((2 : ℝ) ^ (-B - 13) * C) with hM
  have hP : (logP p n χ C Ec F' φ' q B).1 = GmulE p n χ ωg Zr + C * (εg + GmulE p n χ H.2 Zh + C * H.1) +
      M / (1 - C) + Ec / (1 - C) := rfl
  have hP2 : (logP p n χ C Ec F' φ' q B).2 = fun i => max (GmulP p n χ ωg Zr i) (χ i) := rfl
  rw [hP, hP2]
  have hrest : 0 ≤ GmulE p n χ ωg Zr + C * (εg + GmulE p n χ H.2 Zh + C * H.1) :=
    add_nonneg hεr0 (mul_nonneg hC0 (add_nonneg (add_nonneg hεg0 hεh0) (mul_nonneg hC0 hH0)))
  unfold logYc
  split_ifs with hd
  · -- `y_c = c`, with `|c| < 2^{-B-13}`
    refine ⟨?_, fun i hi => (hχ i hi).trans (le_max_right _ _), hc⟩
    have hSs : |S| ≤ (2 : ℝ) ^ (-B - 13) := by
      have h1 := (abs_sum_le_sum_abs _ _).trans ((expU_ge p n hn γ hγ c).trans hU.le)
      exact h1.trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
    have ht := log_tail (lt_of_le_of_lt hSC hC) 1
    simp only [range_one, sum_singleton, Nat.cast_zero, Nat.cast_one, zero_add, pow_one, div_one] at ht
    have h2 : |S| ^ (1 + 1) / ((1 + 1) * (1 - |S|)) ≤ M / (1 - C) := by
      rw [show |S| ^ (1 + 1) = |S| * |S| by ring, div_le_div_iff₀ (by nlinarith [abs_nonneg S]) hC1]
      have hm : (2 : ℝ) ^ (-B - 13) * C ≤ M := le_max_right _ _
      have h3 : |S| * |S| ≤ (2 : ℝ) ^ (-B - 13) * C := mul_le_mul hSs hSC (abs_nonneg _) (by positivity)
      have h4 : 1 - C ≤ (1 + 1) * (1 - |S|) := by linarith [abs_nonneg S]
      calc |S| * |S| * (1 - C) ≤ M * (1 - C) := mul_le_mul_of_nonneg_right (h3.trans hm) hC1.le
        _ ≤ M * ((1 + 1) * (1 - |S|)) := mul_le_mul_of_nonneg_left h4 ((by positivity : (0 : ℝ) ≤
            (2 : ℝ) ^ (-B - 13) * C).trans hm)
    have h5 : |S - Real.log (1 + S)| ≤ M / (1 - C) := by
      rw [abs_sub_comm, show Real.log (1 + S) - S = Real.log (1 + S) + -S by ring]
      exact ht.trans h2
    calc |S - Real.log (1 + cs)| ≤ |S - Real.log (1 + S)| + |Real.log (1 + S) - Real.log (1 + cs)| :=
          abs_sub_le _ _ _
      _ ≤ M / (1 - C) + Ec / (1 - C) := add_le_add h5 hlip
      _ ≤ _ := by linarith
  · obtain ⟨y1, y2, y3⟩ := log_horner p n hp hn hA3 c hc χ hχ0 hχ C hSC F' hF' φ' hφ' q hq ec
    refine ⟨?_, fun i hi => (y2 i hi).trans (le_max_left _ _), y3⟩
    have ht := log_tail (lt_of_le_of_lt hSC hC) q
    have h2 : |S| ^ (q + 1) / ((q + 1) * (1 - |S|)) ≤ M / (1 - C) := by
      have hq0 : (0 : ℝ) < q + 1 := by positivity
      calc |S| ^ (q + 1) / ((q + 1) * (1 - |S|)) ≤ C ^ (q + 1) / ((q + 1) * (1 - C)) :=
            div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) hSC _) (by positivity)
              (mul_le_mul_of_nonneg_left (by linarith) hq0.le)
        _ = C ^ (q + 1) / (q + 1) / (1 - C) := by rw [div_div]
        _ ≤ M / (1 - C) := div_le_div_of_nonneg_right (le_max_left _ _) hC1.le
    have h5 : |-∑ i ∈ range q, (-S) ^ (i + 1) / ((i : ℝ) + 1) - Real.log (1 + S)| ≤ M / (1 - C) := by
      rw [abs_sub_comm, sub_neg_eq_add]
      exact ht.trans h2
    calc _ ≤ |∑ i ∈ range n, _ - -∑ i ∈ range q, (-S) ^ (i + 1) / ((i : ℝ) + 1)| +
          |-∑ i ∈ range q, (-S) ^ (i + 1) / ((i : ℝ) + 1) - Real.log (1 + S)| +
          |Real.log (1 + S) - Real.log (1 + cs)| := by
          refine (abs_sub_le _ _ _).trans (add_le_add (abs_sub_le _ _ _) le_rfl)
      _ ≤ (GmulE p n χ ωg Zr + C * (εg + GmulE p n χ H.2 Zh + C * H.1)) + M / (1 - C) + Ec / (1 - C) :=
          add_le_add (add_le_add y1 h5) hlip
      _ = _ := by ring

/-! ## Step (4): `c` from `φ` and `t` -/

omit [Prec_gt_0 p] in
/-- `e^y - 1 - y` grows on `y ≥ 0` -/
theorem expm1_sub_mono {y y' : ℝ} (h0 : 0 ≤ y) (h : y ≤ y') : Real.exp y - 1 - y ≤ Real.exp y' - 1 - y' := by
  have h1 : Real.exp y' - Real.exp y = Real.exp y * (Real.exp (y' - y) - 1) := by
    rw [mul_sub, ← Real.exp_add]; ring_nf
  have h2 : y' - y ≤ Real.exp (y' - y) - 1 := by linarith [Real.add_one_le_exp (y' - y)]
  have h3 : 1 ≤ Real.exp y := Real.one_le_exp h0
  nlinarith

omit [Prec_gt_0 p] in
/-- `e^{-x} + e^x - 2 ≤ 2(e^{|x|} - 1 - |x|)`, as `sinh|x| ≥ |x|` -/
theorem cosh_sub_two_le (x : ℝ) : Real.exp (-x) + Real.exp x - 2 ≤ 2 * (Real.exp |x| - 1 - |x|) := by
  have key : ∀ y : ℝ, 0 ≤ y → Real.exp (-y) + Real.exp y - 2 ≤ 2 * (Real.exp y - 1 - y) := by
    intro y hy
    -- `e^y ≥ A = 1 + y + y²/2` and `A - 1/A ≥ 2y`
    have hA := Real.quadratic_le_exp_of_nonneg hy
    have hA0 : 0 < 1 + y + y ^ 2 / 2 := by positivity
    have he : Real.exp (-y) ≤ 1 / (1 + y + y ^ 2 / 2) := by
      rw [Real.exp_neg, ← one_div]; exact one_div_le_one_div_of_le hA0 hA
    have h2 : 1 / (1 + y + y ^ 2 / 2) ≤ 1 + y + y ^ 2 / 2 - 2 * y := by
      rw [div_le_iff₀ hA0]; nlinarith [sq_nonneg y, pow_nonneg hy 4]
    have h3 : 1 + y + y ^ 2 / 2 - 2 * y ≤ Real.exp y - 2 * y := by linarith
    linarith
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; exact key x h
  · rw [abs_of_nonpos h]
    have := key (-x) (by linarith)
    rw [neg_neg] at this
    linarith

/-- step (4)'s product `p = 2^{e_t}(2^{e_φ}MUL(2^{-e_φ}φ, 2^{-e_t}t))` is within `G_MUL(π^φ, ψ; Z̄)` of `φt` -/
theorem pOp_bound (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (eφ et : ℤ) (φ t : ℕ → ℝ)
    (hφ : ∀ i < n, F p (φ i)) (ht : ∀ i < n, F p (t i)) (πφ ψ : ℕ → ℝ) (hπφ : ∀ i < n, |φ i| ≤ πφ i)
    (hψ : ∀ i < n, |t i| ≤ ψ i) (Zb : ℝ) (hZ : |(∑ i ∈ range n, φ i) * ∑ i ∈ range n, t i| ≤ Zb) :
    let P := fun i => (2 : ℝ) ^ et * pt (smulOp p n eφ φ fun i => (2 : ℝ) ^ (-et) * t i) i
    |(∑ i ∈ range n, φ i) * (∑ i ∈ range n, t i) - ∑ i ∈ range n, P i| ≤ GmulE p n πφ ψ Zb ∧
      (∀ i, |P i| ≤ GmulP p n πφ ψ Zb i) ∧ ∀ i, F p (P i) := by
  intro P
  have hc : (0 : ℝ) < (2 : ℝ) ^ (-et) := by positivity
  have hce : (2 : ℝ) ^ et * (2 : ℝ) ^ (-et) = 1 := by rw [← zpow_add₀ two_ne_zero]; simp
  have hG := Gmul_smul p n πφ ψ Zb zero_le_one hc.le
  simp only [one_mul] at hG
  obtain ⟨m1, m2, m3, m4⟩ := smulOp_within p n hp hn hA3 eφ φ (fun i => (2 : ℝ) ^ (-et) * t i) πφ
    (fun j => (2 : ℝ) ^ (-et) * ψ j) ((2 : ℝ) ^ (-et) * Zb) hφ (fun i hi => F_zpow_mul p _ (ht i hi)) hπφ
    (fun i hi => by rw [abs_mul, abs_of_pos hc]; exact mul_le_mul_of_nonneg_left (hψ i hi) hc.le)
    (by rw [← mul_sum, mul_left_comm, abs_mul, abs_of_pos hc]; exact mul_le_mul_of_nonneg_left hZ hc.le)
  simp only [mul_zero, add_zero] at m1 m2
  rw [hG.1] at m1
  have hs : (smulOp p n eφ φ fun i => (2 : ℝ) ^ (-et) * t i).sum =
      ∑ i ∈ range n, pt (smulOp p n eφ φ fun i => (2 : ℝ) ^ (-et) * t i) i := list_sum_getD _ n m4
  have hPs : ∑ i ∈ range n, P i = (2 : ℝ) ^ et * (smulOp p n eφ φ fun i => (2 : ℝ) ^ (-et) * t i).sum := by
    rw [hs, mul_sum]
  refine ⟨?_, fun i => ?_, fun i => F_zpow_mul p _ (m3 i)⟩
  · rw [hPs, ← mul_sum, mul_left_comm] at *
    have e1 : (∑ i ∈ range n, φ i) * (∑ i ∈ range n, t i) -
        (2 : ℝ) ^ et * (smulOp p n eφ φ fun i => (2 : ℝ) ^ (-et) * t i).sum =
        (2 : ℝ) ^ et * ((2 : ℝ) ^ (-et) * ((∑ i ∈ range n, φ i) * ∑ i ∈ range n, t i) -
          (smulOp p n eφ φ fun i => (2 : ℝ) ^ (-et) * t i).sum) := by
      rw [mul_sub, ← mul_assoc, hce, one_mul]
    rw [e1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ et)]
    calc (2 : ℝ) ^ et * |_| ≤ (2 : ℝ) ^ et * ((2 : ℝ) ^ (-et) * GmulE p n πφ ψ Zb) :=
          mul_le_mul_of_nonneg_left m1 (by positivity)
      _ = GmulE p n πφ ψ Zb := by rw [← mul_assoc, hce, one_mul]
  · show |(2 : ℝ) ^ et * pt _ i| ≤ _
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ et)]
    calc (2 : ℝ) ^ et * |_| ≤ (2 : ℝ) ^ et * ((2 : ℝ) ^ (-et) * GmulP p n πφ ψ Zb i) :=
          mul_le_mul_of_nonneg_left ((m2 i).trans_eq (hG.2 i)) (by positivity)
      _ = GmulP p n πφ ψ Zb i := by rw [← mul_assoc, hce, one_mul]

omit [Prec_gt_0 p] in
/-- step (4): `c = ADD(φ, t)` where `min(e_φ, e_t) < -B - 13`; otherwise `c = ADD(ADD(φ, t), p)` -/
noncomputable def logC (B eφ et : ℤ) (φ t : ℕ → ℝ) : ℕ → ℝ :=
  if min eφ et < -B - 13 then pt (addOp p n φ t)
  else pt (addOp p n (pt (addOp p n φ t)) fun i =>
    (2 : ℝ) ^ et * pt (smulOp p n eφ φ fun i => (2 : ℝ) ^ (-et) * t i) i)

omit [Prec_gt_0 p] in
/-- step (4)'s bounds: `(ε_{φt}, ν) = G_MUL(π^φ, ψ; φ̄(t̄ + E_m))` with `2^{-B-12}max(φ̄, t̄ + E_m)` added to
`ε_{φt}`, `(ε_{φ+t}, π^s) = G_ADD(π^φ, ψ; 2(e^{b̂} - 1 - b̂) + e^{b̂}(e^{E+δ} - 1) + E_m)` with `b̂ = b + δ`,
`c̄* = e^E - 1`, `E_δ = e^E(e^δ - 1)`, `(ε_c, χ') = G_ADD(π^s, ν; c̄* + ξE_m + E_δ + ε_{φt} + ε_{φ+t})`,
`E_c = ξE_m + E_δ + ε_{φt} + ε_{φ+t} + ε_c`, `χ'' = G_ADD(π^φ, ψ; c̄* + E_c)` and `χ = max(χ', χ'')` -/
noncomputable def logC4 (πφ ψ : ℕ → ℝ) (φb tb Em E δ b ξ : ℝ) (B : ℤ) : ℝ × (ℕ → ℝ) :=
  let Zp := φb * (tb + Em)
  let εφt := GmulE p n πφ ψ Zp + (2 : ℝ) ^ (-B - 12) * max φb (tb + Em)
  let Zs := 2 * (Real.exp (b + δ) - 1 - (b + δ)) + Real.exp (b + δ) * (Real.exp (E + δ) - 1) + Em
  let Zc := (Real.exp E - 1) + ξ * Em + Real.exp E * (Real.exp δ - 1) + εφt + GaddE p n πφ ψ Zs
  let Ec := ξ * Em + Real.exp E * (Real.exp δ - 1) + εφt + GaddE p n πφ ψ Zs +
    GaddE p n (GaddP p n πφ ψ Zs) (GmulP p n πφ ψ Zp) Zc
  (Ec, fun i => max (GaddP p n (GaddP p n πφ ψ Zs) (GmulP p n πφ ψ Zp) Zc i) (GaddP p n πφ ψ (Real.exp E - 1 + Ec) i))

omit [Prec_gt_0 p] in
/-- step (4) in exact arithmetic: with `1 + φ = 2^kx = e^{-e_0 - r_e}`, `|r - r_e| ≤ δ`, `|e_0| ≤ E`, `|r| ≤ b` and `t`
within `E_m` of `e^r - 1`: `|c*| ≤ e^E - 1` for `c* = e^{-e_0} - 1`, `|φ + t + φt - c*| ≤ ξE_m + e^E(e^δ - 1)`, and
`|φ + t| ≤ 2(e^{b̂} - 1 - b̂) + e^{b̂}(e^{E+δ} - 1) + E_m` -/
theorem log_c_exact {R re e0 E δ b ξ Φ T Em : ℝ} (hRre : |R - re| ≤ δ) (he0 : |e0| ≤ E) (hRb : |R| ≤ b)
    (hΦ : Φ = Real.exp (-e0 - re) - 1) (hξ : Real.exp (-e0 - re) ≤ ξ) (hT : |T - (Real.exp R - 1)| ≤ Em) :
    |Real.exp (-e0) - 1| ≤ Real.exp E - 1 ∧
      |Φ + T + Φ * T - (Real.exp (-e0) - 1)| ≤ ξ * Em + Real.exp E * (Real.exp δ - 1) ∧
      |Φ + T| ≤ 2 * (Real.exp (b + δ) - 1 - (b + δ)) + Real.exp (b + δ) * (Real.exp (E + δ) - 1) + Em := by
  have hE0 : 0 ≤ E := (abs_nonneg _).trans he0
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hRre
  have hb0 : 0 ≤ b := (abs_nonneg _).trans hRb
  have hX0 : 0 < Real.exp (-e0 - re) := Real.exp_pos _
  have he0' : Real.exp (-e0) ≤ Real.exp E := Real.exp_le_exp.mpr (by linarith [neg_abs_le e0])
  refine ⟨(abs_exp_sub_one_le _).trans (by rw [abs_neg]; linarith [Real.exp_le_exp.mpr he0]), ?_, ?_⟩
  · have e : Φ + T + Φ * T - (Real.exp (-e0) - 1) = Real.exp (-e0) * (Real.exp (R - re) - 1) +
        Real.exp (-e0 - re) * (T - (Real.exp R - 1)) := by
      rw [hΦ, show Real.exp (-e0 - re) = Real.exp (-e0) * Real.exp (-re) by rw [← Real.exp_add]; ring_nf,
        show Real.exp (R - re) = Real.exp R * Real.exp (-re) by rw [← Real.exp_add]; ring_nf]
      ring
    rw [e]
    have h1 : |Real.exp (R - re) - 1| ≤ Real.exp δ - 1 :=
      (abs_exp_sub_one_le _).trans (by linarith [Real.exp_le_exp.mpr hRre])
    calc _ ≤ |Real.exp (-e0) * (Real.exp (R - re) - 1)| + |Real.exp (-e0 - re) * (T - (Real.exp R - 1))| :=
          abs_add_le _ _
      _ ≤ Real.exp E * (Real.exp δ - 1) + ξ * Em := by
          rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hX0]
          exact add_le_add (mul_le_mul he0' h1 (abs_nonneg _) (Real.exp_pos _).le)
            (mul_le_mul hξ hT (abs_nonneg _) (hX0.le.trans hξ))
      _ = _ := by ring
  · have e : Φ + T = (Real.exp (-e0 - re) - Real.exp (-R)) + (Real.exp (-R) + Real.exp R - 2) +
        (T - (Real.exp R - 1)) := by rw [hΦ]; ring
    rw [e]
    have hRb' : |R| ≤ b + δ := by linarith
    have h1 : |Real.exp (-e0 - re) - Real.exp (-R)| ≤ Real.exp (b + δ) * (Real.exp (E + δ) - 1) := by
      rw [show Real.exp (-e0 - re) - Real.exp (-R) = Real.exp (-R) * (Real.exp (-e0 + (R - re)) - 1) by
        rw [mul_sub, ← Real.exp_add]; ring_nf, abs_mul, abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul (Real.exp_le_exp.mpr (by linarith [neg_abs_le R])) ((abs_exp_sub_one_le _).trans ?_)
        (abs_nonneg _) (Real.exp_pos _).le
      have : |-e0 + (R - re)| ≤ E + δ := (abs_add_le _ _).trans (by rw [abs_neg]; linarith)
      linarith [Real.exp_le_exp.mpr this]
    have h2 : |Real.exp (-R) + Real.exp R - 2| ≤ 2 * (Real.exp (b + δ) - 1 - (b + δ)) := by
      have hlo : 0 ≤ Real.exp (-R) + Real.exp R - 2 := by
        linarith [Real.add_one_le_exp R, Real.add_one_le_exp (-R)]
      rw [abs_of_nonneg hlo]
      exact (cosh_sub_two_le R).trans (by linarith [expm1_sub_mono (abs_nonneg R) hRb'])
    calc _ ≤ |Real.exp (-e0 - re) - Real.exp (-R)| + |Real.exp (-R) + Real.exp R - 2| + |T - (Real.exp R - 1)| := by
          refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by linarith

/-- step (4): `c` is within `E_c` of `c* = e^{-e_0} - 1`, with parts within `χ` -/
theorem log_step4 (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (φ t : ℕ → ℝ)
    (hφ : ∀ i < n, F p (φ i)) (ht : ∀ i < n, F p (t i)) (πφ ψ : ℕ → ℝ) (hπφ0 : ∀ i, 0 ≤ πφ i)
    (hψ0 : ∀ i, 0 ≤ ψ i) (hπφ : ∀ i < n, |φ i| ≤ πφ i) (hψ : ∀ i < n, |t i| ≤ ψ i)
    {R re e0 E δ b ξ φb tb Em : ℝ} (hRre : |R - re| ≤ δ) (he0 : |e0| ≤ E) (hRb : |R| ≤ b)
    (hΦ : ∑ i ∈ range n, φ i = Real.exp (-e0 - re) - 1) (hξ : Real.exp (-e0 - re) ≤ ξ)
    (hφb : |∑ i ∈ range n, φ i| ≤ φb) (hT : |∑ i ∈ range n, t i - (Real.exp R - 1)| ≤ Em)
    (htb : |Real.exp R - 1| ≤ tb) (B eφ et : ℤ) (γ : ℝ) (hγ : (1 + u p) ^ n ≤ 1 + γ)
    (hUφ : expU p n γ φ < (2 : ℝ) ^ (eφ + 1)) (hUt : expU p n γ t < (2 : ℝ) ^ (et + 1)) :
    |∑ i ∈ range n, logC p n B eφ et φ t i - (Real.exp (-e0) - 1)| ≤ (logC4 p n πφ ψ φb tb Em E δ b ξ B).1 ∧
      (∀ i < n, |logC p n B eφ et φ t i| ≤ (logC4 p n πφ ψ φb tb Em E δ b ξ B).2 i) ∧
      (∀ i < n, F p (logC p n B eφ et φ t i)) ∧ ∀ i, 0 ≤ (logC4 p n πφ ψ φb tb Em E δ b ξ B).2 i := by
  set Φ := ∑ i ∈ range n, φ i with hΦd
  set T := ∑ i ∈ range n, t i with hTd
  have hEm0 : 0 ≤ Em := (abs_nonneg _).trans hT
  have htb0 : 0 ≤ tb := (abs_nonneg _).trans htb
  have hφb0 : 0 ≤ φb := (abs_nonneg _).trans hφb
  have hTb : |T| ≤ tb + Em := by
    have := abs_sub_abs_le_abs_sub T (Real.exp R - 1)
    linarith
  obtain ⟨hcs, hrel, hZs⟩ := log_c_exact hRre he0 hRb hΦ hξ hT
  set cs := Real.exp (-e0) - 1 with hcsd
  set Zp := φb * (tb + Em) with hZp
  set Zs := 2 * (Real.exp (b + δ) - 1 - (b + δ)) + Real.exp (b + δ) * (Real.exp (E + δ) - 1) + Em with hZsd
  have hZp' : |Φ * T| ≤ Zp := by rw [abs_mul]; exact mul_le_mul hφb hTb (abs_nonneg _) hφb0
  have hZs0 : 0 ≤ Zs := (abs_nonneg _).trans hZs
  obtain ⟨hεφt0, hν0⟩ := Gmul_nonneg p n hA3 hπφ0 hψ0 (Zb := Zp) (mul_nonneg hφb0 (add_nonneg htb0 hEm0))
  obtain ⟨hεs0, hπs0⟩ := Gadd_nonneg p n hA3 hπφ0 hψ0 hZs0
  set εφt := GmulE p n πφ ψ Zp + (2 : ℝ) ^ (-B - 12) * max φb (tb + Em) with hεφt
  set εs := GaddE p n πφ ψ Zs with hεs
  set πs := GaddP p n πφ ψ Zs with hπs
  set ν := GmulP p n πφ ψ Zp with hν
  set Eδ := Real.exp E * (Real.exp δ - 1) with hEδ
  set cb := Real.exp E - 1 with hcb
  set Zc := cb + ξ * Em + Eδ + εφt + εs with hZc
  have hcb0 : 0 ≤ cb := (abs_nonneg _).trans hcs
  have hmax0 : 0 ≤ (2 : ℝ) ^ (-B - 12) * max φb (tb + Em) :=
    mul_nonneg (by positivity) (le_max_of_le_left hφb0)
  have hεφt0' : 0 ≤ εφt := add_nonneg hεφt0 hmax0
  have hξ0 : 0 ≤ ξ := (Real.exp_pos _).le.trans hξ
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hRre
  have hEδ0 : 0 ≤ Eδ := mul_nonneg (Real.exp_pos _).le (by linarith [Real.add_one_le_exp δ])
  have hZc0 : 0 ≤ Zc :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg hcb0 (mul_nonneg hξ0 hEm0)) hEδ0) hεφt0') hεs0
  obtain ⟨hεc0, hχ'0⟩ := Gadd_nonneg p n hA3 hπs0 hν0 hZc0
  set Ec := ξ * Em + Eδ + εφt + εs + GaddE p n πs ν Zc with hEc
  have hEc0 : 0 ≤ Ec :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg hξ0 hEm0) hEδ0) hεφt0') hεs0) hεc0
  obtain ⟨-, hχ''0⟩ := Gadd_nonneg p n hA3 hπφ0 hψ0 (Zb := cb + Ec) (add_nonneg hcb0 hEc0)
  have hL : (logC4 p n πφ ψ φb tb Em E δ b ξ B).1 = Ec := rfl
  have hL2 : (logC4 p n πφ ψ φb tb Em E δ b ξ B).2 = fun i => max (GaddP p n πs ν Zc i) (GaddP p n πφ ψ (cb + Ec) i) :=
    rfl
  rw [hL, hL2]
  refine ?_
  -- `s = ADD(φ, t)`
  obtain ⟨s1, s2, s3, s4⟩ := add_G p n hp hn hA3 φ t πφ ψ hφ ht hπφ hψ Zs hZs
  rw [← hΦd, ← hTd] at s1
  set S := addOp p n φ t with hSd
  have hSs : S.sum = ∑ i ∈ range n, pt S i := list_sum_getD S n s4
  unfold logC
  split_ifs with hd
  · -- `c = s`, with `|φt| ≤ 2^{-B-12}max(φ̄, t̄ + E_m)`
    have hsmall : |Φ * T| ≤ (2 : ℝ) ^ (-B - 12) * max φb (tb + Em) := by
      have hB : (2 : ℝ) ^ (-B - 13) ≤ (2 : ℝ) ^ (-B - 12) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      rcases min_lt_iff.mp hd with h | h
      · have h1 : |Φ| ≤ (2 : ℝ) ^ (-B - 13) := ((abs_sum_le_sum_abs _ _).trans
          ((expU_ge p n hn γ hγ φ).trans hUφ.le)).trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
        rw [abs_mul]
        calc |Φ| * |T| ≤ (2 : ℝ) ^ (-B - 12) * (tb + Em) :=
              mul_le_mul (h1.trans hB) hTb (abs_nonneg _) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      · have h1 : |T| ≤ (2 : ℝ) ^ (-B - 13) := ((abs_sum_le_sum_abs _ _).trans
          ((expU_ge p n hn γ hγ t).trans hUt.le)).trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
        rw [abs_mul, mul_comm]
        calc |T| * |Φ| ≤ (2 : ℝ) ^ (-B - 12) * φb :=
              mul_le_mul (h1.trans hB) hφb (abs_nonneg _) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    have hmain : |Φ + T - cs| ≤ Ec - εs - GaddE p n πs ν Zc := by
      have : |Φ + T - cs| ≤ |Φ + T + Φ * T - cs| + |Φ * T| := by
        have := abs_sub_le (Φ + T - cs) (Φ + T + Φ * T - cs) 0
        simp only [sub_zero] at this
        rw [show Φ + T - cs - (Φ + T + Φ * T - cs) = -(Φ * T) by ring, abs_neg] at this
        linarith
      rw [hEc]
      linarith
    -- `|φ + t| ≤ C`, so `χ''` bounds the parts
    have hC : |Φ + T| ≤ cb + Ec := by
      have := abs_sub_abs_le_abs_sub (Φ + T) cs
      linarith
    obtain ⟨-, c2, -, -⟩ := add_G p n hp hn hA3 φ t πφ ψ hφ ht hπφ hψ (cb + Ec) hC
    refine ⟨?_, fun i _ => (c2 i).trans (le_max_right _ _), fun i _ => s3 i, fun i => le_max_of_le_left (hχ'0 i)⟩
    rw [← hSs]
    calc |S.sum - cs| ≤ |Φ + T - S.sum| + |Φ + T - cs| := by
          have := abs_sub_le S.sum (Φ + T) cs; rw [abs_sub_comm S.sum (Φ + T)] at this; exact this
      _ ≤ εs + (Ec - εs - GaddE p n πs ν Zc) := add_le_add s1 hmain
      _ ≤ Ec := by linarith
  · -- `c = ADD(s, p)`
    obtain ⟨q1, q2, q3⟩ := pOp_bound p n hp hn hA3 eφ et φ t hφ ht πφ ψ hπφ hψ Zp hZp'
    rw [← hΦd, ← hTd] at q1
    set P := fun i => (2 : ℝ) ^ et * pt (smulOp p n eφ φ fun i => (2 : ℝ) ^ (-et) * t i) i with hPd
    set Ps := ∑ i ∈ range n, P i with hPs
    have hZc' : |∑ i ∈ range n, pt S i + Ps| ≤ Zc := by
      rw [← hSs]
      have e : S.sum + Ps = cs + ((S.sum - (Φ + T)) + (Ps - Φ * T) + (Φ + T + Φ * T - cs)) := by ring
      rw [e]
      have h1 : |S.sum - (Φ + T)| ≤ εs := by rw [abs_sub_comm]; exact s1
      have h2 : |Ps - Φ * T| ≤ εφt := by rw [abs_sub_comm]; linarith
      calc _ ≤ |cs| + (|S.sum - (Φ + T)| + |Ps - Φ * T| + |Φ + T + Φ * T - cs|) := by
            refine (abs_add_le _ _).trans (add_le_add le_rfl ((abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) le_rfl)))
        _ ≤ _ := by rw [hZc]; linarith
    obtain ⟨c1, c2, c3, c4⟩ := add_G p n hp hn hA3 (pt S) P πs ν (fun i _ => s3 i) (fun i _ => q3 i)
      (fun i _ => s2 i) (fun i _ => q2 i) Zc hZc'
    set Cl := addOp p n (pt S) P with hCl
    have hCs : Cl.sum = ∑ i ∈ range n, pt Cl i := list_sum_getD Cl n c4
    refine ⟨?_, fun i _ => (c2 i).trans (le_max_left _ _), fun i _ => c3 i, fun i => le_max_of_le_left (hχ'0 i)⟩
    rw [← hCs]
    have e : Cl.sum - cs = -((∑ i ∈ range n, pt S i + Ps) - Cl.sum) + (S.sum - (Φ + T)) + (Ps - Φ * T) +
        (Φ + T + Φ * T - cs) := by rw [hSs]; ring
    rw [e]
    have h1 : |S.sum - (Φ + T)| ≤ εs := by rw [abs_sub_comm]; exact s1
    have h2 : |Ps - Φ * T| ≤ εφt := by rw [abs_sub_comm]; linarith
    calc _ ≤ |(∑ i ∈ range n, pt S i + Ps) - Cl.sum| + |S.sum - (Φ + T)| + |Ps - Φ * T| +
          |Φ + T + Φ * T - cs| := by
          have t1 := abs_add_le (-((∑ i ∈ range n, pt S i + Ps) - Cl.sum) + (S.sum - (Φ + T)) + (Ps - Φ * T))
            (Φ + T + Φ * T - cs)
          have t2 := abs_add_le (-((∑ i ∈ range n, pt S i + Ps) - Cl.sum) + (S.sum - (Φ + T))) (Ps - Φ * T)
          have t3 := abs_add_le (-((∑ i ∈ range n, pt S i + Ps) - Cl.sum)) (S.sum - (Φ + T))
          rw [abs_neg] at t3
          linarith
      _ ≤ _ := by rw [hEc]; linarith

/-! ## The theorem -/

omit [Prec_gt_0 p] in
/-- step (3): `x' = 2^kx`, exact as the exponent range is unbounded, and `φ = ADDF(x', -1)` -/
noncomputable def logPhi (k : ℤ) (x : ℕ → ℝ) : ℕ → ℝ := pt (addfOp p n (fun i => (2 : ℝ) ^ k * x i) (-1))

omit [Prec_gt_0 p] in
/-- LOG after its start `y_0`, with `t` from EXP's core on `-y_0`: `ADD(y_0, y_c)` -/
noncomputable def logOp (y0 x : ℕ → ℝ) (k : ℤ) (t : ℕ → ℝ) (B eφ et ec : ℤ) (F' : ℕ → ℕ → ℝ) (q : ℕ) : List ℝ :=
  addOp p n y0 (logYc p n B ec (logC p n B eφ et (logPhi p n k x) t) F' q)

omit [Prec_gt_0 p] in
/-- `ξ = e^{E+δ-a}` for `r ≥ 0` and `e^{E+b+δ}` for `r ≤ 0` -/
noncomputable def logXi (pos : Bool) (E a b δ : ℝ) : ℝ := if pos then Real.exp (E + δ - a) else Real.exp (E + b + δ)

omit [Prec_gt_0 p] in
/-- `φ̄ = max(ξ - 1, 1 - e^{-(E+b+δ)})` -/
noncomputable def logPhiB (pos : Bool) (E a b δ : ℝ) : ℝ := max (logXi pos E a b δ - 1) (1 - Real.exp (-(E + b + δ)))

omit [Prec_gt_0 p] in
/-- step (4)'s bounds for a case, from `π^φ = G_ADDF(π^x, 1; φ̄, φ̄ + ∑_{i≥1}π^x_i)` and Lemma 39's `(E_m, ψ_m)`, with
`ψ_m` taken nonnegative -/
noncomputable def logCase4 (E : ℝ) (pos : Bool) (e : ℤ) (m : ℕ) (a b δ : ℝ) (π : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ)
    (φF : ℕ → ℝ) (d' : ℕ) (πx : ℕ → ℝ) (B : ℤ) : ℝ × (ℕ → ℝ) :=
  logC4 p n (GaddfP' p n πx (logPhiB pos E a b δ + ∑ i ∈ Ico 1 n, πx i) (logPhiB pos E a b δ))
    (fun i => max ((coreBound p n pos e m a b π Fk φF d').2 i) 0) (logPhiB pos E a b δ)
    (coreT pos (coreBp e m b) m) (coreBound p n pos e m a b π Fk φF d').1 E δ b (logXi pos E a b δ) B

omit [Prec_gt_0 p] in
/-- `𝓔(ℓ) = ε_y + P` with `(ε_y, ·) = G_ADD(π^y, ω_r; ℓ + P)`, `C = e^E - 1 + E_c` -/
noncomputable def logBound (ℓ E : ℝ) (πy : ℕ → ℝ) (pos : Bool) (e : ℤ) (m : ℕ) (a b δ : ℝ) (π : ℕ → ℝ)
    (Fk : ℕ → ℕ → ℝ) (φF : ℕ → ℝ) (d' : ℕ) (πx : ℕ → ℝ) (F' : ℕ → ℕ → ℝ) (φ' : ℕ → ℝ) (q : ℕ) (B : ℤ) : ℝ :=
  let c4 := logCase4 p n E pos e m a b δ π Fk φF d' πx B
  let P := logP p n c4.2 (Real.exp E - 1 + c4.1) c4.1 F' φ' q B
  GaddE p n πy P.2 (ℓ + P.1) + P.1

/-- Theorem 42 (`thm:log`) with an unbounded exponent range, so `η_0 = 0`, for a case, with `x > 0` and `(n² + n)u < 1`:
with the start `y_0` within `E` of `ln x` and `ℓ ≥ |ln x|`; EXP's reduction of `-y_0` to `r` within `δ` of
`r_e = -y_0 - k ln 2`, with `a ≤ |r| ≤ b` and the case's sign; its core run with `U < 2^{e+1}`, `m` squarings and degree
`d'`; `x' = 2^kx` with parts within `π^x` and `x'_0 ∈ [1/2, 2]`; the exponents `e_φ`, `e_t` and `e_c` of steps (4) and
(5) with `U_v < 2^{e_v+1}`; and `C = e^E - 1 + E_c < 1`: LOG's result `y` satisfies `|y - ln x| ≤ 𝓔(ℓ)` -/
theorem thm42_case (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (x : ℕ → ℝ)
    (hx : ∀ i < n, F p (x i)) (hX0 : 0 < ∑ i ∈ range n, x i) (y0 : ℕ → ℝ) (hy0 : ∀ i < n, F p (y0 i))
    (πy : ℕ → ℝ) (hπy : ∀ i < n, |y0 i| ≤ πy i) (ℓ E : ℝ) (hℓ : |Real.log (∑ i ∈ range n, x i)| ≤ ℓ)
    (hE : |∑ i ∈ range n, y0 i - Real.log (∑ i ∈ range n, x i)| ≤ E)
    (r : ℕ → ℝ) (hr : ∀ i < n, F p (r i)) (k : ℤ) (δ : ℝ)
    (hδ : |∑ i ∈ range n, r i - (-∑ i ∈ range n, y0 i - k * Real.log 2)| ≤ δ) (a b : ℝ)
    (ha : a ≤ |∑ i ∈ range n, r i|) (hb : |∑ i ∈ range n, r i| ≤ b) (π : ℕ → ℝ) (hπ : ∀ i < n, |r i| ≤ π i)
    (pos : Bool) (hsgn : if pos then 0 ≤ ∑ i ∈ range n, r i else ∑ i ∈ range n, r i ≤ 0)
    (γ : ℝ) (hγ : (1 + u p) ^ n ≤ 1 + γ) (e : ℤ) (hU : expU p n γ r < (2 : ℝ) ^ (e + 1)) (m d' : ℕ)
    (hd : 1 ≤ d') (hbd : coreBp e m b < d' + 2) (Fk : ℕ → ℕ → ℝ) (hF : ∀ k, ∀ i < n, F p (Fk k i))
    (φF : ℕ → ℝ) (hφF : ∀ k, |∑ i ∈ range n, Fk k i - invF k| ≤ φF k)
    (πx : ℕ → ℝ) (hπx0 : ∀ i, 0 ≤ πx i) (hπx : ∀ i < n, |(2 : ℝ) ^ k * x i| ≤ πx i)
    (hx0 : 1 / 2 ≤ (2 : ℝ) ^ k * x 0 ∧ (2 : ℝ) ^ k * x 0 ≤ 2) (B eφ et ec : ℤ)
    (hUφ : expU p n γ (logPhi p n k x) < (2 : ℝ) ^ (eφ + 1))
    (hUt : expU p n γ (expCore p n e m r Fk d') < (2 : ℝ) ^ (et + 1))
    (hUc : expU p n γ (logC p n B eφ et (logPhi p n k x) (expCore p n e m r Fk d')) < (2 : ℝ) ^ (ec + 1))
    (F' : ℕ → ℕ → ℝ) (hF' : ∀ k, ∀ i < n, F p (F' k i)) (φ' : ℕ → ℝ)
    (hφ' : ∀ k, |∑ i ∈ range n, F' k i - logFe k| ≤ φ' k) (q : ℕ) (hq : 2 ≤ q)
    (hC : Real.exp E - 1 + (logCase4 p n E pos e m a b δ π Fk φF d' πx B).1 < 1) :
    |(logOp p n y0 x k (expCore p n e m r Fk d') B eφ et ec F' q).sum - Real.log (∑ i ∈ range n, x i)| ≤
      logBound p n ℓ E πy pos e m a b δ π Fk φF d' πx F' φ' q B := by
  set X := ∑ i ∈ range n, x i with hXd
  set Y0 := ∑ i ∈ range n, y0 i with hY0d
  set R := ∑ i ∈ range n, r i with hRd
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hδ
  -- Lemma 39
  obtain ⟨c1, c2, c3⟩ := lemma_core p n hp hn hA3 r hr R hRd a b ha hb π hπ γ hγ e hU m d' hd hbd Fk hF φF hφF pos
    hsgn
  set t := expCore p n e m r Fk d' with htd
  set Em := (coreBound p n pos e m a b π Fk φF d').1 with hEm
  set ψ := fun i => max ((coreBound p n pos e m a b π Fk φF d').2 i) 0 with hψd
  have hψ0 : ∀ i, 0 ≤ ψ i := fun i => le_max_right _ _
  have hψ : ∀ i < n, |t i| ≤ ψ i := fun i hi => (c2 i hi).trans (le_max_left _ _)
  set tb := coreT pos (coreBp e m b) m with htb
  -- `2^kx = e^{-e_0 - r_e}` with `e_0 = y_0 - ln x` and `r_e = -y_0 - k ln 2`
  set e0 := Y0 - Real.log X with he0d
  set re := -Y0 - k * Real.log 2 with hred
  have hX' : (2 : ℝ) ^ k * X = Real.exp (-e0 - re) := by
    rw [he0d, hred, show -(Y0 - Real.log X) - (-Y0 - k * Real.log 2) = Real.log X + k * Real.log 2 by ring,
      Real.exp_add, Real.exp_log hX0, exp_int_mul_log_two, mul_comm]
  set ξ := logXi pos E a b δ with hξd
  set φb := logPhiB pos E a b δ with hφbd
  have hreR : |re| ≤ b + δ := by
    have := abs_sub_abs_le_abs_sub re R
    rw [abs_sub_comm re R] at this
    linarith
  have hξ : Real.exp (-e0 - re) ≤ ξ := by
    rw [hξd, logXi]
    have h1 := (abs_le.mp hδ)
    have h2 := (abs_le.mp hE)
    cases pos with
    | true =>
      simp only [ite_true] at hsgn ⊢
      rw [abs_of_nonneg hsgn] at ha
      exact Real.exp_le_exp.mpr (by linarith)
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hsgn ⊢
      rw [abs_of_nonpos hsgn] at hb
      exact Real.exp_le_exp.mpr (by linarith)
  have hlo : Real.exp (-(E + b + δ)) ≤ Real.exp (-e0 - re) :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp hE).2, (abs_le.mp hreR).2])
  -- step (3): `φ = x' - 1` exactly
  set x' := fun i => (2 : ℝ) ^ k * x i with hx'd
  have hx'F : ∀ i < n, F p (x' i) := fun i hi => F_zpow_mul p _ (hx i hi)
  have hfx := lemma_fexact p n hp hn x' hx'F hx0.1 hx0.2
  have hsx' : ∑ i ∈ range n, x' i = (2 : ℝ) ^ k * X := by rw [hx'd, ← mul_sum]
  have hφbx : |∑ i ∈ range n, x' i + -1| ≤ φb := by
    rw [hsx', hX', ← sub_eq_add_neg, hφbd, logPhiB, ← hξd, abs_le]
    constructor
    · linarith [le_max_right (ξ - 1) (1 - Real.exp (-(E + b + δ)))]
    · linarith [le_max_left (ξ - 1) (1 - Real.exp (-(E + b + δ)))]
  have hlam : |x' 0 + -1| ≤ φb + ∑ i ∈ Ico 1 n, πx i := by
    have h0 : x' 0 + -1 = (∑ i ∈ range n, x' i + -1) - ∑ i ∈ Ico 1 n, x' i := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]; ring
    rw [h0]
    refine (abs_sub _ _).trans (add_le_add hφbx ((abs_sum_le_sum_abs _ _).trans
      (sum_le_sum fun i hi => hπx i (mem_Ico.mp hi).2)))
  obtain ⟨-, f2, f3, f4⟩ := addf_G' p n hp hn x' (-1) πx hx'F (F_neg p (F_one p)) hπx _ hlam φb hφbx
  set φ := logPhi p n k x with hφd
  have hφs : ∑ i ∈ range n, φ i = Real.exp (-e0 - re) - 1 := by
    show ∑ i ∈ range n, (addfOp p n x' (-1)).getD i 0 = _
    rw [← list_sum_getD _ n f4, hfx, hsx', hX']
  have hφb : |∑ i ∈ range n, φ i| ≤ φb := by
    rw [hφs, ← hX', ← hsx', sub_eq_add_neg]; exact hφbx
  have hφb0 : 0 ≤ φb := (abs_nonneg _).trans hφb
  set πφ := GaddfP' p n πx (φb + ∑ i ∈ Ico 1 n, πx i) φb with hπφd
  have hπφ0 : ∀ i, 0 ≤ πφ i := gParts_nonneg p n (addfX_nonneg p n hπx0 (by
    have := sum_nonneg fun i (_ : i ∈ Ico 1 n) => hπx0 i; linarith)) hφb0 le_rfl
  -- step (4)
  obtain ⟨d1, d2, d3, d4⟩ := log_step4 p n hp hn hA3 φ t (fun i _ => f3 i) (expCore_F p n hp hn hA3 e m r hr Fk hF d')
    πφ ψ hπφ0 hψ0 (fun i _ => f2 i) hψ hδ (show |e0| ≤ E from hE) hb hφs hξ hφb c1 c3 B eφ et γ hγ hUφ hUt
  set c := logC p n B eφ et φ t with hcd
  set c4 := logC4 p n πφ ψ φb tb Em E δ b ξ B with hc4
  have hc4' : logCase4 p n E pos e m a b δ π Fk φF d' πx B = c4 := rfl
  rw [hc4'] at hC
  -- step (5)
  have hcs : |Real.exp (-e0) - 1| ≤ Real.exp E - 1 :=
    (abs_exp_sub_one_le _).trans (by rw [abs_neg]; linarith [Real.exp_le_exp.mpr hE])
  obtain ⟨g1, g2, g3⟩ := log_step5 p n hp hn hA3 c d3 c4.2 d4 d2 (Real.exp (-e0) - 1) (Real.exp E - 1) c4.1 hcs d1
    hC F' hF' φ' hφ' q hq B ec γ hγ hUc
  rw [show 1 + (Real.exp (-e0) - 1) = Real.exp (-e0) by ring, Real.log_exp] at g1
  set yc := logYc p n B ec c F' q with hycd
  set P := logP p n c4.2 (Real.exp E - 1 + c4.1) c4.1 F' φ' q B with hPd
  -- the last ADD
  have hZ : |Y0 + ∑ i ∈ range n, yc i| ≤ ℓ + P.1 := by
    have e1 : Y0 + ∑ i ∈ range n, yc i = Real.log X + (∑ i ∈ range n, yc i - -e0) := by rw [he0d]; ring
    rw [e1]
    exact (abs_add_le _ _).trans (add_le_add hℓ g1)
  obtain ⟨a1, -, -, a4⟩ := add_G p n hp hn hA3 y0 yc πy P.2 hy0 g3 hπy g2 (ℓ + P.1) hZ
  have hres : logOp p n y0 x k t B eφ et ec F' q = addOp p n y0 yc := rfl
  have hB : logBound p n ℓ E πy pos e m a b δ π Fk φF d' πx F' φ' q B = GaddE p n πy P.2 (ℓ + P.1) + P.1 := rfl
  rw [hres, hB]
  calc |(addOp p n y0 yc).sum - Real.log X| ≤ |(Y0 + ∑ i ∈ range n, yc i) - (addOp p n y0 yc).sum| +
        |Y0 + ∑ i ∈ range n, yc i - Real.log X| := by
        have := abs_sub_le (addOp p n y0 yc).sum (Y0 + ∑ i ∈ range n, yc i) (Real.log X)
        rw [abs_sub_comm (addOp p n y0 yc).sum (Y0 + ∑ i ∈ range n, yc i)] at this
        exact this
    _ ≤ GaddE p n πy P.2 (ℓ + P.1) + P.1 := by
        refine add_le_add a1 ?_
        rw [show Y0 + ∑ i ∈ range n, yc i - Real.log X = ∑ i ∈ range n, yc i - -e0 by rw [he0d]; ring]
        exact g1

end ExpansionBounds
