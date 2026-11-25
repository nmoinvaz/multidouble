import ExpansionBounds.ExpRed8
import ExpansionBounds.TrigEval

/-!
# Theorem 40's bound of a case in rational arithmetic, rounded up

The bound `ε` of a case is evaluated on rational mirrors whose values are rounded up, as Theorem 35's are
(`TrigEval.lean`): every bound grows with the quantities so rounded, so the mirrors are at least the paper's bounds.
Horner's run is `hornerRunL`'s, with `v_k` replaced by `1/(k!(1 - b'/(k + 1)))`; step (3)'s two products and sum, each
squaring, and the last ADDF with the division by `v` are steps on a state, a bound and a list of part bounds, so that
the kernel can check each against stored data.
-/

namespace ExpansionBounds

open Finset

section Generic

variable (p : ℤ) [Prec_gt_0 p] (n : ℕ)

omit [Prec_gt_0 p] in
/-- Horner's bounds `(e_k, π^{(k)})` of Lemma 33 grow with `π^z`, `z̄`, `ε_z` and `v` -/
theorem hornerB_mono2 (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {πz πz' : ℕ → ℝ} (hπ0 : ∀ i, 0 ≤ πz i)
    (hπ : ∀ i, πz i ≤ πz' i) {zb zb' εz εz' η : ℝ} (hzb : 0 ≤ zb) (hzz : zb ≤ zb') (hε0 : 0 ≤ εz)
    (hε : εz ≤ εz') (hη : 0 ≤ η) (Fk : ℕ → ℕ → ℝ) {φ v v' : ℕ → ℝ} (hφ : ∀ k, 0 ≤ φ k) (hv : ∀ k, 0 ≤ v k)
    (hvv : ∀ k, v k ≤ v' k) (d : ℕ) : ∀ j,
    (hornerB p n πz zb εz η Fk φ v d j).1 ≤ (hornerB p n πz' zb' εz' η Fk φ v' d j).1 ∧
      ∀ i, (hornerB p n πz zb εz η Fk φ v d j).2 i ≤ (hornerB p n πz' zb' εz' η Fk φ v' d j).2 i
  | 0 => ⟨le_rfl, fun _ => le_rfl⟩
  | j + 1 => by
    obtain ⟨i1, i2⟩ := hornerB_mono2 hA3 hπ0 hπ hzb hzz hε0 hε hη Fk hφ hv hvv d j
    obtain ⟨n1, n2⟩ := hornerB_nonneg p n hA3 hπ0 hzb hε0 hη Fk hφ hv d j
    have hε0' : 0 ≤ εz' := hε0.trans hε
    have hvk := hv (d - (j + 1) + 1)
    have hvk' := hvv (d - (j + 1) + 1)
    have hc : (1 + εz) * zb ≤ (1 + εz') * zb' := mul_le_mul (by linarith) hzz hzb (by linarith)
    have hc0 : 0 ≤ (1 + εz) * zb := mul_nonneg (by linarith) hzb
    have hZm : (1 + εz) * zb * (v (d - (j + 1) + 1) + (hornerB p n πz zb εz η Fk φ v d j).1) ≤
        (1 + εz') * zb' * (v' (d - (j + 1) + 1) + (hornerB p n πz' zb' εz' η Fk φ v' d j).1) :=
      mul_le_mul hc (by linarith) (add_nonneg hvk n1) (hc0.trans hc)
    obtain ⟨m1, m2⟩ := Gmul_mono p n hA3 hπ0 n2 hπ i2 hZm
    have hD : (1 + εz) * zb * (hornerB p n πz zb εz η Fk φ v d j).1 + εz * zb * v (d - (j + 1) + 1) +
          φ (d - (j + 1)) + (GmulE p n πz (hornerB p n πz zb εz η Fk φ v d j).2
            ((1 + εz) * zb * (v (d - (j + 1) + 1) + (hornerB p n πz zb εz η Fk φ v d j).1)) + n * η) ≤
        (1 + εz') * zb' * (hornerB p n πz' zb' εz' η Fk φ v' d j).1 + εz' * zb' * v' (d - (j + 1) + 1) +
          φ (d - (j + 1)) + (GmulE p n πz' (hornerB p n πz' zb' εz' η Fk φ v' d j).2
            ((1 + εz') * zb' * (v' (d - (j + 1) + 1) + (hornerB p n πz' zb' εz' η Fk φ v' d j).1)) + n * η) := by
      have a1 : (1 + εz) * zb * (hornerB p n πz zb εz η Fk φ v d j).1 ≤
          (1 + εz') * zb' * (hornerB p n πz' zb' εz' η Fk φ v' d j).1 := mul_le_mul hc i1 n1 (hc0.trans hc)
      have a2 : εz * zb * v (d - (j + 1) + 1) ≤ εz' * zb' * v' (d - (j + 1) + 1) :=
        mul_le_mul (mul_le_mul hε hzz hzb hε0') hvk' hvk (mul_nonneg hε0' (hzb.trans hzz))
      linarith
    obtain ⟨g1, g2⟩ := Gadd_mono p n hA3 (fun i => le_refl |Fk (d - (j + 1)) i|)
      (fun i => add_le_add (m2 i) (le_refl η)) (add_le_add (hvv (d - (j + 1))) hD)
    exact ⟨add_le_add hD g1, g2⟩

omit [Prec_gt_0 p] in
/-- `v_k = ∑_{l ≤ d - k} b'^l/(k + l)! ≤ 1/(k!(1 - b/(k + 1)))` for `0 ≤ b' ≤ b < k + 1` -/
theorem coreV_le {b' b : ℝ} (hb0 : 0 ≤ b') (hbb : b' ≤ b) (d k : ℕ) (hbk : b < k + 1) :
    0 ≤ coreV b' d k ∧ coreV b' d k ≤ invF k / (1 - b / (k + 1)) := by
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hq0 : 0 ≤ b' / (k + 1) := div_nonneg hb0 hk1.le
  have hq1 : b' / (k + 1) < 1 := by rw [div_lt_one hk1]; linarith
  have hi0 : 0 ≤ invF k := by unfold invF; positivity
  unfold coreV hornerE
  refine ⟨sum_nonneg fun l _ => mul_nonneg (by unfold invF; positivity) (pow_nonneg hb0 l), ?_⟩
  have hterm : ∀ l, invF (k + l) * b' ^ l ≤ invF k * (b' / (k + 1)) ^ l := by
    intro l
    have hfk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hfkl : (0 : ℝ) < ((k + l).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hfac : (k.factorial : ℝ) * (k + 1) ^ l ≤ (k + l).factorial := by
      exact_mod_cast Nat.factorial_mul_pow_le_factorial
    unfold invF
    rw [div_pow, one_div_mul_eq_div, one_div_mul_eq_div, div_div]
    exact div_le_div_of_nonneg_left (pow_nonneg hb0 l) (by positivity) (by rw [mul_comm]; exact hfac)
  calc ∑ l ∈ range (d + 1 - k), invF (k + l) * b' ^ l ≤ ∑ l ∈ range (d + 1 - k), invF k * (b' / (k + 1)) ^ l :=
        sum_le_sum fun l _ => hterm l
    _ = invF k * ∑ l ∈ range (d + 1 - k), (b' / (k + 1)) ^ l := by rw [mul_sum]
    _ ≤ invF k * (1 / (1 - b' / (k + 1))) := mul_le_mul_of_nonneg_left (geom_le _ hq0 hq1 _) hi0
    _ = invF k / (1 - b' / (k + 1)) := by rw [mul_one_div]
    _ ≤ invF k / (1 - b / (k + 1)) := by
        refine div_le_div_of_nonneg_left hi0 ?_ ?_
        · rw [sub_pos, div_lt_one hk1]; exact hbk
        · have := div_le_div_of_nonneg_right hbb hk1.le
          linarith

end Generic

/-! ## The bounds use the part bounds below `n` only -/

section Trunc

variable (p : ℤ) (n : ℕ)

/-- a bound's parts below `n` -/
def trunc (f : ℕ → ℝ) : ℕ → ℝ := fun i => if i < n then f i else 0

theorem trunc_lt (f : ℕ → ℝ) {i : ℕ} (h : i < n) : trunc n f i = f i := by simp [trunc, h]

theorem trunc_nonneg {f : ℕ → ℝ} (h : ∀ i < n, 0 ≤ f i) (i : ℕ) : 0 ≤ trunc n f i := by
  unfold trunc
  split_ifs with hi
  · exact h i hi
  · exact le_rfl

theorem trunc_le {f g : ℕ → ℝ} (h : ∀ i < n, f i ≤ g i) (i : ℕ) : trunc n f i ≤ trunc n g i := by
  unfold trunc
  split_ifs with hi
  · exact h i hi
  · exact le_rfl

theorem mulP_trunc (α β : ℕ → ℝ) (m : ℕ) : mulP n (trunc n α) (trunc n β) m = mulP n α β m := by
  unfold mulP
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  rw [trunc_lt n α (mem_range.mp hi), trunc_lt n β (mem_range.mp hj)]

theorem mulA_trunc (α β : ℕ → ℝ) : mulA p n (trunc n α) (trunc n β) = mulA p n α β := by
  funext m
  simp only [mulA, mulP_trunc]

theorem mulX_trunc (α β : ℕ → ℝ) : mulX p n (trunc n α) (trunc n β) = mulX p n α β := by
  funext m
  simp only [mulX, mulA_trunc]

theorem Gmul_trunc (α β : ℕ → ℝ) (Zb : ℝ) : GmulE p n (trunc n α) (trunc n β) Zb = GmulE p n α β Zb ∧
    GmulP p n (trunc n α) (trunc n β) Zb = GmulP p n α β Zb := by
  have hD : mulDelta n (trunc n α) (trunc n β) = mulDelta n α β := by
    unfold mulDelta
    refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
    rw [trunc_lt n α (mem_range.mp hi), trunc_lt n β (mem_range.mp hj)]
  simp only [GmulE, GmulP, mulR, mulX_trunc p n α β, hD, and_self]

theorem pairA_trunc (hn : 1 ≤ n) (α β : ℕ → ℝ) :
    pairA p n (fun m => trunc n α m + trunc n β m) = pairA p n (fun m => α m + β m) := by
  funext m
  unfold pairA
  by_cases h : m < n
  · have h1 : m - 1 < n := by omega
    simp only [h, ↓reduceIte, trunc_lt n α h, trunc_lt n β h, trunc_lt n α h1, trunc_lt n β h1]
  · have h1 : n - 1 < n := by omega
    simp only [h, ↓reduceIte, trunc_lt n α h1, trunc_lt n β h1]

theorem Gadd_trunc (hn : 1 ≤ n) (α β : ℕ → ℝ) (Zb : ℝ) : GaddE p n (trunc n α) (trunc n β) Zb = GaddE p n α β Zb ∧
    GaddP p n (trunc n α) (trunc n β) Zb = GaddP p n α β Zb := by
  have hX : pairX p n (fun m => trunc n α m + trunc n β m) = pairX p n (fun m => α m + β m) := by
    funext m
    simp only [pairX, pairA_trunc p n hn α β]
  simp only [GaddE, GaddP, pairR, hX, and_self]

theorem addfEps_trunc (α : ℕ → ℝ) (lam0 : ℝ) : ∀ m, m < n → addfEps p (trunc n α) lam0 m = addfEps p α lam0 m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [addfEps]
    rw [trunc_lt n α h, addfEps_trunc α lam0 m (by omega)]

theorem addfX_trunc (hn : 1 ≤ n) (α : ℕ → ℝ) (lam0 : ℝ) : addfX p n (trunc n α) lam0 = addfX p n α lam0 := by
  funext m
  unfold addfX
  by_cases h0 : m = 0
  · simp [h0]
  · by_cases h : m < n
    · simp only [h0, h, ↓reduceIte, trunc_lt n α h, addfEps_trunc p n α lam0 (m - 1) (by omega)]
    · simp only [h0, h, ↓reduceIte, addfEps_trunc p n α lam0 (n - 1) (by omega)]

/-- `G_MUL` grows with part bounds compared below `n` -/
theorem Gmul_mono_lt (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α α' β β' : ℕ → ℝ} (hα0 : ∀ i < n, 0 ≤ α i)
    (hβ0 : ∀ j < n, 0 ≤ β j) (hα : ∀ i < n, α i ≤ α' i) (hβ : ∀ j < n, β j ≤ β' j) {Zb Zb' : ℝ} (hZ : Zb ≤ Zb') :
    GmulE p n α β Zb ≤ GmulE p n α' β' Zb' ∧ ∀ i, GmulP p n α β Zb i ≤ GmulP p n α' β' Zb' i := by
  have h := Gmul_mono p n hA3 (trunc_nonneg n hα0) (trunc_nonneg n hβ0) (trunc_le n hα) (trunc_le n hβ) hZ
  rw [(Gmul_trunc p n α β Zb).1, (Gmul_trunc p n α β Zb).2, (Gmul_trunc p n α' β' Zb').1,
    (Gmul_trunc p n α' β' Zb').2] at h
  exact h

/-- `G_ADD` grows with part bounds compared below `n` -/
theorem Gadd_mono_lt (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α α' β β' : ℕ → ℝ}
    (hα : ∀ i < n, α i ≤ α' i) (hβ : ∀ j < n, β j ≤ β' j) {Zb Zb' : ℝ} (hZ : Zb ≤ Zb') :
    GaddE p n α β Zb ≤ GaddE p n α' β' Zb' ∧ ∀ i, GaddP p n α β Zb i ≤ GaddP p n α' β' Zb' i := by
  have h := Gadd_mono p n hA3 (trunc_le n hα) (trunc_le n hβ) hZ
  rw [(Gadd_trunc p n hn α β Zb).1, (Gadd_trunc p n hn α β Zb).2, (Gadd_trunc p n hn α' β' Zb').1,
    (Gadd_trunc p n hn α' β' Zb').2] at h
  exact h

/-- `G_ADDF`'s error bound grows with part bounds compared below `n`, with `λ_0` and `Z̄` -/
theorem Gaddf_mono_lt (hn : 1 ≤ n) {α α' : ℕ → ℝ} (hα : ∀ i < n, α i ≤ α' i) {lam0 lam0' Zb Zb' : ℝ}
    (hl : lam0 ≤ lam0') (hZ : Zb ≤ Zb') : GaddfE' p n α lam0 Zb ≤ GaddfE' p n α' lam0' Zb' := by
  have h := gErr_mono p n (addfX_mono p n (trunc_le n hα) hl) hZ 0
  rw [addfX_trunc p n hn α lam0, addfX_trunc p n hn α' lam0'] at h
  exact h

theorem trunc_trunc (f : ℕ → ℝ) : trunc n (trunc n f) = trunc n f := by
  funext i
  unfold trunc
  split_ifs <;> rfl

theorem GmulE_trunc_left (α β : ℕ → ℝ) (Zb : ℝ) : GmulE p n (trunc n α) β Zb = GmulE p n α β Zb := by
  rw [← (Gmul_trunc p n (trunc n α) β Zb).1, trunc_trunc, (Gmul_trunc p n α β Zb).1]

theorem GmulP_trunc_left (α β : ℕ → ℝ) (Zb : ℝ) : GmulP p n (trunc n α) β Zb = GmulP p n α β Zb := by
  rw [← (Gmul_trunc p n (trunc n α) β Zb).2, trunc_trunc, (Gmul_trunc p n α β Zb).2]

/-- Horner's bounds use `π^z` below `n` only -/
theorem hornerB_trunc (πz : ℕ → ℝ) (zb εz η : ℝ) (Fk : ℕ → ℕ → ℝ) (φ v : ℕ → ℝ) (d : ℕ) :
    ∀ j, hornerB p n (trunc n πz) zb εz η Fk φ v d j = hornerB p n πz zb εz η Fk φ v d j
  | 0 => rfl
  | j + 1 => by
    simp only [hornerB, hornerB_trunc πz zb εz η Fk φ v d j, GmulE_trunc_left, GmulP_trunc_left]

end Trunc

/-! ## Rational enclosures of `e^z` -/

/-- `∑_{i < N} z^i/i!` -/
def expSumQ (z : ℚ) (N : ℕ) : ℚ := ∑ i ∈ range N, z ^ i / (i.factorial : ℚ)

/-- the remainder's bound `|z|^N/(N!(1 - |z|/(N + 1)))` -/
def expRemQ (z : ℚ) (N : ℕ) : ℚ := |z| ^ N / ((N.factorial : ℚ) * (1 - |z| / (N + 1)))

/-- an upper bound of `e^z` for `|z| ≤ 1`, from 16 terms -/
def expUpQ (z : ℚ) : ℚ := expSumQ z 16 + expRemQ z 16

/-- a lower bound of `e^z` for `|z| ≤ 1`, from 16 terms -/
def expLoQ (z : ℚ) : ℚ := expSumQ z 16 - expRemQ z 16

theorem exp_enclosure (z : ℚ) (hz : |z| ≤ 1) :
    ((expLoQ z : ℚ) : ℝ) ≤ Real.exp z ∧ Real.exp z ≤ ((expUpQ z : ℚ) : ℝ) := by
  have hz' : |((z : ℚ) : ℝ)| ≤ 1 := by exact_mod_cast hz
  have h := exp_trunc (z : ℝ) |(z : ℝ)| le_rfl 16 (by norm_num; linarith)
  have hs : ((expSumQ z 16 : ℚ) : ℝ) = ∑ i ∈ range 16, (z : ℝ) ^ i / (i.factorial : ℝ) := by
    simp [expSumQ]
  have hr : ((expRemQ z 16 : ℚ) : ℝ) =
      |(z : ℝ)| ^ 16 / (((16 : ℕ).factorial : ℝ) * (1 - |(z : ℝ)| / ((16 : ℕ) + 1))) := by
    simp [expRemQ]
  have h' := abs_le.mp h
  rw [← hs, ← hr] at h'
  constructor
  · rw [expLoQ, Rat.cast_sub]; linarith [h'.2]
  · rw [expUpQ, Rat.cast_add]; linarith [h'.1]

/-! ## The steps on a state -/

section Mirrors

variable (uq : ℚ) (n : ℕ) (ρ : ℚ → ℚ)

/-- `v_k`'s bound `1/(k!(1 - b'/(k + 1)))` -/
def coreVQ (bp : ℚ) (k : ℕ) : ℚ := 1 / (k.factorial : ℚ) / (1 - bp / (k + 1))

/-- `E^tr_{d'}` over `ℚ` -/
def eTrQ (bp : ℚ) (d : ℕ) : ℚ := bp ^ (d + 1) / (((d + 1).factorial : ℚ) * (1 - bp / (d + 2)))

/-- step (3)'s first product `w = MUL(r', q)`: from Horner's `(e_2, π^q_2)` to `((Z̄_w + ε', ε' + b'e_2), ω')` -/
def expWL (πq : ℕ → ℚ) (bp : ℚ) (st : ℚ × List ℚ) : (ℚ × ℚ) × List ℚ :=
  ((ρ (bp * (coreVQ bp 2 + st.1) + GmulEQ uq n πq (fun i => st.2.getD i 0) (bp * (coreVQ bp 2 + st.1))),
      ρ (GmulEQ uq n πq (fun i => st.2.getD i 0) (bp * (coreVQ bp 2 + st.1)) + bp * st.1)),
    (List.range n).map fun i => ρ (GmulPQ uq n πq (fun i => st.2.getD i 0) (bp * (coreVQ bp 2 + st.1)) i))

/-- step (3)'s second product: to `(E^-, ω)` -/
def expYL (πq : ℕ → ℚ) (bp D : ℚ) (d : ℕ) (st : (ℚ × ℚ) × List ℚ) : ℚ × List ℚ :=
  (ρ (GmulEQ uq n πq (fun i => st.2.getD i 0) (bp * st.1.1) + bp * st.1.2 + eTrQ bp d + D),
    (List.range n).map fun i => ρ (GmulPQ uq n πq (fun i => st.2.getD i 0) (bp * st.1.1) i))

/-- step (3)'s sum and its scaling back: to `(E_0, ψ_0)` -/
def expTL (πq : ℕ → ℚ) (T0 η : ℚ) (st : ℚ × List ℚ) : ℚ × List ℚ :=
  (ρ (st.1 + GaddEQ uq n πq (fun i => st.2.getD i 0) (T0 + st.1) + n * η),
    (List.range n).map fun i => ρ (GaddPQ uq n πq (fun i => st.2.getD i 0) (T0 + st.1) i + η))

/-- one squaring, `sqB` -/
def expSqL (T T' g : ℚ) (st : ℚ × List ℚ) : ℚ × List ℚ :=
  (ρ (2 * g * st.1 + st.1 ^ 2 + GmulEQ uq n (fun i => st.2.getD i 0) (fun i => st.2.getD i 0) ((T + st.1) ^ 2) +
      GaddEQ uq n (fun i => 2 * st.2.getD i 0)
        (GmulPQ uq n (fun i => st.2.getD i 0) (fun i => st.2.getD i 0) ((T + st.1) ^ 2))
        (T' + 2 * st.1 * (1 + T) + st.1 ^ 2 +
          GmulEQ uq n (fun i => st.2.getD i 0) (fun i => st.2.getD i 0) ((T + st.1) ^ 2))),
    (List.range n).map fun i => ρ (GaddPQ uq n (fun i => 2 * st.2.getD i 0)
      (GmulPQ uq n (fun i => st.2.getD i 0) (fun i => st.2.getD i 0) ((T + st.1) ^ 2))
      (T' + 2 * st.1 * (1 + T) + st.1 ^ 2 +
        GmulEQ uq n (fun i => st.2.getD i 0) (fun i => st.2.getD i 0) ((T + st.1) ^ 2)) i))

/-- the bound of a case from `(E_m, ψ_m)`: `(E_m + ε_s)/v + (e^δ - 1)`, with bounds of `e^b` or `e^{-a}`, of `v` from
below and of `e^δ - 1` -/
def expEpsL (Zexp v dexp : ℚ) (st : ℚ × List ℚ) : ℚ :=
  (st.1 + GaddfE'Q uq n (fun i => st.2.getD i 0) (Zexp + st.1 + ∑ i ∈ Ico 1 n, st.2.getD i 0) (Zexp + st.1)) / v +
    dexp

/-- `t̄_j`'s bound: `e^{2^j b'} - 1` for `r ≥ 0` and `1 - e^{-2^j b'}` for `r ≤ 0`, on the enclosure of `e^z` -/
def coreTQ (pos : Bool) (bp : ℚ) (j : ℕ) : ℚ :=
  ρ (if pos then expUpQ (2 ^ j * bp) - 1 else 1 - expLoQ (-(2 ^ j * bp)))

/-- `g_j`'s bound: `e^{2^j b'}` for `r ≥ 0` and `e^{-2^j a'}` for `r ≤ 0` -/
def coreGQ (pos : Bool) (ap bp : ℚ) (j : ℕ) : ℚ :=
  ρ (if pos then expUpQ (2 ^ j * bp) else expUpQ (-(2 ^ j * ap)))

end Mirrors

/-- a rational state bounds a real bound and its part bounds below `n` -/
abbrev Dom (n : ℕ) (E : ℝ) (ψ : ℕ → ℝ) (st : ℚ × List ℚ) : Prop :=
  E ≤ ((st.1 : ℚ) : ℝ) ∧ ∀ i < n, ψ i ≤ ((st.2.getD i 0 : ℚ) : ℝ)

theorem cast_coreVQ (bp : ℚ) (k : ℕ) : ((coreVQ bp k : ℚ) : ℝ) = invF k / (1 - (bp : ℝ) / (k + 1)) := by
  simp [coreVQ, invF]

/-- `E^tr` grows with `b'` -/
theorem eTr_le {b' : ℝ} {bp : ℚ} (hb0 : 0 ≤ b') (hb : b' ≤ (bp : ℝ)) (d : ℕ) (hbd : (bp : ℝ) < d + 2) :
    eTr b' d ≤ ((eTrQ bp d : ℚ) : ℝ) := by
  have hd2 : (0 : ℝ) < d + 2 := by positivity
  have h1 : 0 < 1 - (bp : ℝ) / (d + 2) := by rw [sub_pos, div_lt_one hd2]; exact hbd
  have h2 : 1 - (bp : ℝ) / (d + 2) ≤ 1 - b' / (d + 2) := by
    have := div_le_div_of_nonneg_right hb hd2.le
    linarith
  have hf : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have he : ((eTrQ bp d : ℚ) : ℝ) = (bp : ℝ) ^ (d + 1) / (((d + 1).factorial : ℝ) * (1 - (bp : ℝ) / (d + 2))) := by
    simp [eTrQ]
  rw [he]
  unfold eTr
  exact div_le_div₀ (pow_nonneg (hb0.trans hb) _) (pow_le_pow_left₀ hb0 hb _) (mul_pos hf h1)
    (mul_le_mul_of_nonneg_left h2 hf.le)

theorem getD_range_map (f : ℕ → ℚ) {N i : ℕ} (hi : i < N) : ((List.range N).map f).getD i 0 = f i := by
  rw [getD_map_range]
  simp only [hi, ↓reduceIte]

section Bounds

variable (p : ℤ) (n : ℕ) {uq : ℚ} (h : (uq : ℝ) = u p) {ρ : ℚ → ℚ} (hρ : ∀ q, q ≤ ρ q)

include h in
/-- `G_MUL` on real bounds is at most its mirror on rational bounds above them -/
theorem Gmul_le_mirror (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α β : ℕ → ℝ} {αq βq : ℕ → ℚ}
    (hα0 : ∀ i < n, 0 ≤ α i) (hβ0 : ∀ j < n, 0 ≤ β j) (hα : ∀ i < n, α i ≤ ((αq i : ℚ) : ℝ))
    (hβ : ∀ j < n, β j ≤ ((βq j : ℚ) : ℝ)) {Zb : ℝ} {Zq : ℚ} (hZ : Zb ≤ ((Zq : ℚ) : ℝ)) :
    GmulE p n α β Zb ≤ ((GmulEQ uq n αq βq Zq : ℚ) : ℝ) ∧
      ∀ i, GmulP p n α β Zb i ≤ ((GmulPQ uq n αq βq Zq i : ℚ) : ℝ) := by
  have hm := Gmul_mono_lt p n hA3 hα0 hβ0 hα hβ hZ
  rw [cast_GmulE p n h]
  exact ⟨hm.1, fun i => by rw [cast_GmulP p n h]; exact hm.2 i⟩

include h in
/-- `G_ADD` on real bounds is at most its mirror on rational bounds above them -/
theorem Gadd_le_mirror (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α β : ℕ → ℝ} {αq βq : ℕ → ℚ}
    (hα : ∀ i < n, α i ≤ ((αq i : ℚ) : ℝ)) (hβ : ∀ j < n, β j ≤ ((βq j : ℚ) : ℝ)) {Zb : ℝ} {Zq : ℚ}
    (hZ : Zb ≤ ((Zq : ℚ) : ℝ)) :
    GaddE p n α β Zb ≤ ((GaddEQ uq n αq βq Zq : ℚ) : ℝ) ∧
      ∀ i, GaddP p n α β Zb i ≤ ((GaddPQ uq n αq βq Zq i : ℚ) : ℝ) := by
  have hm := Gadd_mono_lt p n hn hA3 hα hβ hZ
  rw [cast_GaddE p n h]
  exact ⟨hm.1, fun i => by rw [cast_GaddP p n h]; exact hm.2 i⟩

include h in
/-- `G_ADDF`'s error bound on real bounds is at most its mirror on rational bounds above them -/
theorem Gaddf_le_mirror (hn : 1 ≤ n) {α : ℕ → ℝ} {αq : ℕ → ℚ} (hα : ∀ i < n, α i ≤ ((αq i : ℚ) : ℝ))
    {lam0 Zb : ℝ} {lq Zq : ℚ} (hl : lam0 ≤ ((lq : ℚ) : ℝ)) (hZ : Zb ≤ ((Zq : ℚ) : ℝ)) :
    GaddfE' p n α lam0 Zb ≤ ((GaddfE'Q uq n αq lq Zq : ℚ) : ℝ) := by
  rw [cast_GaddfE' p n h]
  exact Gaddf_mono_lt p n hn hα hl hZ

include h hρ in
/-- step (3) for `d' ≠ 1`: from a state above Horner's `(e_2, π^q_2)`, the three steps give a state above
`(E_0, ψ_0)` -/
theorem core0_le (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {π' : ℕ → ℝ} {πq : ℕ → ℚ}
    (hπ0 : ∀ i, 0 ≤ π' i) (hπ : ∀ i < n, π' i ≤ ((πq i : ℚ) : ℝ)) {b' : ℝ} {bp : ℚ} (hb0 : 0 ≤ b')
    (hb : b' ≤ ((bp : ℚ) : ℝ)) (hbp : bp < 1) {T0 D η : ℝ} {T0q Dq ηq : ℚ} (hT : T0 ≤ ((T0q : ℚ) : ℝ))
    (hD : D ≤ ((Dq : ℚ) : ℝ)) (hη : η ≤ ((ηq : ℚ) : ℝ)) (Fk : ℕ → ℕ → ℝ) (φ : ℕ → ℝ) (hφ : ∀ k, 0 ≤ φ k)
    (d : ℕ) (hd : d ≠ 1) (st : ℚ × List ℚ)
    (hst : Dom n (hornerB p n π' b' 0 0 Fk φ (coreV b' d) d (d - 2)).1
      (hornerB p n π' b' 0 0 Fk φ (coreV b' d) d (d - 2)).2 st) :
    Dom n (core0 p n T0 D η π' b' Fk φ d).1 (core0 p n T0 D η π' b' Fk φ d).2
      (expTL uq n ρ πq T0q ηq (expYL uq n ρ πq bp Dq d (expWL uq n ρ πq bp st))) := by
  have hbp' : ((bp : ℚ) : ℝ) < 1 := by exact_mod_cast hbp
  have hbp0 : (0 : ℝ) ≤ ((bp : ℚ) : ℝ) := hb0.trans hb
  have hvk : ∀ k, 0 ≤ coreV b' d k := fun k =>
    (coreV_le hb0 hb d k (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])).1
  obtain ⟨hv0, hv⟩ := coreV_le hb0 hb d 2 (by norm_num; linarith)
  rw [← cast_coreVQ] at hv
  obtain ⟨hH0, hH20⟩ := hornerB_nonneg p n hA3 hπ0 hb0 le_rfl le_rfl Fk hφ hvk d (d - 2)
  obtain ⟨H, hHd⟩ : ∃ H, H = hornerB p n π' b' 0 0 Fk φ (coreV b' d) d (d - 2) := ⟨_, rfl⟩
  rw [← hHd] at hst hH0 hH20
  obtain ⟨s1, s2⟩ := hst
  -- `w = MUL(r', q)`
  obtain ⟨Zw, hZw⟩ : ∃ Zw, Zw = b' * (coreV b' d 2 + H.1) := ⟨_, rfl⟩
  obtain ⟨Zwq, hZwq⟩ : ∃ Zwq, Zwq = bp * (coreVQ bp 2 + st.1) := ⟨_, rfl⟩
  have hZw0 : 0 ≤ Zw := by rw [hZw]; exact mul_nonneg hb0 (add_nonneg hv0 hH0)
  have hZwle : Zw ≤ ((Zwq : ℚ) : ℝ) := by
    rw [hZw, hZwq]
    push_cast
    exact mul_le_mul hb (add_le_add hv s1) (add_nonneg hv0 hH0) hbp0
  obtain ⟨w1, w2⟩ := Gmul_le_mirror p n h hA3 (fun i _ => hπ0 i) (fun i _ => hH20 i) hπ s2 hZwle
  obtain ⟨hε10, hω10⟩ := Gmul_nonneg p n hA3 hπ0 hH20 hZw0
  obtain ⟨ε1, hε1⟩ : ∃ ε1, ε1 = GmulE p n π' H.2 Zw := ⟨_, rfl⟩
  obtain ⟨ω1, hω1⟩ : ∃ ω1, ω1 = GmulP p n π' H.2 Zw := ⟨_, rfl⟩
  rw [← hε1] at w1 hε10
  rw [← hω1] at w2 hω10
  obtain ⟨sW, hsW⟩ : ∃ sW, sW = expWL uq n ρ πq bp st := ⟨_, rfl⟩
  rw [← hsW]
  have hW11 : Zw + ε1 ≤ ((sW.1.1 : ℚ) : ℝ) := by
    rw [hsW]
    simp only [expWL]
    rw [← hZwq]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    linarith
  have hW12 : ε1 + b' * H.1 ≤ ((sW.1.2 : ℚ) : ℝ) := by
    rw [hsW]
    simp only [expWL]
    rw [← hZwq]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    linarith [mul_le_mul hb s1 hH0 hbp0]
  have hW2 : ∀ i < n, ω1 i ≤ ((sW.2.getD i 0 : ℚ) : ℝ) := fun i hi => by
    rw [hsW]
    simp only [expWL]
    rw [getD_range_map _ hi, ← hZwq]
    exact (w2 i).trans (Rat.cast_le.mpr (hρ _))
  -- the second product
  obtain ⟨Zy, hZy⟩ : ∃ Zy, Zy = b' * (Zw + ε1) := ⟨_, rfl⟩
  have hZy0 : 0 ≤ Zy := by rw [hZy]; exact mul_nonneg hb0 (add_nonneg hZw0 hε10)
  have hZyle : Zy ≤ ((bp * sW.1.1 : ℚ) : ℝ) := by
    rw [hZy]
    push_cast
    exact mul_le_mul hb hW11 (add_nonneg hZw0 hε10) hbp0
  obtain ⟨y1, y2⟩ := Gmul_le_mirror p n h hA3 (fun i _ => hπ0 i) (fun i _ => hω10 i) hπ hW2 hZyle
  obtain ⟨hε20, hω0⟩ := Gmul_nonneg p n hA3 hπ0 hω10 hZy0
  obtain ⟨ε2, hε2⟩ : ∃ ε2, ε2 = GmulE p n π' ω1 Zy := ⟨_, rfl⟩
  obtain ⟨ω, hω⟩ : ∃ ω, ω = GmulP p n π' ω1 Zy := ⟨_, rfl⟩
  rw [← hε2] at y1 hε20
  rw [← hω] at y2 hω0
  obtain ⟨Em, hEm⟩ : ∃ Em, Em = ε2 + b' * (ε1 + b' * H.1) + eTr b' d + D := ⟨_, rfl⟩
  obtain ⟨sY, hsY⟩ : ∃ sY, sY = expYL uq n ρ πq bp Dq d sW := ⟨_, rfl⟩
  rw [← hsY]
  have hbd : ((bp : ℚ) : ℝ) < d + 2 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hY1 : Em ≤ ((sY.1 : ℚ) : ℝ) := by
    rw [hsY]
    simp only [expYL]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    rw [hEm]
    have a1 := mul_le_mul hb hW12 (add_nonneg hε10 (mul_nonneg hb0 hH0)) hbp0
    linarith [eTr_le hb0 hb d hbd]
  have hY2 : ∀ i < n, ω i ≤ ((sY.2.getD i 0 : ℚ) : ℝ) := fun i hi => by
    rw [hsY]
    simp only [expYL]
    rw [getD_range_map _ hi]
    exact (y2 i).trans (Rat.cast_le.mpr (hρ _))
  -- the sum and its scaling back
  have hZt : T0 + Em ≤ ((T0q + sY.1 : ℚ) : ℝ) := by push_cast; linarith
  obtain ⟨t1, t2⟩ := Gadd_le_mirror p n h hn hA3 hπ hY2 hZt
  have hcore : core0 p n T0 D η π' b' Fk φ d =
      (Em + GaddE p n π' ω (T0 + Em) + n * η, fun i => GaddP p n π' ω (T0 + Em) i + η) := by
    simp only [core0, hd, ↓reduceIte]
    rw [hEm, hε2, hω, hZy, hε1, hω1, hZw, hHd]
  rw [hcore]
  refine ⟨?_, fun i hi => ?_⟩
  · show Em + GaddE p n π' ω (T0 + Em) + n * η ≤ _
    simp only [expTL]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    linarith [mul_le_mul_of_nonneg_left hη (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · show GaddP p n π' ω (T0 + Em) i + η ≤ _
    simp only [expTL]
    rw [getD_range_map _ hi]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    linarith [t2 i]

include h hρ in
/-- one squaring: a state above `(E, ψ)` gives one above `sqB`'s -/
theorem sqB_le (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {T T' g E : ℝ} {ψ : ℕ → ℝ} {Tq T'q gq : ℚ}
    (hT0 : 0 ≤ T) (hT : T ≤ ((Tq : ℚ) : ℝ)) (hT' : T' ≤ ((T'q : ℚ) : ℝ)) (hg0 : 0 ≤ g) (hg : g ≤ ((gq : ℚ) : ℝ))
    (hE0 : 0 ≤ E) (hψ0 : ∀ i, 0 ≤ ψ i) (st : ℚ × List ℚ) (hst : Dom n E ψ st) :
    Dom n (sqB p n T T' g E ψ).1 (sqB p n T T' g E ψ).2 (expSqL uq n ρ Tq T'q gq st) := by
  obtain ⟨s1, s2⟩ := hst
  have hEq0 : (0 : ℝ) ≤ ((st.1 : ℚ) : ℝ) := hE0.trans s1
  have hZm : (T + E) ^ 2 ≤ (((Tq + st.1) ^ 2 : ℚ) : ℝ) := by
    push_cast
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  obtain ⟨m1, m2⟩ := Gmul_le_mirror p n h hA3 (fun i _ => hψ0 i) (fun i _ => hψ0 i) s2 s2 hZm
  obtain ⟨hεm0, -⟩ := Gmul_nonneg p n hA3 hψ0 hψ0 (Zb := (T + E) ^ 2) (by positivity)
  obtain ⟨εm, hεm⟩ : ∃ εm, εm = GmulE p n ψ ψ ((T + E) ^ 2) := ⟨_, rfl⟩
  rw [← hεm] at m1 hεm0
  have hE2 : E ^ 2 ≤ ((st.1 : ℚ) : ℝ) ^ 2 := pow_le_pow_left₀ hE0 s1 2
  have hET : 2 * E * (1 + T) ≤ 2 * ((st.1 : ℚ) : ℝ) * (1 + ((Tq : ℚ) : ℝ)) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hZs : T' + 2 * E * (1 + T) + E ^ 2 + εm ≤ ((T'q + 2 * st.1 * (1 + Tq) + st.1 ^ 2 +
      GmulEQ uq n (fun i => st.2.getD i 0) (fun i => st.2.getD i 0) ((Tq + st.1) ^ 2) : ℚ) : ℝ) := by
    push_cast
    linarith
  obtain ⟨a1, a2⟩ := Gadd_le_mirror p n h hn hA3 (α := fun i => 2 * ψ i)
    (αq := fun i => 2 * st.2.getD i 0) (fun i hi => by push_cast; linarith [s2 i hi]) (fun j _ => m2 j) hZs
  have hgE : 2 * g * E ≤ 2 * ((gq : ℚ) : ℝ) * ((st.1 : ℚ) : ℝ) :=
    mul_le_mul (by linarith) s1 hE0 (by linarith)
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [sqB, expSqL]
    rw [← hεm]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    linarith
  · simp only [sqB, expSqL]
    rw [getD_range_map _ hi, ← hεm]
    exact (a2 i).trans (Rat.cast_le.mpr (hρ _))

include h in
/-- the bound of a case: from a state above `(E_m, ψ_m)`, with `Z̄_r` above `e^b` or `e^{-a}`, `v_q` below `v` and
`d_q` above `e^δ - 1` -/
theorem expEps_le (hn : 1 ≤ n) {E Zr V dr : ℝ} {ψ : ℕ → ℝ} {Zexp vq dexp : ℚ} (hE0 : 0 ≤ E)
    (hψ0 : ∀ i, 0 ≤ ψ i) (hZr0 : 0 ≤ Zr) (hZ : Zr ≤ ((Zexp : ℚ) : ℝ)) (hv0 : 0 < vq) (hv : ((vq : ℚ) : ℝ) ≤ V)
    (hd : dr ≤ ((dexp : ℚ) : ℝ)) (st : ℚ × List ℚ) (hst : Dom n E ψ st) :
    (E + GaddfE' p n ψ (Zr + E + ∑ i ∈ Ico 1 n, ψ i) (Zr + E)) / V + dr ≤
      ((expEpsL uq n Zexp vq dexp st : ℚ) : ℝ) := by
  obtain ⟨s1, s2⟩ := hst
  have hsum : ∑ i ∈ Ico 1 n, ψ i ≤ ((∑ i ∈ Ico 1 n, st.2.getD i 0 : ℚ) : ℝ) := by
    push_cast
    exact sum_le_sum fun i hi => s2 i (mem_Ico.mp hi).2
  have hsum0 : 0 ≤ ∑ i ∈ Ico 1 n, ψ i := sum_nonneg fun i _ => hψ0 i
  have hl : Zr + E + ∑ i ∈ Ico 1 n, ψ i ≤ ((Zexp + st.1 + ∑ i ∈ Ico 1 n, st.2.getD i 0 : ℚ) : ℝ) := by
    push_cast at hsum ⊢
    linarith
  have hZb : Zr + E ≤ ((Zexp + st.1 : ℚ) : ℝ) := by push_cast; linarith
  have hεs := Gaddf_le_mirror p n h hn s2 hl hZb
  have hεs0 : 0 ≤ GaddfE' p n ψ (Zr + E + ∑ i ∈ Ico 1 n, ψ i) (Zr + E) :=
    gErr_nonneg p n (addfX_nonneg p n hψ0 (by linarith)) (by linarith) le_rfl
  have hv0' : (0 : ℝ) < ((vq : ℚ) : ℝ) := by exact_mod_cast hv0
  simp only [expEpsL]
  push_cast
  have hnum : E + GaddfE' p n ψ (Zr + E + ∑ i ∈ Ico 1 n, ψ i) (Zr + E) ≤ ((st.1 : ℚ) : ℝ) +
      ((GaddfE'Q uq n (fun i => st.2.getD i 0) (Zexp + st.1 + ∑ i ∈ Ico 1 n, st.2.getD i 0) (Zexp + st.1) : ℚ) : ℝ) :=
    add_le_add s1 hεs
  exact add_le_add (div_le_div₀ ((add_nonneg hE0 hεs0).trans hnum) hnum hv0' hv) hd

omit h in
include hρ in
/-- `t̄_j` is nonnegative and at most its mirror -/
theorem coreT_le {pos : Bool} {b' : ℝ} {bp : ℚ} (hb0 : 0 ≤ b') (hb : b' ≤ ((bp : ℚ) : ℝ)) (j : ℕ)
    (hj : 2 ^ j * bp ≤ 1) : 0 ≤ coreT pos b' j ∧ coreT pos b' j ≤ ((coreTQ ρ pos bp j : ℚ) : ℝ) := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hbp0 : (0 : ℚ) ≤ bp := by exact_mod_cast hb0.trans hb
  have hz0 : (0 : ℚ) ≤ 2 ^ j * bp := mul_nonneg (by positivity) hbp0
  have hle : (2 : ℝ) ^ j * b' ≤ (((2 ^ j * bp : ℚ)) : ℝ) := by
    push_cast
    exact mul_le_mul_of_nonneg_left hb h2.le
  have h0 : 0 ≤ (2 : ℝ) ^ j * b' := mul_nonneg h2.le hb0
  cases pos with
  | true =>
    simp only [coreT, coreTQ, ↓reduceIte]
    obtain ⟨-, e2⟩ := exp_enclosure (2 ^ j * bp) (by rw [abs_of_nonneg hz0]; exact hj)
    refine ⟨by linarith [Real.one_le_exp h0], le_trans ?_ (Rat.cast_le.mpr (hρ _))⟩
    push_cast at e2 hle ⊢
    linarith [Real.exp_le_exp.mpr hle]
  | false =>
    simp only [coreT, coreTQ, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨e1, -⟩ := exp_enclosure (-(2 ^ j * bp)) (by rw [abs_neg, abs_of_nonneg hz0]; exact hj)
    refine ⟨by linarith [Real.exp_le_one_iff.mpr (by linarith : -((2 : ℝ) ^ j * b') ≤ 0)],
      le_trans ?_ (Rat.cast_le.mpr (hρ _))⟩
    push_cast at e1 hle ⊢
    linarith [Real.exp_le_exp.mpr (neg_le_neg hle)]

omit h in
include hρ in
/-- `g_j` is nonnegative and at most its mirror -/
theorem coreG_le {pos : Bool} {a' b' : ℝ} {ap bp : ℚ} (ha0 : 0 ≤ ap) (ha : ((ap : ℚ) : ℝ) ≤ a') (hb0 : 0 ≤ b')
    (hb : b' ≤ ((bp : ℚ) : ℝ)) (j : ℕ) (hja : 2 ^ j * ap ≤ 1) (hjb : 2 ^ j * bp ≤ 1) :
    0 ≤ coreG pos a' b' j ∧ coreG pos a' b' j ≤ ((coreGQ ρ pos ap bp j : ℚ) : ℝ) := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hbp0 : (0 : ℚ) ≤ bp := by exact_mod_cast hb0.trans hb
  cases pos with
  | true =>
    simp only [coreG, coreGQ, ↓reduceIte]
    have hz0 : (0 : ℚ) ≤ 2 ^ j * bp := mul_nonneg (by positivity) hbp0
    obtain ⟨-, e2⟩ := exp_enclosure (2 ^ j * bp) (by rw [abs_of_nonneg hz0]; exact hjb)
    have hle : (2 : ℝ) ^ j * b' ≤ (((2 ^ j * bp : ℚ)) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_left hb h2.le
    exact ⟨(Real.exp_pos _).le, ((Real.exp_le_exp.mpr hle).trans e2).trans (Rat.cast_le.mpr (hρ _))⟩
  | false =>
    simp only [coreG, coreGQ, Bool.false_eq_true, ↓reduceIte]
    have hz0 : (0 : ℚ) ≤ 2 ^ j * ap := mul_nonneg (by positivity) ha0
    obtain ⟨-, e2⟩ := exp_enclosure (-(2 ^ j * ap)) (by rw [abs_neg, abs_of_nonneg hz0]; exact hja)
    have hle : -((2 : ℝ) ^ j * a') ≤ (((-(2 ^ j * ap) : ℚ)) : ℝ) := by
      push_cast
      linarith [mul_le_mul_of_nonneg_left ha h2.le]
    exact ⟨(Real.exp_pos _).le, ((Real.exp_le_exp.mpr hle).trans e2).trans (Rat.cast_le.mpr (hρ _))⟩

include h hρ in
/-- step (3) from Horner's run: the three steps on the last state of `hornerRunL`, with `π^z` a list and `v_k`
replaced by its bound, give a state above `(E_0, ψ_0)` -/
theorem core0_cert (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {π' : ℕ → ℝ} (pq : List ℚ)
    (hπ0 : ∀ i, 0 ≤ π' i) (hπ : ∀ i < n, π' i ≤ ((pq.getD i 0 : ℚ) : ℝ)) (hpq0 : ∀ i, 0 ≤ pq.getD i 0)
    {b' : ℝ} {bp : ℚ} (hb0 : 0 ≤ b') (hb : b' ≤ ((bp : ℚ) : ℝ)) (hbp : bp < 1) {T0 D η : ℝ} {T0q Dq ηq : ℚ}
    (hT : T0 ≤ ((T0q : ℚ) : ℝ)) (hD : D ≤ ((Dq : ℚ) : ℝ)) (hη : η ≤ ((ηq : ℚ) : ℝ)) (Fk : ℕ → ℕ → ℚ)
    (hF0 : ∀ k i, n ≤ i → Fk k i = 0) (φ : ℕ → ℚ) (hφ : ∀ k, 0 ≤ φ k) (d : ℕ) (hd : d ≠ 1) :
    Dom n (core0 p n T0 D η π' b' (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φ k : ℚ) : ℝ)) d).1
      (core0 p n T0 D η π' b' (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φ k : ℚ) : ℝ)) d).2
      (expTL uq n ρ (fun i => pq.getD i 0) T0q ηq (expYL uq n ρ (fun i => pq.getD i 0) bp Dq d
        (expWL uq n ρ (fun i => pq.getD i 0) bp
          (hornerRunL uq n ρ (fun i => pq.getD i 0) bp 0 0 Fk φ (coreVQ bp) d 0 (d - 2)
            (hornerInitL n Fk φ d))))) := by
  have hbp' : ((bp : ℚ) : ℝ) < 1 := by exact_mod_cast hbp
  have hbp0 : (0 : ℝ) ≤ ((bp : ℚ) : ℝ) := hb0.trans hb
  have hbpq0 : (0 : ℚ) ≤ bp := by exact_mod_cast hbp0
  have hφ' : ∀ k, (0 : ℝ) ≤ ((φ k : ℚ) : ℝ) := fun k => by exact_mod_cast hφ k
  have hvk : ∀ k, 0 ≤ coreV b' d k ∧ coreV b' d k ≤ ((coreVQ bp k : ℚ) : ℝ) := fun k => by
    rw [cast_coreVQ]
    exact coreV_le hb0 hb d k (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hvq0 : ∀ k, (0 : ℚ) ≤ coreVQ bp k := fun k => by
    have := (hvk k).1.trans (hvk k).2
    exact_mod_cast this
  refine core0_le p n h hρ hn hA3 hπ0 hπ hb0 hb hbp hT hD hη _ _ hφ' d hd _ ?_
  -- Horner's bounds: below `n`, then at the rational `z̄` and `v`, then their rounded mirrors
  have ht := hornerB_trunc p n π' b' 0 0 (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φ k : ℚ) : ℝ)) (coreV b' d) d
    (d - 2)
  have hm := hornerB_mono2 p n hA3 (πz := trunc n π') (πz' := fun i => ((pq.getD i 0 : ℚ) : ℝ))
    (trunc_nonneg n fun i _ => hπ0 i) (fun i => by
      unfold trunc
      split_ifs with hi
      · exact hπ i hi
      · exact_mod_cast hpq0 i) hb0 hb (le_refl (0 : ℝ)) (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
    (fun k i => ((Fk k i : ℚ) : ℝ)) hφ' (fun k => (hvk k).1) (fun k => (hvk k).2) d (d - 2)
  have hr := hornerRunL_ge p n h hρ hn hA3 (πz := fun i => ((pq.getD i 0 : ℚ) : ℝ))
    (πzq := fun i => pq.getD i 0) (fun i => by exact_mod_cast hpq0 i) (fun i => le_rfl) hbpq0 (εz := 0)
    (εzq := 0) le_rfl (by simp) (η := 0) le_rfl Fk hF0 hφ hvq0 d (d - 2)
  simp only [Rat.cast_zero] at hr
  rw [ht] at hm
  exact ⟨hm.1.trans hr.1, fun i _ => (hm.2 i).trans (hr.2 i)⟩

include h hρ in
/-- the squarings: from a state above `(E_0, ψ_0)`, states that follow each other by `expSqL` stay above `coreE`'s -/
theorem coreE_cert (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {T g : ℕ → ℝ} {E0 : ℝ} {ψ0 : ℕ → ℝ}
    (Tq gq : ℕ → ℚ) (m : ℕ) (hT0 : ∀ j, 0 ≤ T j) (hT : ∀ j ≤ m, T j ≤ ((Tq j : ℚ) : ℝ)) (hg0 : ∀ j, 0 ≤ g j)
    (hg : ∀ j < m, g j ≤ ((gq j : ℚ) : ℝ)) (hE0 : 0 ≤ E0) (hψ0 : ∀ i, 0 ≤ ψ0 i) (sts : ℕ → ℚ × List ℚ)
    (h0 : Dom n E0 ψ0 (sts 0))
    (hstep : ∀ j < m, expSqL uq n ρ (Tq j) (Tq (j + 1)) (gq j) (sts j) = sts (j + 1)) :
    ∀ j ≤ m, Dom n (coreE p n T g E0 ψ0 j).1 (coreE p n T g E0 ψ0 j).2 (sts j) ∧
      0 ≤ (coreE p n T g E0 ψ0 j).1 ∧ ∀ i, 0 ≤ (coreE p n T g E0 ψ0 j).2 i
  | 0, _ => ⟨h0, hE0, hψ0⟩
  | j + 1, hj => by
    obtain ⟨i1, i2, i3⟩ := coreE_cert hn hA3 Tq gq m hT0 hT hg0 hg hE0 hψ0 sts h0 hstep j (by omega)
    obtain ⟨E, hE⟩ : ∃ E, E = (coreE p n T g E0 ψ0 j).1 := ⟨_, rfl⟩
    obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = (coreE p n T g E0 ψ0 j).2 := ⟨_, rfl⟩
    rw [← hE, ← hψ] at i1
    rw [← hE] at i2
    rw [← hψ] at i3
    have hs := sqB_le p n h hρ hn hA3 (hT0 j) (hT j (by omega)) (hT (j + 1) hj) (hg0 j) (hg j (by omega)) i2 i3
      (sts j) i1
    rw [hstep j (by omega)] at hs
    have hce : coreE p n T g E0 ψ0 (j + 1) = sqB p n (T j) (T (j + 1)) (g j) E ψ := by
      rw [hE, hψ]
      rfl
    rw [hce]
    refine ⟨hs, ?_, ?_⟩
    · obtain ⟨hεm0, hν0⟩ := Gmul_nonneg p n hA3 i3 i3 (Zb := (T j + E) ^ 2) (by positivity)
      have hZs : 0 ≤ T (j + 1) + 2 * E * (1 + T j) + E ^ 2 + GmulE p n ψ ψ ((T j + E) ^ 2) := by
        have := hT0 j
        have := hT0 (j + 1)
        positivity
      obtain ⟨hεa0, -⟩ := Gadd_nonneg p n hA3 (α := fun i => 2 * ψ i) (fun i => by linarith [i3 i]) hν0 hZs
      simp only [sqB]
      have := hg0 j
      positivity
    · obtain ⟨hεm0, hν0⟩ := Gmul_nonneg p n hA3 i3 i3 (Zb := (T j + E) ^ 2) (by positivity)
      have hZs : 0 ≤ T (j + 1) + 2 * E * (1 + T j) + E ^ 2 + GmulE p n ψ ψ ((T j + E) ^ 2) := by
        have := hT0 j
        have := hT0 (j + 1)
        positivity
      obtain ⟨-, hπa0⟩ := Gadd_nonneg p n hA3 (α := fun i => 2 * ψ i) (fun i => by linarith [i3 i]) hν0 hZs
      simp only [sqB]
      exact hπa0

omit h in
/-- `(E_0, ψ_0)` is nonnegative -/
theorem core0_nonneg (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {π' : ℕ → ℝ} (hπ0 : ∀ i, 0 ≤ π' i) {b' T0 D η : ℝ}
    (hb0 : 0 ≤ b') (hb1 : b' < 1) (hT0 : 0 ≤ T0) (hD0 : 0 ≤ D) (hη0 : 0 ≤ η) (Fk : ℕ → ℕ → ℝ) (φ : ℕ → ℝ)
    (hφ : ∀ k, 0 ≤ φ k) (d : ℕ) :
    0 ≤ (core0 p n T0 D η π' b' Fk φ d).1 ∧ ∀ i, 0 ≤ (core0 p n T0 D η π' b' Fk φ d).2 i := by
  have htr : ∀ d : ℕ, 0 ≤ eTr b' d := fun d => by
    unfold eTr
    have hd2 : (0 : ℝ) < d + 2 := by positivity
    have h1 : 0 < 1 - b' / (d + 2) := by
      rw [sub_pos, div_lt_one hd2]
      linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    positivity
  by_cases hd : d = 1
  · subst hd
    simp only [core0, ↓reduceIte]
    exact ⟨add_nonneg (htr 1) hD0, hπ0⟩
  · have hvk : ∀ k, 0 ≤ coreV b' d k := fun k =>
      (coreV_le hb0 le_rfl d k (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])).1
    obtain ⟨hH0, hH20⟩ := hornerB_nonneg p n hA3 hπ0 hb0 le_rfl le_rfl Fk hφ hvk d (d - 2)
    obtain ⟨H, hHd⟩ : ∃ H, H = hornerB p n π' b' 0 0 Fk φ (coreV b' d) d (d - 2) := ⟨_, rfl⟩
    rw [← hHd] at hH0 hH20
    have hZw0 : 0 ≤ b' * (coreV b' d 2 + H.1) := mul_nonneg hb0 (add_nonneg (hvk 2) hH0)
    obtain ⟨hε10, hω10⟩ := Gmul_nonneg p n hA3 hπ0 hH20 hZw0
    have hZy0 : 0 ≤ b' * (b' * (coreV b' d 2 + H.1) + GmulE p n π' H.2 (b' * (coreV b' d 2 + H.1))) :=
      mul_nonneg hb0 (add_nonneg hZw0 hε10)
    obtain ⟨hε20, hω0⟩ := Gmul_nonneg p n hA3 hπ0 hω10 hZy0
    obtain ⟨Em, hEm⟩ : ∃ Em, Em = GmulE p n π' (GmulP p n π' H.2 (b' * (coreV b' d 2 + H.1)))
        (b' * (b' * (coreV b' d 2 + H.1) + GmulE p n π' H.2 (b' * (coreV b' d 2 + H.1)))) +
        b' * (GmulE p n π' H.2 (b' * (coreV b' d 2 + H.1)) + b' * H.1) + eTr b' d + D := ⟨_, rfl⟩
    have hEm0 : 0 ≤ Em := by
      rw [hEm]
      have := htr d
      have := mul_nonneg hb0 (add_nonneg hε10 (mul_nonneg hb0 hH0))
      linarith
    obtain ⟨ha0, hpa0⟩ := Gadd_nonneg p n hA3 hπ0 hω0 (Zb := T0 + Em) (by linarith)
    have hcore : core0 p n T0 D η π' b' Fk φ d = (Em + GaddE p n π'
        (GmulP p n π' (GmulP p n π' H.2 (b' * (coreV b' d 2 + H.1)))
          (b' * (b' * (coreV b' d 2 + H.1) + GmulE p n π' H.2 (b' * (coreV b' d 2 + H.1))))) (T0 + Em) + n * η,
        fun i => GaddP p n π' (GmulP p n π' (GmulP p n π' H.2 (b' * (coreV b' d 2 + H.1)))
          (b' * (b' * (coreV b' d 2 + H.1) + GmulE p n π' H.2 (b' * (coreV b' d 2 + H.1))))) (T0 + Em) i + η) := by
      simp only [core0, hd, ↓reduceIte]
      rw [hEm, hHd]
    rw [hcore]
    refine ⟨?_, fun i => add_nonneg (hpa0 i) hη0⟩
    have := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hη0
    show 0 ≤ Em + GaddE p n π' _ (T0 + Em) + n * η
    linarith

include h hρ in
/-- the bound of a case from stored states: Horner's run and step (3) at bounds `p_q` and `b_T` of `π'` and `b'`, the
squarings at a bound `b_B` of `b'`, each state following the one before by `expSqL`, and `expEpsL` on the last -/
theorem expEps_cert (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (pos : Bool) (e : ℤ) (m d : ℕ)
    (aq bq δq η₁q η₂q : ℚ) (π : ℕ → ℝ) (Fk : ℕ → ℕ → ℚ) (hF0 : ∀ k i, n ≤ i → Fk k i = 0) (φ : ℕ → ℚ)
    (hφ : ∀ k, 0 ≤ φ k) (hη₁ : 0 ≤ η₁q) (hη₂ : 0 ≤ η₂q) (ha0 : 0 ≤ aq) (hab : aq ≤ bq) (hδ0 : 0 ≤ δq)
    (hbδ : bq + δq ≤ 1) (hπ0 : ∀ i, 0 ≤ π i) (pq : List ℚ) (bpT : ℚ)
    (hpq : ∀ i < n, corePi e m π ((η₁q : ℚ) : ℝ) i ≤ ((pq.getD i 0 : ℚ) : ℝ)) (hpq0 : ∀ i, 0 ≤ pq.getD i 0)
    (hbpT : coreBp n e m ((bq : ℚ) : ℝ) ((η₁q : ℚ) : ℝ) ≤ ((bpT : ℚ) : ℝ)) (hbpT1 : bpT < 1) (st0 : ℚ × List ℚ)
    (hhead : if d = 1 then st0 = (eTrQ bpT 1 + 2 * n * η₁q, pq) else
      expTL uq n ρ (fun i => pq.getD i 0) (coreTQ ρ pos bpT 0) η₂q
        (expYL uq n ρ (fun i => pq.getD i 0) bpT (2 * n * η₁q) d (expWL uq n ρ (fun i => pq.getD i 0) bpT
          (hornerRunL uq n ρ (fun i => pq.getD i 0) bpT 0 0 Fk φ (coreVQ bpT) d 0 (d - 2)
            (hornerInitL n Fk φ d)))) = st0)
    (bpB : ℚ) (hbpB : coreBp n e m ((bq : ℚ) : ℝ) ((η₁q : ℚ) : ℝ) ≤ ((bpB : ℚ) : ℝ)) (hbpB1 : 2 ^ m * bpB ≤ 1)
    (sts : ℕ → ℚ × List ℚ) (hs0 : sts 0 = st0)
    (hstep : ∀ j < m, expSqL uq n ρ (coreTQ ρ pos bpB j) (coreTQ ρ pos bpB (j + 1))
      (coreGQ ρ pos ((2 : ℚ) ^ (-(m : ℤ)) * aq) bpB j) (sts j) = sts (j + 1))
    (εq : ℚ) (hv0 : 0 < (if pos then expLoQ (aq - δq) else expLoQ (-bq - δq)))
    (hfin : expEpsL uq n (ρ (if pos then expUpQ bq else expUpQ (-aq)))
      (if pos then expLoQ (aq - δq) else expLoQ (-bq - δq)) (expUpQ δq - 1) (sts m) ≤ εq) :
    expEps p n ((η₁q : ℚ) : ℝ) ((η₂q : ℚ) : ℝ) pos e m ((aq : ℚ) : ℝ) ((bq : ℚ) : ℝ) ((δq : ℚ) : ℝ) π
      (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φ k : ℚ) : ℝ)) d ≤ ((εq : ℚ) : ℝ) := by
  have hη₁' : (0 : ℝ) ≤ ((η₁q : ℚ) : ℝ) := by exact_mod_cast hη₁
  have hη₂' : (0 : ℝ) ≤ ((η₂q : ℚ) : ℝ) := by exact_mod_cast hη₂
  have hbq0 : (0 : ℚ) ≤ bq := ha0.trans hab
  have hbq1 : bq ≤ 1 := by linarith
  have ha0' : (0 : ℝ) ≤ ((aq : ℚ) : ℝ) := by exact_mod_cast ha0
  have hab' : ((aq : ℚ) : ℝ) ≤ ((bq : ℚ) : ℝ) := by exact_mod_cast hab
  have hφ' : ∀ k, (0 : ℝ) ≤ ((φ k : ℚ) : ℝ) := fun k => by exact_mod_cast hφ k
  have hc0 : (0 : ℝ) < (2 : ℝ) ^ (-(m : ℤ)) := by positivity
  have hnη : (0 : ℝ) ≤ (n : ℝ) * ((η₁q : ℚ) : ℝ) := mul_nonneg (Nat.cast_nonneg n) hη₁'
  obtain ⟨b', hb'⟩ : ∃ b', b' = coreBp n e m ((bq : ℚ) : ℝ) ((η₁q : ℚ) : ℝ) := ⟨_, rfl⟩
  rw [← hb'] at hbpT hbpB
  have hb'0 : 0 ≤ b' := by
    rw [hb', coreBp]
    have : (0 : ℝ) ≤ min ((bq : ℚ) : ℝ) ((2 : ℝ) ^ (e + 1)) := le_min (by exact_mod_cast hbq0) (by positivity)
    linarith [mul_nonneg hc0.le this]
  have hbpT1' : ((bpT : ℚ) : ℝ) < 1 := by exact_mod_cast hbpT1
  have hbpB0 : (0 : ℚ) ≤ bpB := by exact_mod_cast hb'0.trans hbpB
  obtain ⟨π', hπ'⟩ : ∃ π', π' = corePi e m π ((η₁q : ℚ) : ℝ) := ⟨_, rfl⟩
  rw [← hπ'] at hpq
  have hπ'0 : ∀ i, 0 ≤ π' i := fun i => by
    rw [hπ', corePi]
    have : (0 : ℝ) ≤ min (π i) ((2 : ℝ) ^ (e + 1)) := le_min (hπ0 i) (by positivity)
    linarith [mul_nonneg hc0.le this]
  obtain ⟨T, hT⟩ : ∃ T, T = coreT pos b' := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = coreG pos ((2 : ℝ) ^ (-(m : ℤ)) * ((aq : ℚ) : ℝ)) b' := ⟨_, rfl⟩
  have hT0 : ∀ j, 0 ≤ T j := fun j => by
    rw [hT]
    cases pos with
    | true =>
      simp only [coreT, ↓reduceIte]
      linarith [Real.one_le_exp (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ j) hb'0)]
    | false =>
      simp only [coreT, Bool.false_eq_true, ↓reduceIte]
      linarith [Real.exp_le_one_iff.mpr (by
        linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ j) hb'0] : -((2 : ℝ) ^ j * b') ≤ 0)]
  have hg0 : ∀ j, 0 ≤ g j := fun j => by
    rw [hg]
    unfold coreG
    split_ifs <;> exact (Real.exp_pos _).le
  -- the head
  obtain ⟨c0, hc0d⟩ : ∃ c0, c0 = core0 p n (T 0) (2 * n * ((η₁q : ℚ) : ℝ)) ((η₂q : ℚ) : ℝ) π' b'
      (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φ k : ℚ) : ℝ)) d := ⟨_, rfl⟩
  have hT00 : T 0 ≤ ((coreTQ ρ pos bpT 0 : ℚ) : ℝ) := by
    rw [hT]
    exact (coreT_le hρ hb'0 hbpT 0 (by simpa using hbpT1.le)).2
  have hD : 2 * (n : ℝ) * ((η₁q : ℚ) : ℝ) ≤ ((2 * n * η₁q : ℚ) : ℝ) := by push_cast; exact le_rfl
  have hhd : Dom n c0.1 c0.2 st0 := by
    rw [hc0d]
    by_cases hd : d = 1
    · subst hd
      simp only [↓reduceIte] at hhead
      rw [hhead]
      simp only [core0, ↓reduceIte]
      refine ⟨?_, fun i hi => hpq i hi⟩
      push_cast
      linarith [eTr_le hb'0 hbpT 1 (by push_cast; linarith)]
    · simp only [hd, ↓reduceIte] at hhead
      rw [← hhead]
      exact core0_cert p n h hρ hn hA3 pq hπ'0 hpq hpq0 hb'0 hbpT hbpT1 hT00 hD le_rfl Fk hF0 φ hφ d hd
  obtain ⟨hc00, hc01⟩ := core0_nonneg p n hA3 hπ'0 hb'0 (lt_of_le_of_lt hbpT hbpT1') (hT0 0)
    (by positivity : (0 : ℝ) ≤ 2 * n * ((η₁q : ℚ) : ℝ)) hη₂' (fun k i => ((Fk k i : ℚ) : ℝ))
    (fun k => ((φ k : ℚ) : ℝ)) hφ' d
  rw [← hc0d] at hc00 hc01
  -- the squarings
  have hpow : ∀ j ≤ m, (2 : ℚ) ^ j * bpB ≤ 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hbpB0).trans hbpB1
  have hap0 : (0 : ℚ) ≤ (2 : ℚ) ^ (-(m : ℤ)) * aq := mul_nonneg (by positivity) ha0
  have hapc : (((2 : ℚ) ^ (-(m : ℤ)) * aq : ℚ) : ℝ) = (2 : ℝ) ^ (-(m : ℤ)) * ((aq : ℚ) : ℝ) := by push_cast; rfl
  have hpowa : ∀ j ≤ m, (2 : ℚ) ^ j * ((2 : ℚ) ^ (-(m : ℤ)) * aq) ≤ 1 := fun j hj => by
    have h1 : (2 : ℚ) ^ j * (2 : ℚ) ^ (-(m : ℤ)) ≤ 1 := by
      rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
      exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    calc (2 : ℚ) ^ j * ((2 : ℚ) ^ (-(m : ℤ)) * aq) = (2 : ℚ) ^ j * (2 : ℚ) ^ (-(m : ℤ)) * aq := by ring
      _ ≤ 1 * aq := mul_le_mul_of_nonneg_right h1 ha0
      _ ≤ 1 := by linarith
  obtain ⟨f1, f2, f3⟩ := coreE_cert p n h hρ hn hA3 (T := T) (g := g) (coreTQ ρ pos bpB)
    (coreGQ ρ pos ((2 : ℚ) ^ (-(m : ℤ)) * aq) bpB) m hT0
    (fun j hj => by rw [hT]; exact (coreT_le hρ hb'0 hbpB j (hpow j hj)).2) hg0
    (fun j hj => by
      rw [hg]
      exact (coreG_le hρ hap0 hapc.le hb'0 hbpB j (hpowa j hj.le) (hpow j hj.le)).2)
    hc00 hc01 sts (by rw [hs0]; exact hhd) hstep m le_rfl
  have hcb : coreBound p n ((η₁q : ℚ) : ℝ) ((η₂q : ℚ) : ℝ) pos e m ((aq : ℚ) : ℝ) ((bq : ℚ) : ℝ) π
      (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φ k : ℚ) : ℝ)) d = coreE p n T g c0.1 c0.2 m := by
    rw [coreBound, hc0d, hT, hg, hb', hπ']
  -- the last ADDF and the division by `v`
  obtain ⟨Zr, hZr⟩ : ∃ Zr, Zr = (if pos then Real.exp ((bq : ℚ) : ℝ) else Real.exp (-((aq : ℚ) : ℝ))) := ⟨_, rfl⟩
  have hZr0 : 0 ≤ Zr := by rw [hZr]; split_ifs <;> exact (Real.exp_pos _).le
  have hZrle : Zr ≤ ((ρ (if pos then expUpQ bq else expUpQ (-aq)) : ℚ) : ℝ) := by
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    rw [hZr]
    cases pos with
    | true =>
      simp only [↓reduceIte]
      exact (exp_enclosure bq (by rw [abs_of_nonneg hbq0]; exact hbq1)).2
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have := (exp_enclosure (-aq) (by rw [abs_neg, abs_of_nonneg ha0]; linarith)).2
      push_cast at this
      exact this
  have hV : (((if pos then expLoQ (aq - δq) else expLoQ (-bq - δq)) : ℚ) : ℝ) ≤
      expV pos ((aq : ℚ) : ℝ) ((bq : ℚ) : ℝ) ((δq : ℚ) : ℝ) := by
    unfold expV
    cases pos with
    | true =>
      simp only [↓reduceIte]
      have := (exp_enclosure (aq - δq) (by rw [abs_le]; constructor <;> linarith)).1
      push_cast at this
      exact this
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have := (exp_enclosure (-bq - δq) (by rw [abs_le]; constructor <;> linarith)).1
      push_cast at this
      exact this
  have hdr : Real.exp ((δq : ℚ) : ℝ) - 1 ≤ ((expUpQ δq - 1 : ℚ) : ℝ) := by
    have := (exp_enclosure δq (by rw [abs_of_nonneg hδ0]; linarith)).2
    push_cast
    linarith
  have hfinal := expEps_le p n h hn f2 f3 hZr0 hZrle hv0 hV hdr (sts m) f1
  refine le_trans ?_ (hfinal.trans (Rat.cast_le.mpr hfin))
  rw [expEps, hcb]
  unfold expZ
  rw [← hZr]
  exact le_of_eq (by ring)

end Bounds

end ExpansionBounds
