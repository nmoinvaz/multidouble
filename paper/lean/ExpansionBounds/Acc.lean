import ExpansionBounds.Ops

/-!
# The accumulator's levels (`lem:acc`)

`K` deposits into the levels `s_0, …, s_n`, each `dep(s, l, t_l)` for `l = 0, …, n - 1` and then, for
`N = n`, `s_n ← RN(s_n + t_n)`. The bounds `S_m(k)` of (a) are those of the proof's recursion,
`S_0 = Γτ_0W` and `S_m(k) = Γ(τ_m W + m u ∑_{j ≤ k} S_{m-1}(j))`, which the rising factorial `k^{(r)}` puts in
the lemma's closed form.
-/

namespace ExpansionBounds

open Finset

/-- the rising factorial `k^{(r)} = k(k + 1)⋯(k + r - 1)`, with `k^{(0)} = 1` -/
noncomputable def rise (k : ℝ) (r : ℕ) : ℝ := ∏ i ∈ range r, (k + i)

theorem rise_succ_shift (k : ℝ) (r : ℕ) : rise k (r + 1) = k * rise (k + 1) r := by
  unfold rise
  rw [prod_range_succ', mul_comm]
  simp only [Nat.cast_zero, add_zero, Nat.cast_succ]
  congr 1
  exact prod_congr rfl fun i _ => by ring

theorem rise_succ (k : ℝ) (r : ℕ) : rise k (r + 1) = rise k r * (k + r) := by
  unfold rise
  rw [prod_range_succ]

theorem rise_nonneg (k : ℝ) (hk : 0 ≤ k) (r : ℕ) : 0 ≤ rise k r :=
  prod_nonneg fun i _ => by positivity

/-- `∑_{j=1}^k j^{(r)} = k^{(r+1)} / (r + 1)` -/
theorem sum_rise (r : ℕ) : ∀ k : ℕ, ∑ j ∈ Icc 1 k, rise (j : ℝ) r = rise (k : ℝ) (r + 1) / (r + 1)
  | 0 => by simp [rise, prod_range_succ']
  | k + 1 => by
    rw [sum_Icc_succ_top (by omega), sum_rise r k]
    have h1 : rise (k : ℝ) (r + 1) = k * rise ((k : ℝ) + 1) r := rise_succ_shift _ _
    have h2 : rise ((k : ℝ) + 1) (r + 1) = rise ((k : ℝ) + 1) r * ((k : ℝ) + 1 + r) := rise_succ _ _
    push_cast
    rw [h1, h2]
    have : (r : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

variable (τ : ℕ → ℝ) (W Γ uu : ℝ)

/-- `S_m(k)` by the proof's recursion: `S_0 = Γτ_0W` and `S_m(k) = Γ(τ_m W + m u ∑_{j=1}^k S_{m-1}(j))` -/
noncomputable def accS : ℕ → ℕ → ℝ
  | 0, _ => Γ * (τ 0 * W)
  | m + 1, k => Γ * (τ (m + 1) * W + (m + 1) * uu * ∑ j ∈ Icc 1 k, accS m j)

/-- the closed form of (a): `S_m(k) = ΓW ∑_{l=0}^m C(m, l) τ_l (Γu)^{m-l} k^{(m-l)}` -/
noncomputable def accSclosed (m k : ℕ) : ℝ :=
  Γ * W * ∑ l ∈ range (m + 1), (m.choose l : ℝ) * τ l * (Γ * uu) ^ (m - l) * rise k (m - l)

/-- the bound of (b): `Ē_lev = W ∑_{l=0}^n C(n + 1, l) τ_l (Γu)^{n+1-l} K^{(n+1-l)}` -/
noncomputable def accE (n K : ℕ) : ℝ :=
  W * ∑ l ∈ range (n + 1), ((n + 1).choose l : ℝ) * τ l * (Γ * uu) ^ (n + 1 - l) * rise K (n + 1 - l)

/-- `C(m, l) (m + 1) / (m + 1 - l) = C(m + 1, l)` for `l ≤ m` -/
theorem choose_ratio (m l : ℕ) (hl : l ≤ m) :
    (m.choose l : ℝ) * (m + 1) / ((m - l : ℕ) + 1) = ((m + 1).choose l : ℝ) := by
  have h := Nat.choose_mul_succ_eq m l
  have hpos : ((m - l : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  rw [div_eq_iff hpos]
  have : ((m + 1 - l : ℕ) : ℝ) = ((m - l : ℕ) : ℝ) + 1 := by
    rw [show m + 1 - l = m - l + 1 by omega]
    push_cast
    ring
  rw [← this]
  exact_mod_cast h

@[simp] theorem rise_zero (k : ℝ) : rise k 0 = 1 := by simp [rise]

/-- `(m + 1) u ∑_{j=1}^k S_m(j)`, in closed form: the `G_m(k)` bound of the proof -/
theorem sum_accSclosed (m k : ℕ) :
    ((m : ℝ) + 1) * uu * ∑ j ∈ Icc 1 k, accSclosed τ W Γ uu m j =
      W * ∑ l ∈ range (m + 1), ((m + 1).choose l : ℝ) * τ l * (Γ * uu) ^ (m + 1 - l) * rise k (m + 1 - l) := by
  unfold accSclosed
  have hterm : ∀ l ∈ range (m + 1), ((m : ℝ) + 1) * uu *
      (Γ * W * ∑ j ∈ Icc 1 k, (m.choose l : ℝ) * τ l * (Γ * uu) ^ (m - l) * rise j (m - l)) =
      W * (((m + 1).choose l : ℝ) * τ l * (Γ * uu) ^ (m + 1 - l) * rise k (m + 1 - l)) := by
    intro l hl
    rw [mem_range] at hl
    rw [← mul_sum, sum_rise, show m + 1 - l = (m - l) + 1 by omega, pow_succ, ← choose_ratio m l (by omega)]
    have : ((m - l : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  rw [mul_sum (range (m + 1)) _ W, ← sum_congr rfl hterm]
  simp only [mul_sum]
  exact sum_comm

theorem accS_eq : ∀ m k, accS τ W Γ uu m k = accSclosed τ W Γ uu m k
  | 0, k => by simp [accS, accSclosed]; ring
  | m + 1, k => by
    rw [accS, sum_congr rfl fun j _ => accS_eq m j]
    rw [sum_accSclosed]
    unfold accSclosed
    rw [sum_range_succ _ (m + 1)]
    simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, mul_one, rise_zero]
    ring

/-- (b)'s bound is `(n + 1) u ∑_{k=1}^K S_n(k)` -/
theorem accE_eq (n K : ℕ) : accE τ W Γ uu n K = ((n : ℝ) + 1) * uu * ∑ k ∈ Icc 1 K, accS τ W Γ uu n k := by
  rw [sum_congr rfl fun k _ => accS_eq τ W Γ uu n k, sum_accSclosed]
  rfl

/-- `G_m(k) = (m + 1) u ∑_{j=1}^k S_m(j)`, the proof's bound on the carries out of level `m` (the rounding errors
at level `n`) in deposits `1, …, k` -/
noncomputable def accG (m k : ℕ) : ℝ := ((m : ℝ) + 1) * uu * ∑ j ∈ Icc 1 k, accS τ W Γ uu m j

theorem accS_succ (m k : ℕ) : accS τ W Γ uu (m + 1) k = Γ * (τ (m + 1) * W + accG τ W Γ uu m k) := rfl

section Nonneg

variable {τ W Γ uu} (hτ : ∀ l, 0 ≤ τ l) (hW : 0 ≤ W) (hΓ : 0 ≤ Γ) (hu : 0 ≤ uu)
include hτ hW hΓ hu

theorem accS_nonneg : ∀ m k, 0 ≤ accS τ W Γ uu m k
  | 0, _ => mul_nonneg hΓ (mul_nonneg (hτ 0) hW)
  | m + 1, _ => mul_nonneg hΓ (add_nonneg (mul_nonneg (hτ _) hW)
      (mul_nonneg (mul_nonneg (by positivity) hu) (sum_nonneg fun j _ => accS_nonneg m j)))

theorem accG_nonneg (m k : ℕ) : 0 ≤ accG τ W Γ uu m k :=
  mul_nonneg (mul_nonneg (by positivity) hu) (sum_nonneg fun j _ => accS_nonneg hτ hW hΓ hu m j)

/-- `S_m(k)` grows with `k` -/
theorem accS_mono : ∀ m {j k : ℕ}, j ≤ k → accS τ W Γ uu m j ≤ accS τ W Γ uu m k
  | 0, _, _, _ => le_rfl
  | m + 1, j, k, hjk => by
    simp only [accS]
    refine mul_le_mul_of_nonneg_left
      (add_le_add_right (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) hu)) _) hΓ
    exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hjk) fun i _ _ => accS_nonneg hτ hW hΓ hu m i

theorem accG_mono (m : ℕ) {j k : ℕ} (hjk : j ≤ k) : accG τ W Γ uu m j ≤ accG τ W Γ uu m k :=
  mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hjk)
    fun i _ _ => accS_nonneg hτ hW hΓ hu m i) (mul_nonneg (by positivity) hu)

/-- `G_m(k - 1) ≤ (m + 1)(k - 1) u S_m(k)` -/
theorem accG_le (m k : ℕ) : accG τ W Γ uu m (k - 1) ≤ ((m : ℝ) + 1) * ((k - 1 : ℕ) : ℝ) * uu * accS τ W Γ uu m k := by
  unfold accG
  have h : ∑ j ∈ Icc 1 (k - 1), accS τ W Γ uu m j ≤ ∑ j ∈ Icc 1 (k - 1), accS τ W Γ uu m k :=
    sum_le_sum fun j hj => accS_mono hτ hW hΓ hu m (by simp at hj; omega)
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel] at h
  have hc : 0 ≤ ((m : ℝ) + 1) * uu := mul_nonneg (by positivity) hu
  calc ((m : ℝ) + 1) * uu * ∑ j ∈ Icc 1 (k - 1), accS τ W Γ uu m j
      ≤ ((m : ℝ) + 1) * uu * (((k - 1 : ℕ) : ℝ) * accS τ W Γ uu m k) := mul_le_mul_of_nonneg_left h hc
    _ = _ := by ring

end Nonneg

/-- the step of the proof at one carry or rounding: a level's new value `z` with `z ≤ A + G_p + G_o + |r|`, its
error `|r| ≤ u z`, its deposits `A ≤ τW`, the carries in `G_p` within the recursion's term, and the carries out
before it `G_o ≤ G_m(k - 1) + c u S` with `c ≤ m`, has `z ≤ S = Γ(τW + G_prev)` -/
theorem acc_core {z A Gp Go r S τW Gprev Gk1 Γ uu : ℝ} {m n k K : ℕ} (hz : z ≤ A + Gp + Go + r)
    (hr : r ≤ uu * z) (hA : A ≤ τW) (hGp : Gp ≤ Gprev) {c : ℕ} (hc : c ≤ m) (hGo : Go ≤ Gk1 + c * uu * S)
    (hGk1 : Gk1 ≤ ((m : ℝ) + 1) * ((k - 1 : ℕ) : ℝ) * uu * S) (hS : S = Γ * (τW + Gprev)) (hS0 : 0 ≤ S)
    (hmn : m ≤ n) (hk : 1 ≤ k) (hkK : k ≤ K) (hu : 0 ≤ uu) (hu1 : uu < 1)
    (hΓ : Γ * (1 - ((n : ℝ) + 1) * K * uu) = 1) : z ≤ S := by
  have h1 : τW + Gprev = S * (1 - ((n : ℝ) + 1) * K * uu) := by
    rw [hS]
    linear_combination (-(τW + Gprev)) * hΓ
  have hcount : ((m : ℝ) + 1) * ((k - 1 : ℕ) : ℝ) + c + 1 ≤ ((n : ℝ) + 1) * K := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have hm : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hc' : (c : ℝ) ≤ m := by exact_mod_cast hc
    have hk' : (k' : ℝ) + 1 ≤ K := by exact_mod_cast hkK
    have h0 : (0 : ℝ) ≤ k' := Nat.cast_nonneg _
    have h0m : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith
  have hz' : z * (1 - uu) ≤ S * (1 - uu) := by
    have : z * (1 - uu) ≤ S * (1 - ((n : ℝ) + 1) * K * uu) + (((m : ℝ) + 1) * ((k - 1 : ℕ) : ℝ) + c) * uu * S := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hcount (mul_nonneg hu hS0)]
  exact le_of_mul_le_mul_right hz' (by linarith)

theorem accG_succ (m k : ℕ) (hk : 1 ≤ k) :
    accG τ W Γ uu m k = accG τ W Γ uu m (k - 1) + ((m : ℝ) + 1) * uu * accS τ W Γ uu m k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [accG, Nat.add_sub_cancel]
  rw [sum_Icc_succ_top (by omega)]
  ring

variable (p : ℤ) (n : ℕ)

/-- a deposit `t_0, …, t_N`: `dep(s, l, t_l)` for `l = 0, …, n - 1`, then `s_n ← RN(s_n + t_n)` when `N = n` -/
noncomputable def depositOps (t : ℕ → ℝ) (top : Bool) : List LOp :=
  ((List.range n).map fun l => LOp.dep l (t l)) ++ if top then [LOp.round (t n)] else []

/-- the first `k` deposits, the `j`-th of `t j` and with `N = n` when `top j` -/
noncomputable def accOps (t : ℕ → ℕ → ℝ) (top : ℕ → Bool) (k : ℕ) : List LOp :=
  (List.range k).flatMap fun j => depositOps n (t (j + 1)) (top (j + 1))

/-- the `TwoSum`s at level `x < n` after `l` deps of a deposit, `min(l, x + 1)`, and its roundings at level `n`,
`l` -/
def cAfter (l x : ℕ) : ℕ := if x < n then min l (x + 1) else l

/-- the counts inside dep `l` at level `m'`: one more at the levels `l, …, m' - 1` -/
def cMid (l m' x : ℕ) : ℕ := cAfter n l x + if l ≤ x ∧ x < m' then 1 else 0

/-- the accumulator's bounds inside deposit `k`, with counts `c` in it and its deposits made at the levels `r`:
the levels within `S_x(k)`, the carries out of level `x < n` within `G_x(k - 1) + c_x u S_x(k)`, the rounding errors
at level `n` within `G_n(k - 1) + c_n u S_n(k)`, and each level's deposits within `τ_x(W_{k-1} + μ_k)`, without the
`μ_k` before deposit `k` reaches it -/
def AccB (τ μ : ℕ → ℝ) (W Γ : ℝ) (k : ℕ) (c : ℕ → ℕ) (r : ℕ → Bool) (st : LState) : Prop :=
  (∀ x ≤ n, |st.s x| ≤ accS τ W Γ (u p) x k) ∧
    (∀ x < n, st.outA x ≤ accG τ W Γ (u p) x (k - 1) + c x * u p * accS τ W Γ (u p) x k) ∧
    st.rA ≤ accG τ W Γ (u p) n (k - 1) + c n * u p * accS τ W Γ (u p) n k ∧
    ∀ x ≤ n, st.adone x ≤ τ x * (∑ j ∈ Icc 1 (k - 1), μ j + if r x then μ k else 0)

variable [Prec_gt_0 p]

/-- the settings of the lemma: `τ, μ ≥ 0`, `1 ≤ k ≤ K`, `Γ(1 - (n + 1)Ku) = 1` and `W ≥ W_k` -/
structure AccSet (τ μ : ℕ → ℝ) (W Γ : ℝ) (k K : ℕ) : Prop where
  hτ : ∀ l, 0 ≤ τ l
  hμ : ∀ j, 0 ≤ μ j
  hk : 1 ≤ k
  hkK : k ≤ K
  hΓ0 : 0 ≤ Γ
  hΓ : Γ * (1 - ((n : ℝ) + 1) * K * u p) = 1
  hW : ∑ j ∈ Icc 1 k, μ j ≤ W

omit [Prec_gt_0 p] in
theorem AccSet.W0 {τ μ : ℕ → ℝ} {W Γ : ℝ} {k K : ℕ} (h : AccSet p n τ μ W Γ k K) : 0 ≤ W :=
  (sum_nonneg fun j _ => h.hμ j).trans h.hW

omit [Prec_gt_0 p] in
theorem AccSet.Wk {τ μ : ℕ → ℝ} {W Γ : ℝ} {k K : ℕ} (h : AccSet p n τ μ W Γ k K) :
    ∑ j ∈ Icc 1 (k - 1), μ j + μ k ≤ W := by
  have : ∑ j ∈ Icc 1 k, μ j = ∑ j ∈ Icc 1 (k - 1), μ j + μ k := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := h.hk; omega⟩
    rw [sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
  linarith [h.hW]

omit [Prec_gt_0 p] in
/-- a level's deposits are within `τ_x W` -/
theorem AccSet.adone_le {τ μ : ℕ → ℝ} {W Γ : ℝ} {k K : ℕ} (h : AccSet p n τ μ W Γ k K) {a : ℝ} (b : Bool) (x : ℕ)
    (ha : a ≤ τ x * (∑ j ∈ Icc 1 (k - 1), μ j + if b then μ k else 0)) : a ≤ τ x * W := by
  refine ha.trans (mul_le_mul_of_nonneg_left ?_ (h.hτ x))
  have := h.Wk
  split_ifs <;> linarith [h.hμ k]

/-- `S_x(k) = Γ(τ_x W + G_{x-1}(k))`, with `G_{-1} = 0` -/
theorem accS_split (τ : ℕ → ℝ) (W Γ uu : ℝ) (x k : ℕ) :
    accS τ W Γ uu x k = Γ * (τ x * W + if x = 0 then 0 else accG τ W Γ uu (x - 1) k) := by
  rcases x with _ | x
  · simp [accS]
  · simp [accS_succ]

omit [Prec_gt_0 p] in
/-- the carries into level `x` are within `G_{x-1}(k)` while level `x - 1` has done at most `x` `TwoSum`s -/
theorem prevOut_le {τ μ : ℕ → ℝ} {W Γ : ℝ} {k K : ℕ} (h : AccSet p n τ μ W Γ k K) {c : ℕ → ℕ} {r : ℕ → Bool}
    {st : LState} (hB : AccB p n τ μ W Γ k c r st) (x : ℕ) (hx : x ≤ n) (hc : x ≠ 0 → c (x - 1) ≤ x) :
    prevOut st x ≤ if x = 0 then 0 else accG τ W Γ (u p) (x - 1) k := by
  unfold prevOut
  rcases Nat.eq_zero_or_pos x with rfl | hpos
  · simp
  · simp only [show x ≠ 0 by omega, ite_false]
    have h1 := hB.2.1 (x - 1) (by omega)
    have h2 := hc (by omega)
    rw [accG_succ τ W Γ (u p) (x - 1) k h.hk, show ((x - 1 : ℕ) : ℝ) + 1 = x by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
    have hS := accS_nonneg h.hτ h.W0 h.hΓ0 (u_pos p).le (x - 1) k
    have : (c (x - 1) : ℝ) * u p * accS τ W Γ (u p) (x - 1) k ≤ x * u p * accS τ W Γ (u p) (x - 1) k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast h2) (u_pos p).le) hS
    linarith

theorem cMid_self {l m : ℕ} (hlm : l ≤ m) (hm : m < n) : cMid n l m m = l := by
  simp [cMid, cAfter, hm]
  omega

theorem cMid_succ_self {l m : ℕ} (hlm : l ≤ m) (hm : m < n) : cMid n l (m + 1) m = cMid n l m m + 1 := by
  simp [cMid, cAfter, hm, hlm]

theorem cMid_succ_ne {l m x : ℕ} (hxm : x ≠ m) : cMid n l (m + 1) x = cMid n l m x := by
  simp only [cMid]
  have : (l ≤ x ∧ x < m + 1) ↔ (l ≤ x ∧ x < m) := by omega
  simp only [this]

omit [Prec_gt_0 p] in
theorem u_lt_one (hp : 1 < p) : u p < 1 := by linarith [u_le_half p hp]

/-- the `TwoSum` of dep `l` at level `m` keeps the bounds, and adds one to the count at `m` -/
theorem acc_twoAt (hp : 1 < p) {τ μ : ℕ → ℝ} {W Γ : ℝ} {k K : ℕ} (h : AccSet p n τ μ W Γ k K) {l m : ℕ}
    (hlm : l ≤ m) (hm : m < n) {e : ℝ} {st : LState} (hok : st.ok) (hD : DInv p n m e st)
    (hB : AccB p n τ μ W Γ k (cMid n l m) (fun x => decide (x ≤ l)) st) :
    DInv p n (m + 1) (twoSum p (st.s m) e).2 (twoAt p m e st) ∧
      AccB p n τ μ W Γ k (cMid n l (m + 1)) (fun x => decide (x ≤ l)) (twoAt p m e st) := by
  have hD' := twoAt_dinv p n hp hm hD
  refine ⟨hD', ?_⟩
  obtain ⟨-, hF, he, -⟩ := hD hok
  obtain ⟨⟨-, -, hlev', -, -, hin'⟩, -, -, -⟩ := hD' hok
  obtain ⟨b1, b2, b3, b4⟩ := hB
  have hu := u_pos p
  have hadd := (facts_a p hp (hF m) he).1
  have hr : |(twoSum p (st.s m) e).2| ≤ u p * |(twoSum p (st.s m) e).1| := by
    have h1 := abs_RN_sub_le_u_RN p (st.s m + e)
    have hs : (twoSum p (st.s m) e).1 = RN p (st.s m + e) := rfl
    rw [show (twoSum p (st.s m) e).2 = -(RN p (st.s m + e) - (st.s m + e)) by linarith, abs_neg, hs]
    exact h1
  have hz : |(twoSum p (st.s m) e).1| ≤
      st.adone m + prevOut st m + st.outA m + |(twoSum p (st.s m) e).2| := by
    have h1 := (hlev' m hm).2
    have h2 := hin' m hm.le
    rw [prevOut_twoAt] at h2
    simp only [twoAt, Function.update_self, show m ≠ m + 1 by omega, ite_false, add_zero] at h1 h2
    linarith
  have hc1 : m ≠ 0 → cMid n l m (m - 1) ≤ m := fun _ => by
    simp only [cMid, cAfter, show m - 1 < n by omega, ite_true]
    split_ifs <;> omega
  have hnew : |(twoSum p (st.s m) e).1| ≤ accS τ W Γ (u p) m k :=
    acc_core hz hr (AccSet.adone_le p n h _ m (b4 m hm.le)) (prevOut_le p n h ⟨b1, b2, b3, b4⟩ m hm.le hc1)
      (c := cMid n l m m) (by rw [cMid_self n hlm hm]; exact hlm) (b2 m hm)
      (accG_le h.hτ h.W0 h.hΓ0 hu.le m k) (accS_split τ W Γ (u p) m k)
      (accS_nonneg h.hτ h.W0 h.hΓ0 hu.le m k) hm.le h.hk h.hkK hu.le (u_lt_one p hp) h.hΓ
  refine ⟨fun x hx => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · rcases eq_or_ne x m with rfl | hxm
    · simpa [twoAt] using hnew
    · simpa [twoAt, Function.update_of_ne hxm] using b1 x hx
  · rcases eq_or_ne x m with rfl | hxm
    · simp only [twoAt, Function.update_self]
      rw [cMid_succ_self n hlm hm]
      push_cast
      have := b2 x hm
      nlinarith [hr, hnew]
    · simpa [twoAt, Function.update_of_ne hxm, cMid_succ_ne n hxm] using b2 x hx
  · simpa [twoAt, cMid_succ_ne n (show n ≠ m by omega)] using b3
  · simpa [twoAt] using b4 x hx

theorem cMid_n_eq {l x : ℕ} (hx : x < n) : cMid n l n x = cAfter n (l + 1) x := by
  simp only [cMid, cAfter, hx, ite_true]
  by_cases h : l ≤ x
  · simp only [h, and_self, ite_true]
    omega
  · simp only [h, false_and, ite_false, add_zero]
    omega

/-- the rounding that ends dep `l` keeps the bounds, and the dep is done -/
theorem acc_roundN (hp : 1 < p) {τ μ : ℕ → ℝ} {W Γ : ℝ} {k K : ℕ} (h : AccSet p n τ μ W Γ k K) {l : ℕ}
    (hl : l < n) {e : ℝ} {st : LState} (hok : st.ok) (hD : DInv p n n e st)
    (hB : AccB p n τ μ W Γ k (cMid n l n) (fun x => decide (x ≤ l)) st) :
    Inv p n (roundN p n e st) ∧
      AccB p n τ μ W Γ k (cAfter n (l + 1)) (fun x => decide (x < l + 1)) (roundN p n e st) := by
  have hinv := roundN_inv p n (DInv.toN p n hD)
  refine ⟨hinv, ?_⟩
  obtain ⟨⟨-, -, -, -, hsn', hin'⟩, -, -⟩ := hinv hok
  obtain ⟨b1, b2, b3, b4⟩ := hB
  have hu := u_pos p
  have hr : |RN p (st.s n + e) - (st.s n + e)| ≤ u p * |RN p (st.s n + e)| := abs_RN_sub_le_u_RN p _
  have hz : |RN p (st.s n + e)| ≤ st.adone n + prevOut st n + st.rA + |RN p (st.s n + e) - (st.s n + e)| := by
    have h2 := hin' n le_rfl
    rw [show prevOut (roundN p n e st) n = prevOut st n from rfl] at h2
    simp only [roundN, Function.update_self, ite_self, add_zero] at hsn' h2
    linarith
  have hc1 : n ≠ 0 → cMid n l n (n - 1) ≤ n := fun _ => by
    simp only [cMid, cAfter, show n - 1 < n by omega, ite_true]
    split_ifs <;> omega
  have hcn : cMid n l n n = l := by simp [cMid, cAfter]
  have hnew : |RN p (st.s n + e)| ≤ accS τ W Γ (u p) n k :=
    acc_core hz hr (AccSet.adone_le p n h _ n (b4 n le_rfl)) (prevOut_le p n h ⟨b1, b2, b3, b4⟩ n le_rfl hc1)
      (c := cMid n l n n) (by rw [hcn]; exact hl.le) b3
      (accG_le h.hτ h.W0 h.hΓ0 hu.le n k) (accS_split τ W Γ (u p) n k)
      (accS_nonneg h.hτ h.W0 h.hΓ0 hu.le n k) le_rfl h.hk h.hkK hu.le (u_lt_one p hp) h.hΓ
  refine ⟨fun x hx => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · rcases eq_or_ne x n with rfl | hxn
    · simpa [roundN] using hnew
    · simpa [roundN, Function.update_of_ne hxn] using b1 x hx
  · rw [← cMid_n_eq n hx]
    exact b2 x hx
  · show st.rA + |RN p (st.s n + e) - (st.s n + e)| ≤ _
    have : cAfter n (l + 1) n = cMid n l n n + 1 := by simp [cAfter, cMid]
    rw [this]
    push_cast
    nlinarith [hr, hnew]
  · have h4 := b4 x hx
    have hite : (if decide (x < l + 1) = true then μ k else 0) = (if decide (x ≤ l) = true then μ k else 0) := by
      by_cases h1 : x ≤ l
      · simp [h1, Nat.lt_succ_of_le h1]
      · simp [h1, show ¬x < l + 1 by omega]
    show st.adone x ≤ τ x * (∑ j ∈ Icc 1 (k - 1), μ j + if decide (x < l + 1) = true then μ k else 0)
    rw [hite]
    exact h4

omit [Prec_gt_0 p] in
/-- entering dep `l` puts `t_l` into level `l` -/
theorem acc_enter {τ μ : ℕ → ℝ} {W Γ : ℝ} {k : ℕ} {l : ℕ} (hl : l < n) {t : ℝ}
    (ht : F p t) (htb : |t| ≤ τ l * μ k) {st : LState} (hinv : Inv p n st)
    (hB : AccB p n τ μ W Γ k (cAfter n l) (fun x => decide (x < l)) st) :
    DInv p n l t (entering l t st) ∧ AccB p n τ μ W Γ k (cMid n l l) (fun x => decide (x ≤ l)) (entering l t st) := by
  refine ⟨entering_dinv p n ht hinv, ?_⟩
  obtain ⟨b1, b2, b3, b4⟩ := hB
  have hc : ∀ x, cMid n l l x = cAfter n l x := fun x => by simp [cMid]
  refine ⟨b1, fun x hx => by simpa [hc, entering] using b2 x hx, by simpa [hc, entering] using b3,
    fun x hx => ?_⟩
  have := b4 x hx
  rcases eq_or_ne x l with rfl | hxl
  · simp only [entering, Function.update_self, lt_irrefl, decide_false, Bool.false_eq_true, ite_false, add_zero,
      le_refl, decide_true, ite_true] at this ⊢
    rw [mul_add]
    linarith
  · simp only [entering, Function.update_of_ne hxl]
    have hiff : x ≤ l ↔ x < l := by omega
    simpa [hiff] using this

/-- the last rounding of a deposit with `N = n` puts `t_n` into level `n` -/
theorem acc_top (hp : 1 < p) {τ μ : ℕ → ℝ} {W Γ : ℝ} {k K : ℕ} (h : AccSet p n τ μ W Γ k K) {t : ℝ}
    (htb : |t| ≤ τ n * μ k) {st : LState} (hok : st.ok) (hinv : Inv p n st)
    (hB : AccB p n τ μ W Γ k (cAfter n n) (fun x => decide (x < n)) st) :
    Inv p n (roundN p n t (entering n t st)) ∧
      AccB p n τ μ W Γ k (fun x => if x < n then x + 1 else n + 1) (fun _ => true)
        (roundN p n t (entering n t st)) := by
  have hinv' := roundN_inv p n (entering_dinvN p n (y := t) hinv)
  refine ⟨hinv', ?_⟩
  obtain ⟨⟨-, -, -, -, hsn', hin'⟩, -, -⟩ := hinv' hok
  obtain ⟨b1, b2, b3, b4⟩ := hB
  have hu := u_pos p
  have hr : |RN p (st.s n + t) - (st.s n + t)| ≤ u p * |RN p (st.s n + t)| := abs_RN_sub_le_u_RN p (st.s n + t)
  have hz : |RN p (st.s n + t)| ≤ (st.adone n + |t|) + prevOut st n + st.rA + |RN p (st.s n + t) - (st.s n + t)| := by
    have h2 := hin' n le_rfl
    rw [show prevOut (roundN p n t (entering n t st)) n = prevOut st n from rfl] at h2
    simp only [roundN, entering, Function.update_self, ite_self, add_zero] at hsn' h2
    linarith
  have hA : st.adone n + |t| ≤ τ n * (∑ j ∈ Icc 1 (k - 1), μ j + if true then μ k else 0) := by
    have := b4 n le_rfl
    simp only [lt_irrefl, decide_false, Bool.false_eq_true, ite_false, add_zero, ite_true] at this ⊢
    nlinarith [h.hτ n]
  have hc1 : n ≠ 0 → cAfter n n (n - 1) ≤ n := fun _ => by simp [cAfter, show n - 1 < n by omega]
  have hcn : cAfter n n n = n := by simp [cAfter]
  have hnew : |RN p (st.s n + t)| ≤ accS τ W Γ (u p) n k :=
    acc_core hz hr (AccSet.adone_le p n h _ n hA) (prevOut_le p n h ⟨b1, b2, b3, b4⟩ n le_rfl hc1)
      (c := cAfter n n n) (by rw [hcn]) b3
      (accG_le h.hτ h.W0 h.hΓ0 hu.le n k) (accS_split τ W Γ (u p) n k)
      (accS_nonneg h.hτ h.W0 h.hΓ0 hu.le n k) le_rfl h.hk h.hkK hu.le (u_lt_one p hp) h.hΓ
  refine ⟨fun x hx => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · rcases eq_or_ne x n with rfl | hxn
    · simpa [roundN, entering] using hnew
    · simpa [roundN, entering, Function.update_of_ne hxn] using b1 x hx
  · have := b2 x hx
    simp only [cAfter, hx, ite_true, min_eq_right (show x + 1 ≤ n by omega)] at this
    simpa [roundN, entering, hx] using this
  · show st.rA + |RN p (st.s n + t) - (st.s n + t)| ≤ _
    simp only [lt_irrefl, ite_false]
    rw [hcn] at b3
    push_cast
    nlinarith [hr, hnew]
  · rcases eq_or_ne x n with rfl | hxn
    · simpa [roundN, entering] using hA
    · have := b4 x hx
      simp only [roundN, entering, Function.update_of_ne hxn]
      simpa [show x < n by omega] using this

omit [Prec_gt_0 p] in
/-- from the end of deposit `k` to the start of deposit `k + 1` -/
theorem acc_next {τ μ : ℕ → ℝ} {W Γ : ℝ} {k K : ℕ} (h : AccSet p n τ μ W Γ k K) {c : ℕ → ℕ} {r : ℕ → Bool}
    (hc : ∀ x < n, c x = x + 1) (hcn : c n ≤ n + 1) {st : LState}
    (hB : AccB p n τ μ W Γ k c r st) : AccB p n τ μ W Γ (k + 1) (cAfter n 0) (fun x => decide (x < 0)) st := by
  obtain ⟨b1, b2, b3, b4⟩ := hB
  have hu := u_pos p
  have hc0 : ∀ x, cAfter n 0 x = 0 := fun x => by simp [cAfter]
  refine ⟨fun x hx => (b1 x hx).trans (accS_mono h.hτ h.W0 h.hΓ0 hu.le x (Nat.le_succ k)), fun x hx => ?_, ?_,
    fun x hx => ?_⟩
  · rw [hc0, Nat.add_sub_cancel, accG_succ τ W Γ (u p) x k h.hk]
    have := b2 x hx
    rw [hc x hx] at this
    push_cast at this ⊢
    linarith
  · rw [hc0, Nat.add_sub_cancel, accG_succ τ W Γ (u p) n k h.hk]
    have hS := accS_nonneg h.hτ h.W0 h.hΓ0 hu.le n k
    have : (c n : ℝ) * u p * accS τ W Γ (u p) n k ≤ ((n : ℝ) + 1) * u p * accS τ W Γ (u p) n k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hcn) hu.le) hS
    push_cast
    linarith
  · have hsum : ∑ j ∈ Icc 1 k, μ j = ∑ j ∈ Icc 1 (k - 1), μ j + μ k := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := h.hk; omega⟩
      rw [sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    simp only [Nat.add_sub_cancel, Nat.not_lt_zero, decide_false, Bool.false_eq_true, ite_false, add_zero, hsum]
    refine (b4 x hx).trans (mul_le_mul_of_nonneg_left ?_ (h.hτ x))
    split_ifs <;> linarith [h.hμ k]

theorem acc_depRun (hp : 1 < p) {τ μ : ℕ → ℝ} {W Γ : ℝ} {k K : ℕ} (h : AccSet p n τ μ W Γ k K) {l : ℕ}
    (hl : l < n) : ∀ (j m : ℕ) (e : ℝ) (st : LState), m + j = n → l ≤ m → st.ok → DInv p n m e st →
      AccB p n τ μ W Γ k (cMid n l m) (fun x => decide (x ≤ l)) st →
      (∀ x ∈ (depRun p n j m e st).1, ∀ y ≤ n, |x.s y| ≤ accS τ W Γ (u p) y k) ∧
        Inv p n (depRun p n j m e st).2 ∧
        AccB p n τ μ W Γ k (cAfter n (l + 1)) (fun x => decide (x < l + 1)) (depRun p n j m e st).2 ∧
        (depRun p n j m e st).2.ok
  | 0, m, e, st, hmj, hlm, hok, hD, hB => by
    obtain rfl : m = n := by omega
    obtain ⟨h1, h2⟩ := acc_roundN p m hp h hl hok hD hB
    refine ⟨fun x hx y hy => ?_, h1, h2, hok⟩
    simp only [depRun, List.mem_singleton] at hx
    subst hx
    exact h2.1 y hy
  | j + 1, m, e, st, hmj, hlm, hok, hD, hB => by
    obtain ⟨h1, h2⟩ := acc_twoAt p n hp h hlm (by omega) hok hD hB
    obtain ⟨i1, i2, i3, i4⟩ := acc_depRun hp h hl j (m + 1) _ (twoAt p m e st) (by omega) (by omega) hok h1 h2
    refine ⟨fun x hx y hy => ?_, i2, i3, i4⟩
    simp only [depRun, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h2.1 y hy
    · exact i1 x hx y hy

/-- the deps `0, …, l - 1` of a deposit -/
theorem acc_deps (hp : 1 < p) {τ μ : ℕ → ℝ} {W Γ : ℝ} {k K : ℕ} (h : AccSet p n τ μ W Γ k K) (t : ℕ → ℝ)
    (ht : ∀ l < n, F p (t l) ∧ |t l| ≤ τ l * μ k) : ∀ l ≤ n, ∀ st : LState, st.ok → Inv p n st →
      AccB p n τ μ W Γ k (cAfter n 0) (fun x => decide (x < 0)) st →
      (∀ x ∈ (runOps p n ((List.range l).map fun i => LOp.dep i (t i)) st).1, ∀ y ≤ n,
          |x.s y| ≤ accS τ W Γ (u p) y k) ∧
        Inv p n (runOps p n ((List.range l).map fun i => LOp.dep i (t i)) st).2 ∧
        AccB p n τ μ W Γ k (cAfter n l) (fun x => decide (x < l))
          (runOps p n ((List.range l).map fun i => LOp.dep i (t i)) st).2 ∧
        (runOps p n ((List.range l).map fun i => LOp.dep i (t i)) st).2.ok := by
  intro l
  induction l with
  | zero => intro _ st hok hinv hB; exact ⟨by simp [runOps], hinv, hB, hok⟩
  | succ l ih =>
    intro hl st hok hinv hB
    obtain ⟨i1, i2, i3, i4⟩ := ih (by omega) st hok hinv hB
    rw [List.range_succ, List.map_append, (runOps_append p n _ _ _).1, (runOps_append p n _ _ _).2]
    set st1 := (runOps p n ((List.range l).map fun i => LOp.dep i (t i)) st).2
    obtain ⟨e1, e2⟩ := acc_enter p n (hl := (by omega : l < n)) (ht l (by omega)).1 (ht l (by omega)).2 i2 i3
    obtain ⟨d1, d2, d3, d4⟩ := acc_depRun p n hp h (by omega : l < n) (n - l) l (t l) (entering l (t l) st1)
      (by omega) le_rfl i4 e1 e2
    simp only [List.map_cons, List.map_nil, runOps, stepOp_dep, List.append_nil]
    refine ⟨fun x hx y hy => ?_, d2, d3, d4⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact i1 x hx y hy
    · exact d1 x hx y hy

omit [Prec_gt_0 p] in
/-- the initial levels satisfy the bounds of deposit `1` -/
theorem acc_init {τ μ : ℕ → ℝ} {W Γ : ℝ} (hτ : ∀ l, 0 ≤ τ l) (hW : 0 ≤ W) (hΓ0 : 0 ≤ Γ) :
    AccB p n τ μ W Γ 1 (cAfter n 0) (fun x => decide (x < 0)) LState.init := by
  have hu := u_pos p
  refine ⟨fun x _ => by simpa [LState.init] using accS_nonneg hτ hW hΓ0 hu.le x 1,
    fun x _ => by simp [LState.init, accG, cAfter], by simp [LState.init, accG, cAfter], fun x _ => by
      simp [LState.init]⟩

/-- one deposit, from the start of deposit `k` to the start of deposit `k + 1` -/
theorem acc_deposit (hp : 1 < p) {τ μ : ℕ → ℝ} {W Γ : ℝ} {k K : ℕ} (h : AccSet p n τ μ W Γ k K) (t : ℕ → ℝ)
    (top : Bool) (ht : ∀ l < n, F p (t l) ∧ |t l| ≤ τ l * μ k) (htop : top = true → |t n| ≤ τ n * μ k)
    (st : LState) (hok : st.ok) (hinv : Inv p n st)
    (hB : AccB p n τ μ W Γ k (cAfter n 0) (fun x => decide (x < 0)) st) :
    (∀ x ∈ (runOps p n (depositOps n t top) st).1, ∀ y ≤ n, |x.s y| ≤ accS τ W Γ (u p) y k) ∧
      Inv p n (runOps p n (depositOps n t top) st).2 ∧
      AccB p n τ μ W Γ (k + 1) (cAfter n 0) (fun x => decide (x < 0)) (runOps p n (depositOps n t top) st).2 ∧
      (runOps p n (depositOps n t top) st).2.ok := by
  obtain ⟨i1, i2, i3, i4⟩ := acc_deps p n hp h t ht n le_rfl st hok hinv hB
  unfold depositOps
  rw [(runOps_append p n _ _ _).1, (runOps_append p n _ _ _).2]
  set st1 := (runOps p n ((List.range n).map fun i => LOp.dep i (t i)) st).2
  cases top with
  | false =>
    simp only [Bool.false_eq_true, ite_false, runOps, List.append_nil]
    refine ⟨i1, i2, acc_next p n h (c := cAfter n n) (fun x hx => by simp [cAfter, hx])
      (by simp [cAfter]) i3, i4⟩
  | true =>
    obtain ⟨a1, a2⟩ := acc_top p n hp h (htop rfl) i4 i2 i3
    simp only [ite_true, runOps, stepOp, List.append_nil]
    refine ⟨fun x hx y hy => ?_, a1, acc_next p n h (fun x hx => by simp [hx]) (by simp) a2, i4⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact i1 x hx y hy
    · simp only [List.mem_singleton] at hx
      subst hx
      exact a2.1 y hy

theorem accOps_succ (t : ℕ → ℕ → ℝ) (top : ℕ → Bool) (k : ℕ) :
    accOps n t top (k + 1) = accOps n t top k ++ depositOps n (t (k + 1)) (top (k + 1)) := by
  simp [accOps, List.range_succ, List.flatMap_append]

/-- the first `k` deposits -/
theorem acc_run (hp : 1 < p) (t : ℕ → ℕ → ℝ) (top : ℕ → Bool) {τ μ : ℕ → ℝ} {W Γ : ℝ} (K : ℕ)
    (hset : ∀ k, 1 ≤ k → k ≤ K → AccSet p n τ μ W Γ k K) (hτ : ∀ l, 0 ≤ τ l) (hW : 0 ≤ W) (hΓ0 : 0 ≤ Γ)
    (ht : ∀ k ∈ Icc 1 K, ∀ l < n, F p (t k l) ∧ |t k l| ≤ τ l * μ k)
    (htop : ∀ k ∈ Icc 1 K, top k = true → |t k n| ≤ τ n * μ k) : ∀ k ≤ K,
      (∀ x ∈ LState.init :: (runOps p n (accOps n t top k) LState.init).1, ∀ y ≤ n,
          |x.s y| ≤ accS τ W Γ (u p) y k) ∧
        Inv p n (runOps p n (accOps n t top k) LState.init).2 ∧
        AccB p n τ μ W Γ (k + 1) (cAfter n 0) (fun x => decide (x < 0)) (runOps p n (accOps n t top k) LState.init).2 ∧
        (runOps p n (accOps n t top k) LState.init).2.ok := by
  have hu := u_pos p
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun x hx y _ => ?_, init_inv p n, acc_init p n hτ hW hΓ0, trivial⟩
    simp only [accOps, List.range_zero, List.flatMap_nil, runOps, List.mem_singleton] at hx
    subst hx
    simpa [LState.init] using accS_nonneg hτ hW hΓ0 hu.le y 0
  | succ k ih =>
    intro hk
    obtain ⟨i1, i2, i3, i4⟩ := ih (by omega)
    have hk1 : k + 1 ∈ Icc 1 K := by simp; omega
    obtain ⟨d1, d2, d3, d4⟩ := acc_deposit p n hp (hset (k + 1) (by omega) hk) (t (k + 1)) (top (k + 1))
      (ht _ hk1) (htop _ hk1) _ i4 i2 i3
    rw [accOps_succ, (runOps_append p n _ _ _).1, (runOps_append p n _ _ _).2]
    refine ⟨fun x hx y hy => ?_, d2, d3, d4⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (i1 _ (List.mem_cons_self) y hy).trans (accS_mono hτ hW hΓ0 hu.le y (Nat.le_succ k))
    rcases List.mem_append.mp hx with hx | hx
    · exact (i1 x (List.mem_cons_of_mem _ hx) y hy).trans (accS_mono hτ hW hΓ0 hu.le y (Nat.le_succ k))
    · exact d1 x hx y hy

omit [Prec_gt_0 p] in
theorem accOps_wf (t : ℕ → ℕ → ℝ) (top : ℕ → Bool) (K : ℕ) (ht : ∀ k ∈ Icc 1 K, ∀ l < n, F p (t k l)) :
    ∀ o ∈ accOps n t top K, o.wf p n := by
  intro o ho
  simp only [accOps, depositOps, List.mem_flatMap, List.mem_range, List.mem_append, List.mem_map] at ho
  obtain ⟨j, hj, ho⟩ := ho
  rcases ho with ⟨l, hl, rfl⟩ | ho
  · exact ⟨hl.le, ht (j + 1) (by simp; omega) l hl⟩
  · split_ifs at ho
    · simp only [List.mem_singleton] at ho
      subst ho
      trivial
    · simp at ho

theorem accOps_Y (t : ℕ → ℕ → ℝ) (top : ℕ → Bool) (K : ℕ) :
    opsY (accOps n t top K) = ∑ k ∈ Icc 1 K, (∑ l ∈ range n, t k l + if top k then t k n else 0) := by
  induction K with
  | zero => simp [accOps, opsY]
  | succ K ih =>
    rw [accOps_succ, sum_Icc_succ_top (by omega), ← ih]
    simp only [opsY, List.map_append, List.sum_append]
    congr 1
    simp only [depositOps, List.map_append, List.sum_append, List.map_map, Function.comp_def, opY,
      list_sum_map_range]
    split_ifs <;> simp [opY]

/-- Lemma `lem:acc`. `K` deposits are made into zero levels, the `k`-th with `|t_l^{(k)}| ≤ τ_l μ_k` for `l < n`
and, where `N = n`, for `t_n`; `W = ∑ μ_k`, `(n + 1)Ku < 1` and `Γ = 1/(1 - (n + 1)Ku)`. (a) At every moment up
to the end of the `k`-th deposit, `|s_m| ≤ S_m(k)`. (b) At the end, `∑ s_m = ∑_{k,l} t_l^{(k)} - E_lev` with
`|E_lev| ≤ Ē_lev`. -/
theorem lemma_acc (hp : 1 < p) (t : ℕ → ℕ → ℝ) (top : ℕ → Bool) (K : ℕ) (τ μ : ℕ → ℝ) (hτ : ∀ l, 0 ≤ τ l)
    (hμ : ∀ k, 0 ≤ μ k) (ht : ∀ k ∈ Icc 1 K, ∀ l < n, F p (t k l) ∧ |t k l| ≤ τ l * μ k)
    (htop : ∀ k ∈ Icc 1 K, top k = true → |t k n| ≤ τ n * μ k) (hK : ((n : ℝ) + 1) * K * u p < 1) :
    (∀ k ∈ Icc 1 K, ∀ x ∈ LState.init :: (runOps p n (accOps n t top k) LState.init).1, ∀ m ≤ n,
        |x.s m| ≤ accSclosed τ (∑ j ∈ Icc 1 K, μ j) (1 / (1 - ((n : ℝ) + 1) * K * u p)) (u p) m k) ∧
      ∑ m ∈ range (n + 1), (runOps p n (accOps n t top K) LState.init).2.s m =
        ∑ k ∈ Icc 1 K, (∑ l ∈ range n, t k l + if top k then t k n else 0) -
          (runOps p n (accOps n t top K) LState.init).2.rS ∧
      |(runOps p n (accOps n t top K) LState.init).2.rS| ≤
        accE τ (∑ j ∈ Icc 1 K, μ j) (1 / (1 - ((n : ℝ) + 1) * K * u p)) (u p) n K := by
  have hu := u_pos p
  set W := ∑ j ∈ Icc 1 K, μ j with hWdef
  set Γ := 1 / (1 - ((n : ℝ) + 1) * K * u p) with hΓdef
  have h1X : 0 < 1 - ((n : ℝ) + 1) * K * u p := by linarith
  have hΓ0 : 0 ≤ Γ := by rw [hΓdef]; positivity
  have hΓ : Γ * (1 - ((n : ℝ) + 1) * K * u p) = 1 := by rw [hΓdef]; field_simp
  have hW : 0 ≤ W := sum_nonneg fun j _ => hμ j
  have hset : ∀ k, 1 ≤ k → k ≤ K → AccSet p n τ μ W Γ k K := fun k hk hkK =>
    ⟨hτ, hμ, hk, hkK, hΓ0, hΓ, sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hkK) fun j _ _ => hμ j⟩
  have hrun := acc_run p n hp t top K hset hτ hW hΓ0 ht htop
  obtain ⟨-, r2, r3, r4⟩ := hrun K le_rfl
  refine ⟨fun k hk x hx m hm => ?_, ?_, ?_⟩
  · rw [← accS_eq]
    exact (hrun k (mem_Icc.mp hk).2).1 x hx m hm
  · obtain ⟨-, -, hsum⟩ := r2 r4
    obtain ⟨-, -, -, hY⟩ := runOps_tot p n _ LState.init (accOps_wf p n t top K fun k hk l hl => (ht k hk l hl).1)
    rw [hsum, hY, accOps_Y]
    simp [LState.init]
  · have hr := runOps_rS p n (accOps n t top K) LState.init (by simp [LState.init])
    refine hr.trans (r3.2.2.1.trans (le_of_eq ?_))
    rw [accE_eq, Nat.add_sub_cancel]
    simp [cAfter, accG]

end ExpansionBounds
