import ExpansionBounds.ExpCore

/-!
# Theorems 14 and 15: the bounds on `H(θ)`

An `n`-part `a` satisfies `H(θ)` when `|a_i| ≤ ρ^i |a_0|` for `1 ≤ i ≤ n - 1`, with `ρ = θu`. Lemma 13's bounds, taken
at the part bounds `ρ^i |a_0|` and `ρ^j |b_0|`, have the closed forms of Theorem 14: the inputs of level `m` total
`Â_m ρ^m M`, Lemma 11's `D_m` is `d_m ρ^m M`, and its `X_m` is `L_m u^m M`. Theorem 15 adds Theorem 9 (e). The
theorems hold for any `θ > 0`; the paper's `1 ≤ θ ≤ 1/(4u)` enters only through `(eq:a0)`, which needs `2ρ < 1`.
-/

namespace ExpansionBounds

open Finset

/-- the pairs `(i, j)` with `i, j < n` and `i + j = m`: `m + 1` for `m < n` and `2n - 1 - m` otherwise -/
def pairCnt (n m : ℕ) : ℕ := if m < n then m + 1 else 2 * n - 1 - m

theorem pairCnt_eq (n m : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, (if i + j = m then (1 : ℝ) else 0) = (pairCnt n m : ℝ) := by
  have h1 : ∀ i ∈ range n, ∑ j ∈ range n, (if i + j = m then (1 : ℝ) else 0) =
      if i ∈ Ico (m + 1 - n) (min (m + 1) n) then 1 else 0 := by
    intro i hi
    rw [mem_range] at hi
    by_cases h : i ≤ m ∧ m - i < n
    · have hc : i ∈ Ico (m + 1 - n) (min (m + 1) n) := by rw [mem_Ico]; omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true hc), sum_eq_single (m - i)]
      · simp only [show i + (m - i) = m by omega, ite_true]
      · intro j _ hj
        simp only [show i + j ≠ m by omega, ite_false]
      · intro hj
        rw [mem_range] at hj
        omega
    · have hc : i ∉ Ico (m + 1 - n) (min (m + 1) n) := by rw [mem_Ico]; omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      exact sum_eq_zero fun j hj => by
        rw [mem_range] at hj
        simp only [show i + j ≠ m by omega, ite_false]
  rw [sum_congr rfl h1, sum_ite_mem, show range n ∩ Ico (m + 1 - n) (min (m + 1) n) = Ico (m + 1 - n) (min (m + 1) n) by
    ext i; simp only [mem_inter, mem_range, mem_Ico]; omega]
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  congr 1
  unfold pairCnt
  split_ifs <;> omega

variable (p : ℤ) (n : ℕ)

/-- `H(θ)`: `|a_i| ≤ ρ^i |a_0|` for `1 ≤ i ≤ n - 1`, with `ρ = θu` -/
def Htheta (θ : ℝ) (a : ℕ → ℝ) : Prop := ∀ i, 1 ≤ i → i < n → |a i| ≤ (θ * u p) ^ i * |a 0|

theorem Htheta_le {θ : ℝ} {a : ℕ → ℝ} (h : Htheta p n θ a) : ∀ i < n, |a i| ≤ (θ * u p) ^ i * |a 0| := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  · exact h i hi0 hi

theorem mulP_geom (ρ x y : ℝ) (m : ℕ) :
    mulP n (fun i => ρ ^ i * x) (fun j => ρ ^ j * y) m = pairCnt n m * ρ ^ m * (x * y) := by
  unfold mulP
  have h : ∀ i ∈ range n, ∑ j ∈ range n, (if i + j = m then ρ ^ i * x * (ρ ^ j * y) else 0) =
      ρ ^ m * (x * y) * ∑ j ∈ range n, (if i + j = m then (1 : ℝ) else 0) := fun i _ => by
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · rw [← hij, pow_add]; ring
    · ring
  rw [sum_congr rfl h, ← mul_sum, pairCnt_eq]
  ring

/-- `Â_m` for MUL: `(1 + u)(m + 1) + m/θ` for `m < n` and `n - 1 + n/θ` for `m = n` -/
noncomputable def hatAmul (θ : ℝ) (m : ℕ) : ℝ :=
  if m < n then (1 + u p) * (m + 1) + m / θ else if m = n then (n - 1 : ℝ) + n / θ else 0

/-- `Â_m` for ADD and MULF: `1 + u` for `m = 0`, `1 + u + 1/θ` for `0 < m < n` and `1/θ` for `m = n` -/
noncomputable def hatApair (θ : ℝ) (m : ℕ) : ℝ :=
  if m < n then 1 + u p + (if m = 0 then 0 else 1 / θ) else if m = n then 1 / θ else 0

theorem mulA_geom (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 < θ) (x y : ℝ) (m : ℕ) :
    mulA p n (fun i => (θ * u p) ^ i * x) (fun j => (θ * u p) ^ j * y) m =
      hatAmul p n θ m * (θ * u p) ^ m * (x * y) := by
  unfold mulA hatAmul
  simp only [mulP_geom]
  rcases lt_trichotomy m n with hm | hm | hm
  · simp only [hm, ite_true]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp [pairCnt, show 0 < n by omega]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [show k + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel, pairCnt, show k < n by omega,
        show k + 1 < n by omega, ite_true]
      field_simp
      push_cast
      ring
  · rw [hm]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [lt_irrefl, ite_false, ite_true, pairCnt, Nat.add_sub_cancel, show k < k + 1 by omega,
      show 2 * (k + 1) - 1 - (k + 1) = k by omega]
    rw [pow_succ]
    field_simp
    push_cast
    ring
  · simp only [show ¬m < n by omega, show m ≠ n by omega, ite_false, zero_mul]

theorem pairA_geom (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 < θ) (M : ℝ) (m : ℕ) :
    pairA p n (fun k => (θ * u p) ^ k * M) m = hatApair p n θ m * (θ * u p) ^ m * M := by
  unfold pairA hatApair
  rcases lt_trichotomy m n with hm | hm | hm
  · simp only [hm, ite_true]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [show k + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
      rw [pow_succ]
      field_simp
      try ring
  · rw [hm]
    simp only [lt_irrefl, ite_false, ite_true]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    field_simp
    try ring
  · simp only [show ¬m < n by omega, show m ≠ n by omega, ite_false, zero_mul]

/-- `d_0 = Â_0` and `d_{m+1} = Â_{m+1} + γ_m`, with `γ_m = T_m d_m / (θ(1 - T_m u))` -/
noncomputable def thmD (Ah : ℕ → ℝ) (T : ℕ → ℕ) (θ : ℝ) : ℕ → ℝ
  | 0 => Ah 0
  | m + 1 => Ah (m + 1) + T m * thmD Ah T θ m / (θ * (1 - T m * u p))

/-- `L_m = θ^m d_m / (1 - T_m u)` for `m < n` and `L_n = θ^n d_n / (1 - Qu)` -/
noncomputable def thmL (Ah : ℕ → ℝ) (T : ℕ → ℕ) (θ : ℝ) (Q : ℕ) (m : ℕ) : ℝ :=
  if m < n then θ ^ m * thmD p Ah T θ m / (1 - T m * u p) else θ ^ n * thmD p Ah T θ n / (1 - Q * u p)

/-- Lemma 11's `D_m` on inputs `Â_m ρ^m M` is `d_m ρ^m M` -/
theorem levD_geom (Ah : ℕ → ℝ) (T : ℕ → ℕ) (θ : ℝ) (hθ : 0 < θ) (M : ℝ) :
    ∀ m, levD (fun k => Ah k * (θ * u p) ^ k * M) T (u p) m = thmD p Ah T θ m * (θ * u p) ^ m * M := by
  intro m
  induction m with
  | zero => simp [levD, thmD]
  | succ m ih =>
    simp only [levD, thmD]
    rw [ih]
    have hρ : (θ * u p) ^ (m + 1) = θ * (u p * (θ * u p) ^ m) := by ring
    rw [hρ]
    field_simp

/-- `Δ_n = ∑_{k=n+1}^{2n-1} (2n - 1 - k) θ^k u^{k-n-1}`, the paper's sum with its zero last term -/
noncomputable def thmDelta (θ : ℝ) : ℝ :=
  ∑ k ∈ Ico (n + 1) (2 * n), ((2 * n - 1 - k : ℕ) : ℝ) * θ ^ k * u p ^ (k - n - 1)

theorem mulDelta_geom (θ x y : ℝ) :
    mulDelta n (fun i => (θ * u p) ^ i * x) (fun j => (θ * u p) ^ j * y) =
      thmDelta p n θ * u p ^ (n + 1) * (x * y) := by
  rw [mulDelta_eq, thmDelta, sum_mul, sum_mul]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_Ico] at hk
  rw [mulP_geom, pairCnt, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), mul_pow]
  rw [show u p ^ k = u p ^ (k - n - 1) * u p ^ (n + 1) by rw [← pow_add]; congr 1; omega]
  ring

/-- MUL's `L_m`: `Â_m` of MUL, `T_m = m(m + 1)` and `Q = n² + n - 1` -/
noncomputable def mulL (θ : ℝ) (m : ℕ) : ℝ := thmL p n (hatAmul p n θ) mulT θ (n ^ 2 + n - 1) m

/-- ADD's and MULF's `L_m`: `T_m = m` and `Q = n - 1` -/
noncomputable def pairL (θ : ℝ) (m : ℕ) : ℝ := thmL p n (hatApair p n θ) id θ (n - 1) m

theorem mulX_geom (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 < θ) (x y : ℝ) (m : ℕ) (hm : m ≤ n) :
    mulX p n (fun i => (θ * u p) ^ i * x) (fun j => (θ * u p) ^ j * y) m = mulL p n θ m * u p ^ m * (x * y) := by
  have hA : mulA p n (fun i => (θ * u p) ^ i * x) (fun j => (θ * u p) ^ j * y) =
      fun k => hatAmul p n θ k * (θ * u p) ^ k * (x * y) := funext (mulA_geom p n hn θ hθ x y)
  unfold mulX levX mulL thmL
  rw [hA, levD_geom p _ _ θ hθ, levD_geom p _ _ θ hθ]
  split_ifs with h
  · rw [mul_pow]; ring
  · obtain rfl : m = n := by omega
    rw [mul_pow]; ring

theorem pairX_geom (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 < θ) (M : ℝ) (m : ℕ) (hm : m ≤ n) :
    pairX p n (fun k => (θ * u p) ^ k * M) m = pairL p n θ m * u p ^ m * M := by
  have hA : pairA p n (fun k => (θ * u p) ^ k * M) = fun k => hatApair p n θ k * (θ * u p) ^ k * M :=
    funext (pairA_geom p n hn θ hθ M)
  unfold pairX levX pairL thmL
  rw [hA, levD_geom p _ _ θ hθ, levD_geom p _ _ θ hθ]
  split_ifs with h
  · rw [mul_pow]; ring
  · obtain rfl : m = n := by omega
    rw [mul_pow]; ring

/-- ADDF's `L_m`: `(1 + u) ∑_{k ≤ m} θ^k` for `m < n` and `∑_{k < n} θ^k` for `m = n` -/
noncomputable def addfL (θ : ℝ) (m : ℕ) : ℝ :=
  if m < n then (1 + u p) * ∑ k ∈ range (m + 1), θ ^ k else ∑ k ∈ range n, θ ^ k

theorem addfEps_geom (θ : ℝ) (hθ : 0 ≤ θ) (x M : ℝ) (hxM : x ≤ M) :
    ∀ i, addfEps p (fun k => (θ * u p) ^ k * x) M i ≤ u p ^ (i + 1) * M * ∑ k ∈ range (i + 1), θ ^ k := by
  have hu := u_pos p
  intro i
  induction i with
  | zero => simp [addfEps]
  | succ i ih =>
    simp only [addfEps]
    have h1 : (θ * u p) ^ (i + 1) * x ≤ θ ^ (i + 1) * u p ^ (i + 1) * M := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hxM (by positivity)
    calc u p * ((θ * u p) ^ (i + 1) * x + addfEps p (fun k => (θ * u p) ^ k * x) M i)
        ≤ u p * (θ ^ (i + 1) * u p ^ (i + 1) * M + u p ^ (i + 1) * M * ∑ k ∈ range (i + 1), θ ^ k) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 ih) hu.le
      _ = u p ^ (i + 1 + 1) * M * ∑ k ∈ range (i + 1 + 1), θ ^ k := by rw [sum_range_succ _ (i + 1)]; ring

theorem addfX_geom (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 ≤ θ) (x M : ℝ) (hxM : x ≤ M) (m : ℕ) (hm : m ≤ n) :
    addfX p n (fun k => (θ * u p) ^ k * x) M m ≤ addfL p n θ m * u p ^ m * M := by
  have hu := u_pos p
  have he := addfEps_geom p θ hθ x M hxM
  unfold addfX addfL
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp [show 0 < n by omega]
  rcases Nat.lt_or_ge m n with hlt | hge
  · simp only [show m ≠ 0 by omega, hlt, ite_false, ite_true]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have h1 : (θ * u p) ^ (k + 1) * x ≤ θ ^ (k + 1) * u p ^ (k + 1) * M := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hxM (by positivity)
    calc (1 + u p) * ((θ * u p) ^ (k + 1) * x + addfEps p (fun k => (θ * u p) ^ k * x) M k)
        ≤ (1 + u p) * (θ ^ (k + 1) * u p ^ (k + 1) * M + u p ^ (k + 1) * M * ∑ j ∈ range (k + 1), θ ^ j) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 (he k)) (by linarith)
      _ = _ := by rw [sum_range_succ _ (k + 1)]; ring
  · obtain rfl : m = n := by omega
    simp only [show m ≠ 0 by omega, lt_irrefl, ite_false, ite_true]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact (he k).trans_eq (by ring)

variable [Prec_gt_0 p]

/-- Theorem 14 (`thm:t2`) for MUL: on `H(θ)` operands, with `M = |a_0 b_0|`, the levels stay within `L_m u^m M` at
every moment and the final ones sum to within `(R_n + Δ_n) u^{n+1} M` of `ab`, with `R_n = QL_n`; there are
`T_m = m(m + 1)` `TwoSum`s at level `m` and `Q = n² + n - 1` roundings at level `n` -/
theorem thm14_mul (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (θ : ℝ) (hθ : 0 < θ)
    (a b : ℕ → ℝ) (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j)) (hHa : Htheta p n θ a)
    (hHb : Htheta p n θ b) :
    (∀ x ∈ LState.init :: (runOps p n (mulOps p n a b) LState.init).1, ∀ m ≤ n,
        |x.s m| ≤ mulL p n θ m * u p ^ m * |a 0 * b 0|) ∧
      |(∑ i ∈ range n, a i) * (∑ j ∈ range n, b j) -
          ∑ m ∈ range (n + 1), (runOps p n (mulOps p n a b) LState.init).2.s m| ≤
        (((n ^ 2 + n - 1 : ℕ) : ℝ) * mulL p n θ n + thmDelta p n θ) * u p ^ (n + 1) * |a 0 * b 0| ∧
      (∀ m < n, opsT (mulOps p n a b) m = m * (m + 1)) ∧ opsQ (mulOps p n a b) = n ^ 2 + n - 1 := by
  obtain ⟨c1, c2, c3, c4, -⟩ := mulOps_levels p n hp hn a b (fun i => (θ * u p) ^ i * |a 0|)
    (fun j => (θ * u p) ^ j * |b 0|) ha hb (Htheta_le p n hHa) (Htheta_le p n hHb) hA3
  have hX : ∀ m ≤ n, mulX p n (fun i => (θ * u p) ^ i * |a 0|) (fun j => (θ * u p) ^ j * |b 0|) m =
      mulL p n θ m * u p ^ m * |a 0 * b 0| := fun m hm => by rw [mulX_geom p n hn θ hθ _ _ m hm, abs_mul]
  refine ⟨fun x hx m hm => (c1 x hx m hm).trans_eq (hX m hm), ?_, c3, c4⟩
  rw [sum_mul_sum]
  refine c2.trans_eq ?_
  rw [mulR, hX n le_rfl, mulDelta_geom, abs_mul]
  ring

/-- Theorem 14 for ADD: with `M = |a_0| + |b_0|`, `T_m = m` and `Q = n - 1` -/
theorem thm14_add (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (θ : ℝ) (hθ : 0 < θ)
    (a b : ℕ → ℝ) (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j)) (hHa : Htheta p n θ a)
    (hHb : Htheta p n θ b) :
    (∀ x ∈ LState.init :: (runOps p n (addOps p n a b) LState.init).1, ∀ m ≤ n,
        |x.s m| ≤ pairL p n θ m * u p ^ m * (|a 0| + |b 0|)) ∧
      |(∑ i ∈ range n, a i + ∑ i ∈ range n, b i) - ∑ m ∈ range (n + 1), addLevels p n a b m| ≤
        ((n - 1 : ℕ) : ℝ) * pairL p n θ n * u p ^ (n + 1) * (|a 0| + |b 0|) ∧
      (∀ m < n, opsT (addOps p n a b) m = m) ∧ opsQ (addOps p n a b) = n - 1 := by
  have hlam : ∀ m < n, |a m + b m| ≤ (θ * u p) ^ m * (|a 0| + |b 0|) := fun m hm => by
    rw [mul_add]
    exact (abs_add_le _ _).trans (add_le_add (Htheta_le p n hHa m hm) (Htheta_le p n hHb m hm))
  obtain ⟨-, -, -, c1, c2, c3, c4⟩ := lemma13_add p n hp hn a b ha hb _ hlam hA3 _ le_rfl
  have hX : ∀ m ≤ n, pairX p n (fun k => (θ * u p) ^ k * (|a 0| + |b 0|)) m =
      pairL p n θ m * u p ^ m * (|a 0| + |b 0|) := fun m hm => pairX_geom p n hn θ hθ _ m hm
  refine ⟨fun x hx m hm => (c1 x hx m hm).trans_eq (hX m hm), ?_, c3, c4⟩
  rw [← sum_add_distrib]
  refine c2.trans_eq ?_
  rw [pairR, hX n le_rfl]
  ring

/-- Theorem 14 for MULF: with `M = |a_0 b|`, `T_m = m` and `Q = n - 1` -/
theorem thm14_mulf (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (θ : ℝ) (hθ : 0 < θ)
    (a : ℕ → ℝ) (b : ℝ) (ha : ∀ i < n, F p (a i)) (hb : F p b) (hHa : Htheta p n θ a) :
    (∀ x ∈ LState.init :: (runOps p n (mulfOps p n a b) LState.init).1, ∀ m ≤ n,
        |x.s m| ≤ pairL p n θ m * u p ^ m * |a 0 * b|) ∧
      |(∑ i ∈ range n, a i) * b - ∑ m ∈ range (n + 1), mulfLevels p n a b m| ≤
        ((n - 1 : ℕ) : ℝ) * pairL p n θ n * u p ^ (n + 1) * |a 0 * b| ∧
      (∀ m < n, opsT (mulfOps p n a b) m = m) ∧ opsQ (mulfOps p n a b) = n - 1 := by
  obtain ⟨-, -, -, c1, c2, c3, c4⟩ := lemma13_mulf p n hp hn a b ha hb (fun i => (θ * u p) ^ i * |a 0|) |b|
    (Htheta_le p n hHa) le_rfl hA3 _ le_rfl
  have hlam : (fun m => (θ * u p) ^ m * |a 0| * |b|) = fun k => (θ * u p) ^ k * |a 0 * b| :=
    funext fun m => by rw [abs_mul]; ring
  have hX : ∀ m ≤ n, pairX p n (fun k => (θ * u p) ^ k * |a 0 * b|) m = pairL p n θ m * u p ^ m * |a 0 * b| :=
    fun m hm => pairX_geom p n hn θ hθ _ m hm
  rw [hlam] at c1 c2
  refine ⟨fun x hx m hm => (c1 x hx m hm).trans_eq (hX m hm), ?_, c3, c4⟩
  rw [sum_mul]
  refine c2.trans_eq ?_
  rw [pairR, hX n le_rfl]
  ring

/-- Theorem 14 for ADDF: with `M = |a_0| + |b|`, the levels sum exactly to `a + b` and `|c_m| ≤ L_m u^m M` -/
theorem thm14_addf (hp : 1 < p) (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 < θ) (a : ℕ → ℝ) (b : ℝ) (ha : ∀ i < n, F p (a i))
    (hb : F p b) (hHa : Htheta p n θ a) :
    (∀ m ≤ n, |addfLevels p n a b m| ≤ addfL p n θ m * u p ^ m * (|a 0| + |b|)) ∧
      ∑ m ∈ range (n + 1), addfLevels p n a b m = ∑ i ∈ range n, a i + b := by
  have hlam : |a 0 + b| ≤ |a 0| + |b| := abs_add_le _ _
  obtain ⟨-, -, -, c4, c5⟩ := lemma13_addf p hp hn a b ha hb (fun i => (θ * u p) ^ i * |a 0|) (Htheta_le p n hHa)
    _ hlam _ le_rfl
  refine ⟨fun m hm => (c4 m hm).trans (addfX_geom p n hn θ hθ.le _ _ ?_ m hm), c5⟩
  linarith [abs_nonneg b]

/-- Theorem 9 (e) after levels within `F_b u^{n+1} M` of `Z`: `|Z - ∑ Ren_n(c)| ≤ u^n|Z| + (κ_0 Λ + (1 + u^n)F_b)
u^{n+1} M`, with `κ_0 = 2(1 + u)^{n-1}/(1 - u)` and `Λ = ∑ L_m` -/
theorem ren_closed (hp : 1 < p) (hn : 1 ≤ n) (c : ℕ → ℝ) (hc : ∀ i ≤ n, F p (c i)) (L : ℕ → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hL : ∀ m ≤ n, |c m| ≤ L m * u p ^ m * M) (Z Fb : ℝ)
    (hZ : |Z - ∑ m ∈ range (n + 1), c m| ≤ Fb * u p ^ (n + 1) * M) :
    |Z - (ren p n n c).sum| ≤ u p ^ n * |Z| +
      (2 * (1 + u p) ^ (n - 1) / (1 - u p) * ∑ m ∈ range (n + 1), L m + (1 + u p ^ n) * Fb) * u p ^ (n + 1) * M := by
  have hu := u_pos p
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ m ∈ range (n + 1), c m := ⟨_, rfl⟩
  rw [← hS] at hZ
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * (1 + u p) ^ (n - 1) / (1 - u p) * (∑ m ∈ range (n + 1), L m) * u p ^ (n + 1) * M :=
    ⟨_, rfl⟩
  have hE : |S - (ren p n n c).sum| ≤ u p ^ n * |S| + K := by
    rcases eq_or_lt_of_le hM with h0 | hpos
    · have h := renErr_le_scaled p hp n hn c hc (fun _ => 0) 1 one_pos (fun m hm => by
        have := hL m hm
        rw [← h0, mul_zero] at this
        simpa using this)
      simp only [sum_const_zero, mul_zero, zero_mul, add_zero] at h
      rw [hK, ← h0, mul_zero, add_zero]
      unfold renErr at h
      rw [← hS] at h
      exact h
    · have h := renErr_le_scaled p hp n hn c hc L M hpos hL
      unfold renErr at h
      rw [← hS, ← hK] at h
      exact h
  have hSZ : |S| ≤ |Z| + Fb * u p ^ (n + 1) * M := by
    have h1 := abs_sub_abs_le_abs_sub S Z
    rw [abs_sub_comm] at h1
    linarith
  have h2 : u p ^ n * |S| ≤ u p ^ n * (|Z| + Fb * u p ^ (n + 1) * M) :=
    mul_le_mul_of_nonneg_left hSZ (pow_nonneg hu.le n)
  calc |Z - (ren p n n c).sum| ≤ |Z - S| + |S - (ren p n n c).sum| := abs_sub_le _ _ _
    _ ≤ Fb * u p ^ (n + 1) * M + (u p ^ n * (|Z| + Fb * u p ^ (n + 1) * M) + K) := by linarith
    _ = _ := by rw [hK]; ring

/-- `κ = 2(1 + u)^{n-1}/(1 - u) · Λ + (1 + u^n)(R_n + Δ_n)`, with `Λ = ∑_{m ≤ n} L_m` -/
noncomputable def thmKappa (L : ℕ → ℝ) (RΔ : ℝ) : ℝ :=
  2 * (1 + u p) ^ (n - 1) / (1 - u p) * ∑ m ∈ range (n + 1), L m + (1 + u p ^ n) * RΔ

/-- Theorem 15 (`thm:t3`) for MUL: `|ab - x| ≤ u^n|ab| + κu^{n+1}M` with `M = |a_0 b_0|` -/
theorem thm15_mul (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (θ : ℝ) (hθ : 0 < θ)
    (a b : ℕ → ℝ) (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j)) (hHa : Htheta p n θ a)
    (hHb : Htheta p n θ b) :
    |(∑ i ∈ range n, a i) * (∑ j ∈ range n, b j) - (mulOp p n a b).sum| ≤
      u p ^ n * |(∑ i ∈ range n, a i) * (∑ j ∈ range n, b j)| +
        thmKappa p n (mulL p n θ) (((n ^ 2 + n - 1 : ℕ) : ℝ) * mulL p n θ n + thmDelta p n θ) * u p ^ (n + 1) *
          |a 0 * b 0| := by
  obtain ⟨t1, t2, -, -⟩ := thm14_mul p n hp hn hA3 θ hθ a b ha hb hHa hHb
  obtain ⟨-, -, -, -, c5⟩ := mulOps_levels p n hp hn a b _ _ ha hb (Htheta_le p n hHa) (Htheta_le p n hHb) hA3
  have hne : mulOps p n a b ≠ [] := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [mulOps, List.range_succ]
  have hlast := runOps_last_mem p n _ hne LState.init
  exact ren_closed p n hp hn _ (fun i _ => c5 i) _ _ (abs_nonneg _) (t1 _ (List.mem_cons_of_mem _ hlast)) _ _ t2

/-- the levels of ADD are in `F` -/
theorem addLevels_F (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (a b : ℕ → ℝ)
    (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j)) : ∀ m, F p (addLevels p n a b m) := by
  have hlam : ∀ m < n, |a m + b m| ≤ |a m + b m| := fun _ _ => le_rfl
  have hfa : ∀ i < n, _ := fun i hi => facts_a p hp (ha i hi) (hb i hi)
  exact (pairOps_levels p n hp hn _ _ (fun i _ => ⟨F_twoSum_fst p _ _, F_twoSum_snd p _ _⟩)
    (fun i hi => (abs_RN_le p _).trans (mul_le_mul_of_nonneg_left (hlam i hi) (by linarith [u_pos p])))
    (fun i hi => ((hfa i hi).2.1.trans (min_le_right _ _)).trans
      ((mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hlam i hi) (u_pos p).le))) hA3).2.2.2.2

/-- the levels of MULF are in `F` -/
theorem mulfLevels_F (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (a : ℕ → ℝ) (b : ℝ)
    (ha : ∀ i < n, F p (a i)) (hb : F p b) : ∀ m, F p (mulfLevels p n a b m) := by
  have hu := u_pos p
  have hfc : ∀ i < n, _ := fun i hi => facts_c p (ha i hi) hb
  exact (pairOps_levels p n hp hn (fun i => twoProd p (a i) b) (fun i => |a i * b|) (fun i _ => ⟨F_RN p _, F_RN p _⟩)
    (fun i hi => (hfc i hi).2.2)
    (fun i hi => (hfc i hi).2.1.trans (mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _))) hA3).2.2.2.2

/-- Theorem 15 for ADD: `|a + b - x| ≤ u^n|a + b| + κu^{n+1}M` with `M = |a_0| + |b_0|` -/
theorem thm15_add (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (θ : ℝ) (hθ : 0 < θ)
    (a b : ℕ → ℝ) (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j)) (hHa : Htheta p n θ a)
    (hHb : Htheta p n θ b) :
    |(∑ i ∈ range n, a i + ∑ i ∈ range n, b i) - (addOp p n a b).sum| ≤
      u p ^ n * |∑ i ∈ range n, a i + ∑ i ∈ range n, b i| +
        thmKappa p n (pairL p n θ) (((n - 1 : ℕ) : ℝ) * pairL p n θ n) * u p ^ (n + 1) * (|a 0| + |b 0|) := by
  obtain ⟨t1, t2, -, -⟩ := thm14_add p n hp hn hA3 θ hθ a b ha hb hHa hHb
  have hne : addOps p n a b ≠ [] := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [addOps, pairOps, List.range_succ]
  have hlast := runOps_last_mem p n _ hne LState.init
  exact ren_closed p n hp hn _ (fun i _ => addLevels_F p n hp hn hA3 a b ha hb i) _ _ (by positivity)
    (t1 _ (List.mem_cons_of_mem _ hlast)) _ _ (t2.trans_eq (by ring))

/-- Theorem 15 for MULF: `|ab - x| ≤ u^n|ab| + κu^{n+1}M` with `M = |a_0 b|` -/
theorem thm15_mulf (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (θ : ℝ) (hθ : 0 < θ)
    (a : ℕ → ℝ) (b : ℝ) (ha : ∀ i < n, F p (a i)) (hb : F p b) (hHa : Htheta p n θ a) :
    |(∑ i ∈ range n, a i) * b - (mulfOp p n a b).sum| ≤ u p ^ n * |(∑ i ∈ range n, a i) * b| +
      thmKappa p n (pairL p n θ) (((n - 1 : ℕ) : ℝ) * pairL p n θ n) * u p ^ (n + 1) * |a 0 * b| := by
  obtain ⟨t1, t2, -, -⟩ := thm14_mulf p n hp hn hA3 θ hθ a b ha hb hHa
  have hne : mulfOps p n a b ≠ [] := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [mulfOps, pairOps, List.range_succ]
  have hlast := runOps_last_mem p n _ hne LState.init
  exact ren_closed p n hp hn _ (fun i _ => mulfLevels_F p n hp hn hA3 a b ha hb i) _ _ (abs_nonneg _)
    (t1 _ (List.mem_cons_of_mem _ hlast)) _ _ (t2.trans_eq (by ring))

/-- Theorem 15 for ADDF: `|a + b - x| ≤ u^n|a + b| + κu^{n+1}M` with `M = |a_0| + |b|` and `R_n = Δ_n = 0` -/
theorem thm15_addf (hp : 1 < p) (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 < θ) (a : ℕ → ℝ) (b : ℝ) (ha : ∀ i < n, F p (a i))
    (hb : F p b) (hHa : Htheta p n θ a) :
    |(∑ i ∈ range n, a i + b) - (addfOp p n a b).sum| ≤ u p ^ n * |∑ i ∈ range n, a i + b| +
      thmKappa p n (addfL p n θ) 0 * u p ^ (n + 1) * (|a 0| + |b|) := by
  obtain ⟨t1, t2⟩ := thm14_addf p n hp hn θ hθ a b ha hb hHa
  have hF : ∀ i ≤ n, F p (addfLevels p n a b i) := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hch := addf_chain p (n' + 1) hp a b ha hb (fun i => |a i|) (fun _ _ => le_rfl) _ le_rfl
    intro i hi
    rcases Nat.lt_or_ge i (n' + 1) with hlt | hge
    · simp only [addfLevels, hlt, ite_true]
      exact F_twoSum_fst p _ _
    · obtain rfl : i = n' + 1 := by omega
      simp only [addfLevels, lt_irrefl, ite_false, ite_true]
      exact (hch n' (by omega)).2.2.1
  exact ren_closed p n hp hn _ hF _ _ (by positivity) t1 _ 0 (by rw [t2, sub_self, abs_zero]; simp)

omit [Prec_gt_0 p] in
theorem thmD_nonneg (Ah : ℕ → ℝ) (T : ℕ → ℕ) (θ : ℝ) (hθ : 0 < θ) (hA : ∀ m ≤ n, 0 ≤ Ah m)
    (hT : ∀ m < n, (T m : ℝ) * u p < 1) : ∀ m ≤ n, 0 ≤ thmD p Ah T θ m := by
  intro m
  induction m with
  | zero => intro h; exact hA 0 h
  | succ m ih =>
    intro hm
    simp only [thmD]
    have h1 : 0 < 1 - (T m : ℝ) * u p := by linarith [hT m (by omega)]
    exact add_nonneg (hA _ hm) (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (ih (by omega))) (by positivity))

omit [Prec_gt_0 p] in
theorem thmL_nonneg (Ah : ℕ → ℝ) (T : ℕ → ℕ) (θ : ℝ) (hθ : 0 < θ) (Q : ℕ) (hA : ∀ m ≤ n, 0 ≤ Ah m)
    (hT : ∀ m < n, (T m : ℝ) * u p < 1) (hQ : (Q : ℝ) * u p < 1) (m : ℕ) : 0 ≤ thmL p n Ah T θ Q m := by
  have hD := thmD_nonneg p n Ah T θ hθ hA hT
  unfold thmL
  split_ifs with h
  · have : 0 < 1 - (T m : ℝ) * u p := by linarith [hT m h]
    exact div_nonneg (mul_nonneg (by positivity) (hD m h.le)) this.le
  · exact div_nonneg (mul_nonneg (by positivity) (hD n le_rfl)) (by linarith)

omit [Prec_gt_0 p] in
theorem thmKappa_nonneg (hp : 1 < p) (L : ℕ → ℝ) (hL : ∀ m, 0 ≤ L m) (RΔ : ℝ) (hR : 0 ≤ RΔ) :
    0 ≤ thmKappa p n L RΔ := by
  have hu := u_pos p
  have h1 : 0 < 1 - u p := by linarith [u_le_half p hp]
  unfold thmKappa
  exact add_nonneg (mul_nonneg (div_nonneg (by positivity) h1.le) (sum_nonneg fun m _ => hL m))
    (mul_nonneg (by positivity) hR)

omit [Prec_gt_0 p] in
theorem mulL_nonneg (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (θ : ℝ) (hθ : 0 < θ) (m : ℕ) :
    0 ≤ mulL p n θ m := by
  have hu := u_pos p
  refine thmL_nonneg p n _ _ θ hθ _ (fun m hm => ?_) (fun m hm => ?_) ?_ m
  · unfold hatAmul
    split_ifs with h1 h2
    · positivity
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have : 0 ≤ (n : ℝ) / θ := by positivity
      linarith
    · exact le_rfl
  · have h : (mulT m : ℝ) ≤ (n : ℝ) ^ 2 + n := by
      unfold mulT; push_cast
      have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hm
      nlinarith
    nlinarith
  · have h : (((n ^ 2 + n - 1 : ℕ) : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 + n := by
      have : n ^ 2 + n - 1 ≤ n ^ 2 + n := Nat.sub_le _ _
      exact_mod_cast this
    nlinarith

omit [Prec_gt_0 p] in
theorem pairL_nonneg (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (θ : ℝ) (hθ : 0 < θ) (m : ℕ) : 0 ≤ pairL p n θ m := by
  have hu := u_pos p
  refine thmL_nonneg p n _ _ θ hθ _ (fun m hm => ?_) (fun m hm => ?_) ?_ m
  · unfold hatApair
    split_ifs <;> positivity
  · have : (m : ℝ) ≤ (n : ℝ) ^ 2 + n := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hm.le
      nlinarith
    simp only [id]
    nlinarith
  · have : (((n - 1 : ℕ) : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 + n := by
      have : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
      nlinarith
    nlinarith

omit [Prec_gt_0 p] in
theorem thmDelta_nonneg (θ : ℝ) (hθ : 0 ≤ θ) : 0 ≤ thmDelta p n θ :=
  sum_nonneg fun _ _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hθ _)) (pow_nonneg (u_pos p).le _)

omit [Prec_gt_0 p] in
theorem addfL_nonneg (θ : ℝ) (hθ : 0 ≤ θ) (m : ℕ) : 0 ≤ addfL p n θ m := by
  have hu := u_pos p
  unfold addfL
  split_ifs
  · exact mul_nonneg (by linarith) (sum_nonneg fun k _ => pow_nonneg hθ k)
  · exact sum_nonneg fun k _ => pow_nonneg hθ k

omit [Prec_gt_0 p] in
/-- `(eq:a0)`: on `H(θ)` with `2ρ < 1`, `|a| ≥ (1 - 2ρ)/(1 - ρ) |a_0|`, so `|a_0| ≤ (1 - ρ)/(1 - 2ρ) |a|` -/
theorem Htheta_a0 (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 ≤ θ) (hρ : 2 * (θ * u p) < 1) (a : ℕ → ℝ) (hH : Htheta p n θ a) :
    |a 0| ≤ (1 - θ * u p) / (1 - 2 * (θ * u p)) * |∑ i ∈ range n, a i| := by
  obtain ⟨ρ, hρd⟩ : ∃ ρ, ρ = θ * u p := ⟨_, rfl⟩
  rw [← hρd] at hρ ⊢
  have hρ0 : 0 ≤ ρ := by rw [hρd]; exact mul_nonneg hθ (u_pos p).le
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ']
  have ht : |∑ i ∈ range k, a (i + 1)| ≤ ρ / (1 - ρ) * |a 0| := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ range k, |a (i + 1)| ≤ ∑ i ∈ range k, ρ ^ (i + 1) * |a 0| :=
          sum_le_sum fun i hi => by rw [hρd]; exact hH (i + 1) (by omega) (by rw [mem_range] at hi; omega)
      _ = ρ * |a 0| * ∑ i ∈ range k, ρ ^ i := by rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
      _ ≤ ρ * |a 0| * (1 / (1 - ρ)) := mul_le_mul_of_nonneg_left (geom_le ρ hρ0 (by linarith) k) (by positivity)
      _ = ρ / (1 - ρ) * |a 0| := by ring
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < 1 - 2 * ρ := by linarith
  have hS : (1 - 2 * ρ) / (1 - ρ) * |a 0| ≤ |∑ i ∈ range k, a (i + 1) + a 0| := by
    have := abs_sub_abs_le_abs_sub (a 0) (-∑ i ∈ range k, a (i + 1))
    rw [abs_neg, sub_neg_eq_add, add_comm] at this
    have he : (1 - 2 * ρ) / (1 - ρ) = 1 - ρ / (1 - ρ) := by field_simp; ring
    rw [he]
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h2]
  calc |a 0| * (1 - 2 * ρ) = (1 - ρ) * ((1 - 2 * ρ) / (1 - ρ) * |a 0|) := by field_simp
    _ ≤ (1 - ρ) * |∑ i ∈ range k, a (i + 1) + a 0| := mul_le_mul_of_nonneg_left hS h1.le

/-- Theorem 15's form for MUL: `|ab - x| ≤ (u^n + κu^{n+1}((1 - ρ)/(1 - 2ρ))²)|ab|` -/
theorem thm15_mul_rel (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (θ : ℝ) (hθ : 0 < θ)
    (hρ : 2 * (θ * u p) < 1) (a b : ℕ → ℝ) (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j))
    (hHa : Htheta p n θ a) (hHb : Htheta p n θ b) :
    |(∑ i ∈ range n, a i) * (∑ j ∈ range n, b j) - (mulOp p n a b).sum| ≤
      (u p ^ n + thmKappa p n (mulL p n θ) (((n ^ 2 + n - 1 : ℕ) : ℝ) * mulL p n θ n + thmDelta p n θ) *
        u p ^ (n + 1) * ((1 - θ * u p) / (1 - 2 * (θ * u p))) ^ 2) * |(∑ i ∈ range n, a i) * (∑ j ∈ range n, b j)| := by
  have hk := thmKappa_nonneg p n hp _ (mulL_nonneg p n hn hA3 θ hθ)
    (((n ^ 2 + n - 1 : ℕ) : ℝ) * mulL p n θ n + thmDelta p n θ)
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (mulL_nonneg p n hn hA3 θ hθ n)) (thmDelta_nonneg p n θ hθ.le))
  have hc : 0 ≤ (1 - θ * u p) / (1 - 2 * (θ * u p)) :=
    div_nonneg (by linarith [mul_nonneg hθ.le (u_pos p).le]) (by linarith)
  have hM : |a 0 * b 0| ≤ ((1 - θ * u p) / (1 - 2 * (θ * u p))) ^ 2 *
      |(∑ i ∈ range n, a i) * (∑ j ∈ range n, b j)| := by
    rw [abs_mul, abs_mul, sq]
    calc |a 0| * |b 0| ≤ ((1 - θ * u p) / (1 - 2 * (θ * u p)) * |∑ i ∈ range n, a i|) *
          ((1 - θ * u p) / (1 - 2 * (θ * u p)) * |∑ j ∈ range n, b j|) :=
          mul_le_mul (Htheta_a0 p n hn θ hθ.le hρ a hHa) (Htheta_a0 p n hn θ hθ.le hρ b hHb) (abs_nonneg _)
            (mul_nonneg hc (abs_nonneg _))
      _ = _ := by ring
  refine (thm15_mul p n hp hn hA3 θ hθ a b ha hb hHa hHb).trans ?_
  have := mul_le_mul_of_nonneg_left hM (mul_nonneg hk (pow_nonneg (u_pos p).le (n + 1)))
  nlinarith

/-- Theorem 15's form for MULF: `|ab - x| ≤ (u^n + κu^{n+1}(1 - ρ)/(1 - 2ρ))|ab|` -/
theorem thm15_mulf_rel (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (θ : ℝ) (hθ : 0 < θ)
    (hρ : 2 * (θ * u p) < 1) (a : ℕ → ℝ) (b : ℝ) (ha : ∀ i < n, F p (a i)) (hb : F p b) (hHa : Htheta p n θ a) :
    |(∑ i ∈ range n, a i) * b - (mulfOp p n a b).sum| ≤
      (u p ^ n + thmKappa p n (pairL p n θ) (((n - 1 : ℕ) : ℝ) * pairL p n θ n) * u p ^ (n + 1) *
        ((1 - θ * u p) / (1 - 2 * (θ * u p)))) * |(∑ i ∈ range n, a i) * b| := by
  have hk := thmKappa_nonneg p n hp _ (pairL_nonneg p n hA3 θ hθ) (((n - 1 : ℕ) : ℝ) * pairL p n θ n)
    (mul_nonneg (Nat.cast_nonneg _) (pairL_nonneg p n hA3 θ hθ n))
  have hM : |a 0 * b| ≤ (1 - θ * u p) / (1 - 2 * (θ * u p)) * |(∑ i ∈ range n, a i) * b| := by
    rw [abs_mul, abs_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (Htheta_a0 p n hn θ hθ.le hρ a hHa) (abs_nonneg _)
  refine (thm15_mulf p n hp hn hA3 θ hθ a b ha hb hHa).trans ?_
  have := mul_le_mul_of_nonneg_left hM (mul_nonneg hk (pow_nonneg (u_pos p).le (n + 1)))
  nlinarith

/-- Theorem 15's form for ADD: `|a + b - x| ≤ u^n|a + b| + κu^{n+1}(1 - ρ)/(1 - 2ρ)(|a| + |b|)` -/
theorem thm15_add_rel (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (θ : ℝ) (hθ : 0 < θ)
    (hρ : 2 * (θ * u p) < 1) (a b : ℕ → ℝ) (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j))
    (hHa : Htheta p n θ a) (hHb : Htheta p n θ b) :
    |(∑ i ∈ range n, a i + ∑ i ∈ range n, b i) - (addOp p n a b).sum| ≤
      u p ^ n * |∑ i ∈ range n, a i + ∑ i ∈ range n, b i| +
        thmKappa p n (pairL p n θ) (((n - 1 : ℕ) : ℝ) * pairL p n θ n) * u p ^ (n + 1) *
          ((1 - θ * u p) / (1 - 2 * (θ * u p))) * (|∑ i ∈ range n, a i| + |∑ i ∈ range n, b i|) := by
  have hk := thmKappa_nonneg p n hp _ (pairL_nonneg p n hA3 θ hθ) (((n - 1 : ℕ) : ℝ) * pairL p n θ n)
    (mul_nonneg (Nat.cast_nonneg _) (pairL_nonneg p n hA3 θ hθ n))
  have hM : |a 0| + |b 0| ≤ (1 - θ * u p) / (1 - 2 * (θ * u p)) * (|∑ i ∈ range n, a i| + |∑ i ∈ range n, b i|) := by
    rw [mul_add]
    exact add_le_add (Htheta_a0 p n hn θ hθ.le hρ a hHa) (Htheta_a0 p n hn θ hθ.le hρ b hHb)
  refine (thm15_add p n hp hn hA3 θ hθ a b ha hb hHa hHb).trans ?_
  have := mul_le_mul_of_nonneg_left hM (mul_nonneg hk (pow_nonneg (u_pos p).le (n + 1)))
  nlinarith

/-- Theorem 15's form for ADDF: `|a + b - x| ≤ u^n|a + b| + κu^{n+1}((1 - ρ)/(1 - 2ρ)|a| + |b|)` -/
theorem thm15_addf_rel (hp : 1 < p) (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 < θ) (hρ : 2 * (θ * u p) < 1) (a : ℕ → ℝ)
    (b : ℝ) (ha : ∀ i < n, F p (a i)) (hb : F p b) (hHa : Htheta p n θ a) :
    |(∑ i ∈ range n, a i + b) - (addfOp p n a b).sum| ≤ u p ^ n * |∑ i ∈ range n, a i + b| +
      thmKappa p n (addfL p n θ) 0 * u p ^ (n + 1) *
        ((1 - θ * u p) / (1 - 2 * (θ * u p)) * |∑ i ∈ range n, a i| + |b|) := by
  have hk := thmKappa_nonneg p n hp _ (addfL_nonneg p n θ hθ.le) _ le_rfl
  have hM : |a 0| + |b| ≤ (1 - θ * u p) / (1 - 2 * (θ * u p)) * |∑ i ∈ range n, a i| + |b| :=
    add_le_add (Htheta_a0 p n hn θ hθ.le hρ a hHa) le_rfl
  refine (thm15_addf p n hp hn θ hθ a b ha hb hHa).trans ?_
  have := mul_le_mul_of_nonneg_left hM (mul_nonneg hk (pow_nonneg (u_pos p).le (n + 1)))
  nlinarith

end ExpansionBounds
