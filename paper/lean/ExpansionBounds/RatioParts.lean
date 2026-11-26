import ExpansionBounds.Recip

/-!
# `recip::ratio_parts` computes the greedy expansion

`ratio_parts(p, q)` keeps what is left of `p/q` as `(-1)^neg n / (q 2^e)` with `n` an integer. Each part is the u128
quotient `n 2^s / q`, put in `[2^52, 2^53)` by the shift `s` (a first guess, one more where its quotient falls short:
`rpShift`), rounded once to the nearest integer with ties to even and scaled by `2^{-(e + s)}` (`rpStep`). Each part
is `RN` of what is left (`rpStep_spec`), so the parts are the greedy expansion of `p/q` (`rpPart_eq`).
-/

namespace ExpansionBounds

variable (p : ℤ) [Prec_gt_0 p]

/-- the rounding of one step: `a / dv` in `[2^52, 2^53)`, its floor `q0`, rounded up where the remainder is past half
of `dv` or at half with `q0` odd -/
def rpRound (a dv : ℕ) : ℕ :=
  a / dv + if dv < 2 * (a % dv) ∨ (2 * (a % dv) = dv ∧ (a / dv) % 2 = 1) then 1 else 0

omit [Prec_gt_0 p] in
/-- `RN` at `a/dv` in `[2^52, 2^53)`, scaled by `2^E`, is `rpRound` scaled by `2^E` -/
theorem rn_rpRound (hp : p = 53) {a dv : ℕ} (hdv : 0 < dv) (hlo : 2 ^ 52 ≤ a / dv) (hhi : a / dv < 2 ^ 53)
    (E : ℤ) : RN p ((2 : ℝ) ^ E * ((a : ℝ) / dv)) = (2 : ℝ) ^ E * (rpRound a dv : ℝ) := by
  rw [RN_zpow_mul]
  congr 1
  set q0 := a / dv with hq0
  set r := a % dv with hr
  have hdvR : (0 : ℝ) < dv := by exact_mod_cast hdv
  have hsplit : (a : ℝ) / dv = q0 + (r : ℝ) / dv := by
    have hnat : (a : ℝ) = dv * q0 + r := by exact_mod_cast (Nat.div_add_mod a dv).symm
    rw [hnat]
    field_simp
  have hrlt : (r : ℝ) / dv < 1 := by
    rw [div_lt_one hdvR]
    exact_mod_cast Nat.mod_lt a hdv
  have hr0 : (0 : ℝ) ≤ (r : ℝ) / dv := by positivity
  have hfl : ⌊(a : ℝ) / dv⌋ = (q0 : ℤ) := by
    rw [Int.floor_eq_iff, hsplit]
    push_cast
    constructor <;> linarith
  have hq0lo : (2 : ℝ) ^ (52 : ℕ) ≤ q0 := by exact_mod_cast hlo
  have hq0hi : (q0 : ℝ) + 1 ≤ (2 : ℝ) ^ (53 : ℕ) := by exact_mod_cast hhi
  have hz1 : (2 : ℝ) ^ (53 - 1 : ℤ) ≤ |(a : ℝ) / dv| := by
    rw [abs_of_nonneg (by positivity), hsplit, show (53 - 1 : ℤ) = ((52 : ℕ) : ℤ) by norm_num, zpow_natCast]
    linarith
  have hz2 : |(a : ℝ) / dv| < (2 : ℝ) ^ (53 : ℤ) := by
    rw [abs_of_nonneg (by positivity), hsplit, show (53 : ℤ) = ((53 : ℕ) : ℤ) by norm_num, zpow_natCast]
    linarith
  rw [hp] at *
  rw [RN_of_mag 53 hz1 hz2, sub_self, neg_zero, zpow_zero, mul_one, mul_one, Znearest_tieEven, hfl]
  have hfr : (a : ℝ) / dv - (q0 : ℤ) = (r : ℝ) / dv := by rw [hsplit]; push_cast; ring
  rw [hfr]
  have e1 : (r : ℝ) / dv < 1 / 2 ↔ ¬ (dv ≤ 2 * r) := by
    rw [div_lt_iff₀ hdvR, not_le]
    constructor <;> intro h
    · exact_mod_cast (by linarith : (2 : ℝ) * r < dv)
    · have : (2 : ℝ) * r < dv := by exact_mod_cast h
      linarith
  have e2 : 1 / 2 < (r : ℝ) / dv ↔ dv < 2 * r := by
    rw [lt_div_iff₀ hdvR]
    constructor <;> intro h
    · exact_mod_cast (by linarith : (dv : ℝ) < 2 * r)
    · have : (dv : ℝ) < 2 * r := by exact_mod_cast h
      linarith
  have e3 : ((q0 : ℤ) % 2 = 1) ↔ q0 % 2 = 1 := by omega
  suffices H : (if (r : ℝ) / dv < 1 / 2 then (q0 : ℤ) else if 1 / 2 < (r : ℝ) / dv then (q0 : ℤ) + 1
      else if (q0 : ℤ) % 2 = 1 then (q0 : ℤ) + 1 else (q0 : ℤ)) = ((rpRound a dv : ℕ) : ℤ) by
    rw [H, Int.cast_natCast]
  unfold rpRound
  rw [← hq0, ← hr]
  by_cases h1 : dv ≤ 2 * r
  · rw [ite_eq_right (by rw [e1]; exact not_not.mpr h1)]
    by_cases h2 : dv < 2 * r
    · rw [ite_eq_left (e2.mpr h2), ite_eq_left (Or.inl h2)]
      omega
    · have h2' : 2 * r = dv := by omega
      rw [ite_eq_right (by rw [e2]; exact h2)]
      by_cases h3 : q0 % 2 = 1
      · rw [ite_eq_left (e3.mpr h3), ite_eq_left (Or.inr ⟨h2', h3⟩)]
        omega
      · rw [ite_eq_right (by rw [e3]; exact h3), ite_eq_right (by omega)]
        omega
  · rw [ite_eq_left (by rw [e1]; exact h1), ite_eq_right (by omega)]
    omega

/-- the bit length of `n`, `128 - n.leading_zeros()` for a u128 -/
def bitLen (n : ℕ) : ℕ := if n = 0 then 0 else Nat.log2 n + 1

theorem bitLen_bounds {n : ℕ} (hn : n ≠ 0) : 2 ^ (bitLen n - 1) ≤ n ∧ n < 2 ^ bitLen n := by
  unfold bitLen
  rw [ite_eq_right hn, Nat.add_sub_cancel]
  exact ⟨Nat.log2_self_le hn, Nat.lt_log2_self⟩

/-- `split(s)`: the dividend `n 2^s` and divisor `q` for `s ≥ 0`, else `n` and `q 2^{-s}` -/
def rpSplit (n q : ℕ) (s : ℤ) : ℕ × ℕ := if 0 ≤ s then (n * 2 ^ s.toNat, q) else (n, q * 2 ^ (-s).toNat)

/-- the shift: `s = 52 - (bits(n) - bits(q))`, one more where `split(s)`'s quotient is below `2^52` -/
def rpShift (n q : ℕ) : ℤ :=
  if (rpSplit n q (52 - ((bitLen n : ℤ) - bitLen q))).1 / (rpSplit n q (52 - ((bitLen n : ℤ) - bitLen q))).2 < 2 ^ 52
  then 52 - ((bitLen n : ℤ) - bitLen q) + 1 else 52 - ((bitLen n : ℤ) - bitLen q)

omit [Prec_gt_0 p] in
/-- `split(s)` is `n 2^s / q` with a positive divisor, and its divisor times `2^{e + s}` is `q 2^{e + max(s, 0)}` -/
theorem rpSplit_val (n q : ℕ) (s e : ℤ) (hq : 0 < q) :
    0 < (rpSplit n q s).2 ∧ ((rpSplit n q s).1 : ℝ) / (rpSplit n q s).2 = n * (2 : ℝ) ^ s / q ∧
      ((rpSplit n q s).2 : ℝ) * (2 : ℝ) ^ (e + s) = q * (2 : ℝ) ^ (e + max s 0) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  unfold rpSplit
  split_ifs with hs
  · have h2 : ((2 : ℝ) ^ s.toNat) = (2 : ℝ) ^ s := by rw [← zpow_natCast, Int.toNat_of_nonneg hs]
    refine ⟨hq, ?_, ?_⟩
    · push_cast; rw [h2]
    · rw [max_eq_left hs]
  · have hs' : 0 ≤ -s := by omega
    have h2 : ((2 : ℝ) ^ (-s).toNat) = (2 : ℝ) ^ (-s) := by rw [← zpow_natCast, Int.toNat_of_nonneg hs']
    refine ⟨Nat.mul_pos hq (Nat.pow_pos (by norm_num)), ?_, ?_⟩
    · push_cast
      rw [h2, zpow_neg]
      field_simp
    · push_cast
      rw [h2, max_eq_right (by omega), add_zero, mul_assoc, ← zpow_add₀ two_ne_zero]
      ring_nf

omit [Prec_gt_0 p] in
/-- the quotient of `split(s)` is the floor of `n 2^s / q` -/
theorem rpSplit_div (n q : ℕ) (s : ℤ) (hq : 0 < q) :
    (rpSplit n q s).1 / (rpSplit n q s).2 = ⌊(n : ℝ) * (2 : ℝ) ^ s / q⌋₊ := by
  rw [← (rpSplit_val n q s 0 hq).2.1]
  set A := (rpSplit n q s).1
  set D := (rpSplit n q s).2
  have hD : (0 : ℝ) < D := by exact_mod_cast (rpSplit_val n q s 0 hq).1
  have hnat : (A : ℝ) = D * (A / D : ℕ) + (A % D : ℕ) := by exact_mod_cast (Nat.div_add_mod A D).symm
  have hlt : ((A % D : ℕ) : ℝ) < D := by exact_mod_cast Nat.mod_lt A (rpSplit_val n q s 0 hq).1
  symm
  rw [Nat.floor_eq_iff (by positivity), le_div_iff₀ hD, div_lt_iff₀ hD]
  constructor <;> nlinarith [(Nat.cast_nonneg (A % D : ℕ) : (0 : ℝ) ≤ _)]

omit [Prec_gt_0 p] in
/-- at `s_0 = 52 - (bits(n) - bits(q))`, `n 2^{s_0} / q` lies in `(2^51, 2^53)` -/
theorem rpShift0_range {n q : ℕ} (hn : n ≠ 0) (hq : 0 < q) :
    (2 : ℝ) ^ (51 : ℤ) < n * (2 : ℝ) ^ (52 - ((bitLen n : ℤ) - bitLen q)) / q ∧
      n * (2 : ℝ) ^ (52 - ((bitLen n : ℤ) - bitLen q)) / q < (2 : ℝ) ^ (53 : ℤ) := by
  obtain ⟨hn1, hn2⟩ := bitLen_bounds hn
  obtain ⟨hq1, hq2⟩ := bitLen_bounds hq.ne'
  have hLn : 1 ≤ bitLen n := by
    by_contra h
    have : bitLen n = 0 := by omega
    rw [this] at hn2
    omega
  have hLq : 1 ≤ bitLen q := by
    by_contra h
    have : bitLen q = 0 := by omega
    rw [this] at hq2
    omega
  set Ln := bitLen n
  set Lq := bitLen q
  have z (k : ℕ) : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ (k : ℤ) := by push_cast; rw [zpow_natCast]
  have n1 : (2 : ℝ) ^ ((Ln : ℤ) - 1) ≤ n := by
    have h := (Nat.cast_le (α := ℝ)).mpr hn1
    rwa [z, Nat.cast_sub hLn, Nat.cast_one] at h
  have n2 : (n : ℝ) < (2 : ℝ) ^ (Ln : ℤ) := by
    have h := (Nat.cast_lt (α := ℝ)).mpr hn2
    rwa [z] at h
  have q1 : (2 : ℝ) ^ ((Lq : ℤ) - 1) ≤ q := by
    have h := (Nat.cast_le (α := ℝ)).mpr hq1
    rwa [z, Nat.cast_sub hLq, Nat.cast_one] at h
  have q2 : (q : ℝ) < (2 : ℝ) ^ (Lq : ℤ) := by
    have h := (Nat.cast_lt (α := ℝ)).mpr hq2
    rwa [z] at h
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hS : (0 : ℝ) < (2 : ℝ) ^ (52 - ((Ln : ℤ) - Lq)) := by positivity
  constructor
  · rw [lt_div_iff₀ hqR]
    calc (2 : ℝ) ^ (51 : ℤ) * q < (2 : ℝ) ^ (51 : ℤ) * (2 : ℝ) ^ (Lq : ℤ) := by gcongr
      _ = (2 : ℝ) ^ ((Ln : ℤ) - 1) * (2 : ℝ) ^ (52 - ((Ln : ℤ) - Lq)) := by
        rw [← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]; ring_nf
      _ ≤ n * (2 : ℝ) ^ (52 - ((Ln : ℤ) - Lq)) := by gcongr
  · rw [div_lt_iff₀ hqR]
    calc n * (2 : ℝ) ^ (52 - ((Ln : ℤ) - Lq)) < (2 : ℝ) ^ (Ln : ℤ) * (2 : ℝ) ^ (52 - ((Ln : ℤ) - Lq)) := by gcongr
      _ = (2 : ℝ) ^ (53 : ℤ) * (2 : ℝ) ^ ((Lq : ℤ) - 1) := by
        rw [← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]; ring_nf
      _ ≤ (2 : ℝ) ^ (53 : ℤ) * q := by gcongr

omit [Prec_gt_0 p] in
/-- at the shift, the quotient of `split(s)` lies in `[2^52, 2^53)` -/
theorem rpShift_range {n q : ℕ} (hn : n ≠ 0) (hq : 0 < q) :
    2 ^ 52 ≤ (rpSplit n q (rpShift n q)).1 / (rpSplit n q (rpShift n q)).2 ∧
      (rpSplit n q (rpShift n q)).1 / (rpSplit n q (rpShift n q)).2 < 2 ^ 53 := by
  obtain ⟨h1, h2⟩ := rpShift0_range hn hq
  set s0 : ℤ := 52 - ((bitLen n : ℤ) - bitLen q) with hs0
  have hz0 : (0 : ℝ) ≤ n * (2 : ℝ) ^ s0 / q := by positivity
  have c51 : ((2 : ℝ) ^ (51 : ℤ)) = ((2 ^ 51 : ℕ) : ℝ) := by norm_num
  have c52 : ((2 : ℝ) ^ (52 : ℤ)) = ((2 ^ 52 : ℕ) : ℝ) := by norm_num
  have c53 : ((2 : ℝ) ^ (53 : ℤ)) = ((2 ^ 53 : ℕ) : ℝ) := by norm_num
  unfold rpShift
  rw [← hs0]
  split_ifs with hlt
  · rw [rpSplit_div n q s0 hq, Nat.floor_lt hz0] at hlt
    have hz : n * (2 : ℝ) ^ (s0 + 1) / q = 2 * (n * (2 : ℝ) ^ s0 / q) := by
      rw [zpow_add_one₀ two_ne_zero]; ring
    rw [rpSplit_div n q (s0 + 1) hq, hz]
    have hz1 : (0 : ℝ) ≤ 2 * (n * (2 : ℝ) ^ s0 / q) := by positivity
    constructor
    · rw [Nat.le_floor_iff hz1]
      have : (((2 : ℕ) ^ 52 : ℕ) : ℝ) = 2 * (2 : ℝ) ^ (51 : ℤ) := by push_cast; norm_num
      rw [this]
      linarith
    · rw [Nat.floor_lt hz1]
      have : (((2 : ℕ) ^ 53 : ℕ) : ℝ) = 2 * (((2 : ℕ) ^ 52 : ℕ) : ℝ) := by push_cast; ring
      rw [this]
      linarith
  · push Not at hlt
    rw [rpSplit_div n q s0 hq] at hlt ⊢
    exact ⟨hlt, by rw [Nat.floor_lt hz0, ← c53]; exact h2⟩

/-- what `ratio_parts` keeps between parts: `(-1)^neg n / (q 2^e)` is what the parts so far leave of `p/q` -/
structure RPState where
  n : ℕ
  neg : Bool
  e : ℤ

/-- the value that a state stands for -/
noncomputable def rpVal (q : ℕ) (st : RPState) : ℝ := (if st.neg then -1 else 1) * st.n / (q * (2 : ℝ) ^ st.e)

/-- one part of `ratio_parts` and the state after it; `0` and the same state where nothing is left -/
noncomputable def rpStep (q : ℕ) (st : RPState) : ℝ × RPState :=
  if st.n = 0 then (0, st) else
    ((if st.neg then -1 else 1) * ((rpRound (rpSplit st.n q (rpShift st.n q)).1 (rpSplit st.n q (rpShift st.n q)).2 : ℝ) *
        (2 : ℝ) ^ (-(st.e + rpShift st.n q))),
      ⟨((rpSplit st.n q (rpShift st.n q)).1 - rpRound (rpSplit st.n q (rpShift st.n q)).1
          (rpSplit st.n q (rpShift st.n q)).2 * (rpSplit st.n q (rpShift st.n q)).2 : ℤ).natAbs,
        xor st.neg (decide (((rpSplit st.n q (rpShift st.n q)).1 - rpRound (rpSplit st.n q (rpShift st.n q)).1
          (rpSplit st.n q (rpShift st.n q)).2 * (rpSplit st.n q (rpShift st.n q)).2 : ℤ) < 0)),
        st.e + max (rpShift st.n q) 0⟩)

/-- a step's part is `RN` of what is left, and the state after it stands for what the part leaves -/
theorem rpStep_spec (hp : p = 53) {q : ℕ} (hq : 0 < q) (st : RPState) :
    (rpStep q st).1 = RN p (rpVal q st) ∧ rpVal q (rpStep q st).2 = rpVal q st - (rpStep q st).1 := by
  by_cases hn : st.n = 0
  · have h0 : rpVal q st = 0 := by simp [rpVal, hn]
    simp only [rpStep, hn, ↓reduceIte, h0, RN_zero, sub_zero, and_self]
  obtain ⟨hlo, hhi⟩ := rpShift_range hn hq
  obtain ⟨hD0, hval, hscale⟩ := rpSplit_val st.n q (rpShift st.n q) st.e hq
  set sh := rpShift st.n q with hsh
  set A := (rpSplit st.n q sh).1 with hA
  set D := (rpSplit st.n q sh).2 with hD
  set g : ℝ := if st.neg then -1 else 1 with hg
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
  -- what is left is `g 2^{-(e + s)} (A / D)`
  have hv : rpVal q st = g * ((2 : ℝ) ^ (-(st.e + sh)) * ((A : ℝ) / D)) := by
    unfold rpVal
    rw [← hg, hval, zpow_neg, zpow_add₀ two_ne_zero]
    field_simp
  have hpart : (rpStep q st).1 = g * ((2 : ℝ) ^ (-(st.e + sh)) * (rpRound A D : ℝ)) := by
    simp only [rpStep, hn, ↓reduceIte]
    rw [← hsh, ← hA, ← hD, ← hg]
    ring
  constructor
  · rw [hpart, hv, ← rn_rpRound p hp hD0 hlo hhi]
    rcases Bool.eq_false_or_eq_true st.neg with h | h
    · simp [hg, h, RN_neg]
    · simp [hg, h]
  · have hnext : rpVal q (rpStep q st).2 =
        g * (((A : ℤ) - (rpRound A D : ℤ) * D : ℤ) : ℝ) / (q * (2 : ℝ) ^ (st.e + max sh 0)) := by
      simp only [rpStep, hn, ↓reduceIte, rpVal]
      rw [← hsh, ← hA, ← hD]
      set r : ℤ := (A : ℤ) - (rpRound A D : ℤ) * D
      congr 1
      rcases lt_or_ge r 0 with hr | hr
      · have : ((r.natAbs : ℕ) : ℝ) = -(r : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hr)]
        rw [this]
        rcases Bool.eq_false_or_eq_true st.neg with h | h
        · simp [hg, h, hr]
        · simp [hg, h, hr]
      · have : ((r.natAbs : ℕ) : ℝ) = (r : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hr)]
        rw [this]
        have hr' : ¬ r < 0 := not_lt.mpr hr
        rcases Bool.eq_false_or_eq_true st.neg with h | h
        · simp [hg, h, hr']
        · simp [hg, h, hr']
    rw [hnext, hpart, hv, ← hscale]
    push_cast
    rw [zpow_neg]
    field_simp

/-- the state before part `i` of `ratio_parts(a, q)`: `|a|`, its sign and `e = 0` to start -/
noncomputable def rpState (a : ℤ) (q : ℕ) : ℕ → RPState
  | 0 => ⟨a.natAbs, decide (a < 0), 0⟩
  | i + 1 => (rpStep q (rpState a q i)).2

/-- part `i` of `ratio_parts(a, q)` -/
noncomputable def rpPart (a : ℤ) (q : ℕ) (i : ℕ) : ℝ := (rpStep q (rpState a q i)).1

/-- `ratio_parts(a, q)` gives the greedy expansion of `a/q`: each part is `RN` of what the parts before it leave -/
theorem rpPart_eq (hp : p = 53) (a : ℤ) {q : ℕ} (hq : 0 < q) (i : ℕ) :
    rpPart a q i = gPart p ((a : ℝ) / q) i := by
  have key : ∀ i, rpVal q (rpState a q i) = gRem p ((a : ℝ) / q) i := by
    intro i
    induction i with
    | zero =>
      simp only [rpState, rpVal, gRem, zpow_zero, mul_one]
      rcases lt_or_ge a 0 with h | h
      · have : ((a.natAbs : ℕ) : ℝ) = -(a : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast h)]
        simp [h, this]
      · have : ((a.natAbs : ℕ) : ℝ) = (a : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast h)]
        simp [not_lt.mpr h, this]
    | succ i ih =>
      obtain ⟨h1, h2⟩ := rpStep_spec p hp hq (rpState a q i)
      simp only [rpState]
      rw [h2, h1, ih, gRem_succ]
      rfl
  obtain ⟨h1, -⟩ := rpStep_spec p hp hq (rpState a q i)
  rw [rpPart, h1, key i]
  rfl

end ExpansionBounds
