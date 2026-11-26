import ExpansionBounds.RatioParts

/-!
# `recip::ratio_parts` stays within u128 and binary64

For `1 ≤ q < 2^60` and `|p| ≤ 2^63` the eight steps of `ratio_parts` never leave the integers that u128 and i128
hold, and every part's scale `2^{-(e + s)}` is a normal binary64 number (`rp_bounds`): what is left after the first
part is below `q 2^{11}`, after the second at most `q/2` (`rpState_inv`), so every shift past the first is at least
`41`, every shift at most `112`, and `e` at most `112` times the number of parts.
-/

namespace ExpansionBounds

theorem bitLen_le {n k : ℕ} (h : n < 2 ^ k) : bitLen n ≤ k := by
  by_cases hn : n = 0
  · simp [bitLen, hn]
  obtain ⟨h1, -⟩ := bitLen_bounds hn
  have : 2 ^ (bitLen n - 1) < 2 ^ k := lt_of_le_of_lt h1 h
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp this
  omega

theorem bitLen_pos {n : ℕ} (hn : n ≠ 0) : 1 ≤ bitLen n := by
  unfold bitLen
  rw [ite_eq_right hn]
  omega

/-- the rounded quotient misses `A` by at most half of `D` -/
theorem rpRound_rem (A D : ℕ) (hD : 0 < D) : 2 * ((A : ℤ) - rpRound A D * D).natAbs ≤ D := by
  have h := Nat.div_add_mod A D
  have hr := Nat.mod_lt A hD
  unfold rpRound
  generalize hX : A / D * D = X at *
  generalize A % D = r at *
  have hA : (A : ℤ) = X + r := by rw [← h, ← hX]; push_cast; ring
  split_ifs with hc
  · have : ((A / D + 1 : ℕ) : ℤ) * D = X + D := by rw [← hX]; push_cast; ring
    rw [show ((A : ℤ) - ((A / D + 1 : ℕ) : ℤ) * D) = r - D by rw [this, hA]; ring]
    omega
  · have : ((A / D + 0 : ℕ) : ℤ) * D = X := by rw [← hX]; push_cast; ring
    rw [show ((A : ℤ) - ((A / D + 0 : ℕ) : ℤ) * D) = r by rw [this, hA]; ring]
    omega

theorem rpRound_le {A D : ℕ} (h : A / D < 2 ^ 53) : rpRound A D ≤ 2 ^ 53 := by
  unfold rpRound
  split_ifs <;> omega

/-- the shift is `s_0` or `s_0 + 1`, `s_0 = 52 - (bits(n) - bits(q))` -/
theorem rpShift_cases (n q : ℕ) :
    rpShift n q = 52 - ((bitLen n : ℤ) - bitLen q) ∨ rpShift n q = 52 - ((bitLen n : ℤ) - bitLen q) + 1 := by
  unfold rpShift
  split_ifs <;> simp

/-- `split(s)`'s divisor is `q 2^{max(-s, 0)}` -/
theorem rpSplit_snd (n q : ℕ) (s : ℤ) : (rpSplit n q s).2 = q * 2 ^ (-s).toNat := by
  unfold rpSplit
  split_ifs with hs
  · simp [show (-s).toNat = 0 by omega]
  · rfl

/-- the step after a state with nothing left keeps it -/
theorem rpStep_zero {q : ℕ} {st : RPState} (hn : st.n = 0) : (rpStep q st).2 = st := by
  simp [rpStep, hn]

/-- the state after a step: what is left is at most half the divisor, and `e` grows by `max(s, 0)` -/
theorem rpStep_next {q : ℕ} (hq : 0 < q) {st : RPState} (hn : st.n ≠ 0) :
    2 * (rpStep q st).2.n ≤ q * 2 ^ (-(rpShift st.n q)).toNat ∧
      (rpStep q st).2.e = st.e + max (rpShift st.n q) 0 := by
  have hD : 0 < (rpSplit st.n q (rpShift st.n q)).2 := (rpSplit_val st.n q (rpShift st.n q) 0 hq).1
  have h := rpRound_rem (rpSplit st.n q (rpShift st.n q)).1 (rpSplit st.n q (rpShift st.n q)).2 hD
  simp only [rpStep, hn, ↓reduceIte]
  exact ⟨h.trans (rpSplit_snd _ _ _).le, trivial⟩

/-- the shift lies in `[52 - bits(n) + bits(q), 53 - bits(n) + bits(q)]` -/
theorem rpShift_ge (n q : ℕ) : 52 - ((bitLen n : ℤ) - bitLen q) ≤ rpShift n q := by
  rcases rpShift_cases n q with h | h <;> omega

theorem rpShift_le (n q : ℕ) : rpShift n q ≤ 53 - ((bitLen n : ℤ) - bitLen q) := by
  rcases rpShift_cases n q with h | h <;> omega

/-- what is left before part `i`, for `1 ≤ q < 2^60` and `|a| ≤ 2^63`: `|a|` before the first part, below `q 2^{11}`
before the second, at most `q/2` before the others; `e` between `0` and `112 i` -/
theorem rpState_inv (a : ℤ) {q : ℕ} (hq0 : 0 < q) (hq : q < 2 ^ 60) (ha : a.natAbs ≤ 2 ^ 63) (i : ℕ) :
    (i = 0 → (rpState a q i).n ≤ 2 ^ 63) ∧ (i = 1 → (rpState a q i).n < q * 2 ^ 11) ∧
      (2 ≤ i → 2 * (rpState a q i).n ≤ q) ∧ 0 ≤ (rpState a q i).e ∧ (rpState a q i).e ≤ 112 * i := by
  have hLq : bitLen q ≤ 60 := bitLen_le hq
  have hLq1 : 1 ≤ bitLen q := bitLen_pos hq0.ne'
  induction i with
  | zero => exact ⟨fun _ => ha, by omega, by omega, le_rfl, by simp [rpState]⟩
  | succ i ih =>
    obtain ⟨h0, h1, h2, he0, he1⟩ := ih
    set st := rpState a q i with hst
    have hnext : rpState a q (i + 1) = (rpStep q st).2 := rfl
    rw [hnext]
    by_cases hn : st.n = 0
    · rw [rpStep_zero hn, hn]
      refine ⟨by omega, fun _ => by positivity, fun _ => by omega, he0, by push_cast; linarith⟩
    obtain ⟨hn2, he⟩ := rpStep_next hq0 hn
    have hLn1 : 1 ≤ bitLen st.n := bitLen_pos hn
    have hsl := rpShift_le st.n q
    have hsg := rpShift_ge st.n q
    rw [he]
    -- the shift's lower bound in each case, and with it the divisor
    have hshift : (i = 0 → -11 ≤ rpShift st.n q) ∧ (1 ≤ i → 0 ≤ rpShift st.n q) := by
      refine ⟨fun hi => ?_, fun hi => ?_⟩
      · have : bitLen st.n ≤ 64 := bitLen_le (by have := h0 hi; omega)
        omega
      · rcases Nat.lt_or_ge i 2 with hi2 | hi2
        · have hlt : st.n < 2 ^ (bitLen q + 11) := by
            have := h1 (by omega)
            have hq2 := (bitLen_bounds hq0.ne').2
            calc st.n < q * 2 ^ 11 := this
              _ < 2 ^ bitLen q * 2 ^ 11 := by gcongr
              _ = 2 ^ (bitLen q + 11) := by rw [pow_add]
          have := bitLen_le hlt
          omega
        · have hlt : st.n < 2 ^ bitLen q := by
            have := h2 hi2
            have hq2 := (bitLen_bounds hq0.ne').2
            omega
          have := bitLen_le hlt
          omega
    refine ⟨by omega, fun hi => ?_, fun hi => ?_, by omega, by push_cast; omega⟩
    · have hs := hshift.1 (by omega)
      have hk : (-(rpShift st.n q)).toNat ≤ 11 := by omega
      have : q * 2 ^ (-(rpShift st.n q)).toNat ≤ q * 2 ^ 11 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hk)
      have hq11 : 0 < q * 2 ^ 11 := by positivity
      omega
    · have hs := hshift.2 (by omega)
      have hk : (-(rpShift st.n q)).toNat = 0 := by omega
      rw [hk, pow_zero, mul_one] at hn2
      exact hn2

theorem lt_two_pow_bitLen (n : ℕ) : n < 2 ^ bitLen n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact (bitLen_bounds hn).2

/-- `split(t)` for `-11 ≤ t ≤ 53 - bits(n) + bits(q)`, `q < 2^60` and `n < 2^71`: a dividend below `2^127` and a
divisor below `2^72` -/
theorem rpSplit_bounds {n q : ℕ} {t : ℤ} (hq : q < 2 ^ 60) (hn : n < 2 ^ 71) (htl : -11 ≤ t)
    (htu : t ≤ 53 - ((bitLen n : ℤ) - bitLen q)) : (rpSplit n q t).1 < 2 ^ 127 ∧ (rpSplit n q t).2 < 2 ^ 72 := by
  have hLq : bitLen q ≤ 60 := bitLen_le hq
  unfold rpSplit
  split_ifs with ht
  · constructor
    · have hk : bitLen n + t.toNat ≤ 127 := by omega
      calc n * 2 ^ t.toNat < 2 ^ bitLen n * 2 ^ t.toNat :=
            Nat.mul_lt_mul_of_pos_right (lt_two_pow_bitLen n) (by positivity)
        _ = 2 ^ (bitLen n + t.toNat) := by rw [pow_add]
        _ ≤ 2 ^ 127 := Nat.pow_le_pow_right (by norm_num) hk
    · calc q < 2 ^ 60 := hq
        _ ≤ 2 ^ 72 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · constructor
    · calc n < 2 ^ 71 := hn
        _ ≤ 2 ^ 127 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    · have hk : (-t).toNat ≤ 11 := by omega
      calc q * 2 ^ (-t).toNat ≤ q * 2 ^ 11 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hk)
        _ < 2 ^ 60 * 2 ^ 11 := Nat.mul_lt_mul_of_pos_right hq (by positivity)
        _ ≤ 2 ^ 72 := by norm_num

/-- the eight steps of `ratio_parts` for `1 ≤ q < 2^60` and `|p| ≤ 2^63`, at a state with something left: both
splits, at `s_0` and at the shift `s`, take shifts in `[-11, 112]` and give a dividend below `2^127` and a divisor `D`
below `2^72`; the rounded quotient lies in `[2^52, 2^53]`, so it and its product with `D` are below `2^127`; and the
part's scale `2^{-(e + s)}` has an exponent in `[-1022, 1023]`, the normal range of binary64 -/
theorem rp_bounds (a : ℤ) {q : ℕ} (hq0 : 0 < q) (hq : q < 2 ^ 60) (ha : a.natAbs ≤ 2 ^ 63) {i : ℕ} (hi : i < 8)
    (hn : (rpState a q i).n ≠ 0) :
    (∀ t : ℤ, 52 - ((bitLen (rpState a q i).n : ℤ) - bitLen q) ≤ t → t ≤ rpShift (rpState a q i).n q →
        -11 ≤ t ∧ t ≤ 112 ∧ (rpSplit (rpState a q i).n q t).1 < 2 ^ 127 ∧
          (rpSplit (rpState a q i).n q t).2 < 2 ^ 72) ∧
      2 ^ 52 ≤ rpRound (rpSplit (rpState a q i).n q (rpShift (rpState a q i).n q)).1
        (rpSplit (rpState a q i).n q (rpShift (rpState a q i).n q)).2 ∧
      rpRound (rpSplit (rpState a q i).n q (rpShift (rpState a q i).n q)).1
          (rpSplit (rpState a q i).n q (rpShift (rpState a q i).n q)).2 *
        (rpSplit (rpState a q i).n q (rpShift (rpState a q i).n q)).2 < 2 ^ 127 ∧
      -1022 ≤ -((rpState a q i).e + rpShift (rpState a q i).n q) ∧
      -((rpState a q i).e + rpShift (rpState a q i).n q) ≤ 1023 := by
  obtain ⟨h0, h1, h2, he0, he1⟩ := rpState_inv a hq0 hq ha i
  set st := rpState a q i
  have hLq : bitLen q ≤ 60 := bitLen_le hq
  have hLq1 : 1 ≤ bitLen q := bitLen_pos hq0.ne'
  have hLn1 : 1 ≤ bitLen st.n := bitLen_pos hn
  have hsl := rpShift_le st.n q
  have hsg := rpShift_ge st.n q
  -- what is left is below `2^71`, and `s_0 ≥ -11`
  have hn71 : st.n < 2 ^ 71 := by
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · rcases Nat.lt_or_ge i 1 with hi1 | hi1
      · calc st.n ≤ 2 ^ 63 := h0 (by omega)
          _ < 2 ^ 71 := by norm_num
      · calc st.n < q * 2 ^ 11 := h1 (by omega)
          _ < 2 ^ 60 * 2 ^ 11 := Nat.mul_lt_mul_of_pos_right hq (by positivity)
          _ = 2 ^ 71 := by norm_num
    · have := h2 hi2
      omega
  have hs0 : -11 ≤ 52 - ((bitLen st.n : ℤ) - bitLen q) := by
    rcases Nat.lt_or_ge i 1 with hi1 | hi1
    · have : bitLen st.n ≤ 64 := bitLen_le (by have := h0 (by omega); omega)
      omega
    · rcases Nat.lt_or_ge i 2 with hi2 | hi2
      · have hlt : st.n < 2 ^ (bitLen q + 11) := by
          have hq2 := (bitLen_bounds hq0.ne').2
          calc st.n < q * 2 ^ 11 := h1 (by omega)
            _ < 2 ^ bitLen q * 2 ^ 11 := by gcongr
            _ = 2 ^ (bitLen q + 11) := by rw [pow_add]
        have := bitLen_le hlt
        omega
      · have hlt : st.n < 2 ^ bitLen q := by
          have := h2 hi2
          have hq2 := (bitLen_bounds hq0.ne').2
          omega
        have := bitLen_le hlt
        omega
  have hsplit : ∀ t : ℤ, 52 - ((bitLen st.n : ℤ) - bitLen q) ≤ t → t ≤ rpShift st.n q →
      -11 ≤ t ∧ t ≤ 112 ∧ (rpSplit st.n q t).1 < 2 ^ 127 ∧ (rpSplit st.n q t).2 < 2 ^ 72 := by
    intro t ht1 ht2
    exact ⟨by omega, by omega, rpSplit_bounds hq hn71 (by omega) (by omega)⟩
  obtain ⟨-, -, -, hD72⟩ := hsplit (rpShift st.n q) hsg le_rfl
  obtain ⟨hlo, hhi⟩ := rpShift_range hn hq0
  have hr1 : 2 ^ 52 ≤ rpRound (rpSplit st.n q (rpShift st.n q)).1 (rpSplit st.n q (rpShift st.n q)).2 := by
    unfold rpRound; split_ifs <;> omega
  have hr2 := rpRound_le hhi
  refine ⟨hsplit, hr1, ?_, by omega, by omega⟩
  calc rpRound (rpSplit st.n q (rpShift st.n q)).1 (rpSplit st.n q (rpShift st.n q)).2 *
        (rpSplit st.n q (rpShift st.n q)).2 ≤ 2 ^ 53 * (rpSplit st.n q (rpShift st.n q)).2 :=
        Nat.mul_le_mul_right _ hr2
    _ < 2 ^ 53 * 2 ^ 72 := Nat.mul_lt_mul_of_pos_left hD72 (by positivity)
    _ ≤ 2 ^ 127 := by norm_num

end ExpansionBounds
