import ExpansionBounds.DWDiv
import ExpansionBounds.MullowDigits

/-!
# `series::digits` and `series::load` in binary64
-/

/-!
## `series::digits` in binary64

A float at least `2^{p-1}` is an integer (`F_int`). The code's `r_lo`, from the least part at least 1 over the
lanes, makes every part at least 1 a multiple of `2^{16 r_lo}`, or `r_lo = 0` (`rlo_code`). `rnd(x) = (x + M) - M`,
`M = 3·2^{51}`, is an integer within `1/2` of `x` for `|x| < 2^{51}` (`magic_rnd`); `rndC` is that integer there and
the nearest one elsewhere, always within `1/2` (`rndC_err`). A step of the digit loop, `q = rnd(rem 2^{-16r})` and
`rem - q 2^{16r}`, is exact (`step_exact`), and so are sums of integers below `2^{53}` (`F_int_le`).
-/

namespace ExpansionBounds

variable (p : ℤ) [Prec_gt_0 p]

omit [Prec_gt_0 p] in
/-- a float at least `2^{p-1}` is an integer -/
theorem F_int {P : ℝ} (hP : F p P) (h : (2 : ℝ) ^ (p - 1) ≤ |P|) : ∃ z : ℤ, P = z := by
  obtain ⟨k, hk⟩ := mult_of_F p (E := 0) hP (by simpa using h)
  exact ⟨k, by simpa using hk⟩

omit [Prec_gt_0 p] in
/-- the code's `r_lo`: from a lane's value `a_min ≥ 2^{e - 1}` at or below `|P|`, `r_lo = max(0, e - 54)/16`; then a
part `P` at least 1 is a multiple of `2^{16 r_lo}`, or `r_lo = 0` -/
theorem rlo_code (hp : p = 53) {P amin : ℝ} {e : ℤ} (hP : F p P) (hle : amin ≤ |P|) (he : (2 : ℝ) ^ (e - 1) ≤ amin) :
    (max 0 (e - 54) / 16).toNat = 0 ∨ ∃ z : ℤ, P = z * 2 ^ (16 * (max 0 (e - 54) / 16).toNat) := by
  rcases lt_or_ge (max 0 (e - 54) / 16) 1 with h | h
  · left; omega
  · right
    have hm : Mult (e - 53) P := mult_of_F p hP (by rw [hp]; ring_nf; ring_nf at he; linarith)
    have hE : ((16 * (max 0 (e - 54) / 16).toNat : ℕ) : ℤ) ≤ e - 53 := by
      push_cast
      have := Int.toNat_of_nonneg (by omega : 0 ≤ max 0 (e - 54) / 16)
      omega
    obtain ⟨k, hk⟩ := hm.mono hE
    refine ⟨k, ?_⟩
    rw [hk, ← zpow_natCast]

/-- `M = 3·2^{51}`, the constant of `rnd` -/
noncomputable def magicM : ℝ := 6755399441055744

/-- `rnd(x) = RN(RN(x + M) - M)` is an integer within `1/2` of `x`, for `|x| < 2^{51}` at `p = 53` -/
theorem magic_rnd (hp : p = 53) {x : ℝ} (hx : |x| < 2 ^ 51) :
    ∃ z : ℤ, RN p (RN p (x + magicM) - magicM) = z ∧ |x - z| ≤ 1 / 2 := by
  have hM : magicM = 6755399441055744 := rfl
  -- `x + M` lies in `(2^{52}, 2^{53})`, where the floats are the integers
  have hlo : (2 : ℝ) ^ 52 < x + magicM := by rw [hM]; have := (abs_lt.mp hx).1; norm_num at this ⊢; linarith
  have hhi : x + magicM < 2 ^ 53 := by rw [hM]; have := (abs_lt.mp hx).2; norm_num at this ⊢; linarith
  have herr : |RN p (x + magicM) - (x + magicM)| ≤ (2 : ℝ) ^ (0 : ℤ) / 2 :=
    RN_err_grid_le p (by rw [abs_of_pos (by linarith), hp]; norm_num; linarith)
  rw [zpow_zero] at herr
  set y := RN p (x + magicM) with hy
  -- `y ≥ 2^{52}` is a float, so an integer
  have h52 : (2 : ℝ) ^ (52 : ℤ) ≤ y := by
    have := RN_mono p (show (2 : ℝ) ^ (52 : ℤ) ≤ x + magicM by norm_num; linarith)
    rwa [RN_of_F p (F_two_zpow p 52)] at this
  obtain ⟨k, hk⟩ : Mult 0 y :=
    mult_of_F p (F_RN p _) (by rw [abs_of_pos (lt_of_lt_of_le (by positivity) h52), hp]; norm_num at h52 ⊢; linarith)
  rw [zpow_zero, mul_one] at hk
  -- `y - M` is an integer below `2^{53}`, so a float
  have hd : |y - magicM| ≤ (2 : ℝ) ^ ((0 : ℤ) + p) := by
    rw [hp]; norm_num
    have := (abs_lt.mp hx)
    rw [abs_le]; constructor <;> linarith [(abs_le.mp herr).1, (abs_le.mp herr).2]
  have hF : F p (y - magicM) := F_of_mult_le p ⟨k - 6755399441055744, by rw [hk, hM]; push_cast; ring⟩ hd
  refine ⟨k - 6755399441055744, by rw [RN_of_F p hF, hk, hM]; push_cast; ring, ?_⟩
  have : x - ((k - 6755399441055744 : ℤ) : ℝ) = -(y - (x + magicM)) := by rw [hk, hM]; push_cast; ring
  rw [this, abs_neg]
  exact herr

/-- the code's `rnd` as an integer for `|x| < 2^{51}`, the nearest integer elsewhere -/
noncomputable def rndC (x : ℝ) : ℤ :=
  if |x| < 2 ^ 51 then ⌊RN p (RN p (x + magicM) - magicM)⌋ else round x

/-- `rndC` is the code's `rnd` where `|x| < 2^{51}` -/
theorem rndC_code (hp : p = 53) {x : ℝ} (hx : |x| < 2 ^ 51) : (rndC p x : ℝ) = RN p (RN p (x + magicM) - magicM) := by
  obtain ⟨z, hz, -⟩ := magic_rnd p hp hx
  rw [rndC, ite_eq_left hx, hz, Int.floor_intCast]

/-- `rndC` is within `1/2` of its argument -/
theorem rndC_err (hp : p = 53) (x : ℝ) : |x - rndC p x| ≤ 1 / 2 := by
  by_cases hx : |x| < 2 ^ 51
  · obtain ⟨z, hz, h⟩ := magic_rnd p hp hx
    rwa [rndC_code p hp hx, hz]
  · rw [rndC, ite_eq_right hx]
    exact abs_sub_round x

/-- an integer of size at most `2^p` is in `F` -/
theorem F_int_le {z : ℤ} (hz : |(z : ℝ)| ≤ 2 ^ p) : F p z :=
  F_of_mult_le p (E := 0) ⟨z, by simp⟩ (by simpa using hz)

/-- a step of the digit loop is exact without underflow (A2): with `y = rem 2^{-16r}`, `|y| < 2^{51}` and `q = rnd(y)`,
the code's `RN(rem 2^{-16r})` is `y` and `RN(rem - RN(q 2^{16r}))` is `rem - q 2^{16r}` -/
theorem step_exact (hp : p = 53) {rem : ℝ} (hrem : F p rem) (r : ℕ) (hy : |rem / 2 ^ (16 * r)| < 2 ^ 51) :
    RN p (rem * 2 ^ (-(16 * r : ℤ))) = rem / 2 ^ (16 * r) ∧
      RN p (rem - RN p (RN p (RN p (rem / 2 ^ (16 * r) + magicM) - magicM) * 2 ^ (16 * r))) =
        rem - rndC p (rem / 2 ^ (16 * r)) * 2 ^ (16 * r) := by
  have hS : (0 : ℝ) < 2 ^ (16 * r) := by positivity
  set y := rem / 2 ^ (16 * r) with hydef
  have hey : rem * 2 ^ (-(16 * r : ℤ)) = y := by
    rw [hydef, zpow_neg, div_eq_mul_inv, show (16 * (r : ℤ)) = ((16 * r : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hFy : F p y := by
    rw [← hey, mul_comm]
    exact F_zpow_mul p _ hrem
  refine ⟨by rw [hey, RN_of_F p hFy], ?_⟩
  rw [← rndC_code p hp hy]
  set q := rndC p y
  have hq := rndC_err p hp y
  have hFq : F p (q : ℝ) := by
    have : F p (RN p (RN p (y + magicM) - magicM)) := F_RN p _
    rwa [← rndC_code p hp hy] at this
  -- `q 2^{16r}` is a float; `y - q` is one by Sterbenz's lemma (or `q = 0`)
  have hFqS : F p ((q : ℝ) * 2 ^ (16 * r)) := by
    rw [mul_comm, ← zpow_natCast]
    exact F_zpow_mul p _ hFq
  rw [RN_of_F p hFqS]
  have hFd : F p (y - q) := by
    rcases eq_or_ne q 0 with h0 | h0
    · rw [h0, Int.cast_zero, sub_zero]; exact hFy
    have hq1 : (1 : ℝ) ≤ |(q : ℝ)| := by
      have : (1 : ℤ) ≤ |q| := Int.one_le_abs h0
      exact_mod_cast this
    rcases le_or_gt 1 |y| with hy1 | hy1
    · exact F_sub_of_near p hFy hFq (by rw [abs_sub_comm]; linarith)
    · -- `|y| < 1` and `|q| ≥ 1` within `1/2`: `|q| = 1`, and `y` is within `|q|/2` of `q`
      have hq1' : |(q : ℝ)| ≤ 1 := by
        have : |(q : ℝ)| < 2 := by
          have := abs_sub_abs_le_abs_sub (q : ℝ) y
          rw [abs_sub_comm] at this
          linarith
        have h2 : |q| < 2 := by exact_mod_cast this
        have : |q| ≤ 1 := by omega
        exact_mod_cast this
      have h := F_sub_of_near p hFq hFy (by linarith)
      have := F_neg p h
      rwa [neg_sub] at this
  have e : rem - (q : ℝ) * 2 ^ (16 * r) = 2 ^ ((16 * r : ℕ) : ℤ) * (y - q) := by
    rw [zpow_natCast, hydef]; field_simp
  rw [e, RN_of_F p (F_zpow_mul p _ hFd)]

end ExpansionBounds

/-!
## `series::digits` on one lane, in binary64

The code's loop, each operation rounded: a part's remainder after `n` of its levels (`cRem`), the digit sums over the
parts (`cD`), and the carry into balanced digits (`cCarry`, `cDig`). With each scaled part a float below
`2^{16 r_hi + 16}`, every operation but the rounding to an integer `RN(x + M)` of `rnd` is exact without underflow
(A2), and the loop computes the model of `MullowDigits` with `rnd = rndC` (`cRem_eq`, `cD_eq`, `cCarry_eq`, `cDig_eq`).
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) [Prec_gt_0 p]

/-- the code's `rnd(rem 2^{-16r})` -/
noncomputable def cq (rem : ℝ) (r : ℕ) : ℝ :=
  RN p (RN p (RN p (rem * 2 ^ (-(16 * r : ℤ))) + magicM) - magicM)

/-- the code's remainder of a part after `n` levels from `r_hi` down -/
noncomputable def cRem (P : ℝ) (rhi : ℕ) : ℕ → ℝ
  | 0 => P
  | n + 1 => RN p (cRem P rhi n - RN p (cq p (cRem P rhi n) (rhi - n) * 2 ^ (16 * (rhi - n))))

/-- the model's digit of a part at level `r`, levels `r_lo..=r_hi` -/
noncomputable def qd (P : ℝ) (rhi rlo r : ℕ) : ℤ :=
  if rlo ≤ r ∧ r ≤ rhi then rndC p (extRem (rndC p) P rhi (rhi - r) / 2 ^ (16 * r)) else 0

variable {p}

/-- every level's argument of `rnd` is below `2^{16}` -/
theorem lvl_range (hp : p = 53) {P : ℝ} {rhi : ℕ} (hP : |P| < 2 ^ (16 * rhi + 16)) (n : ℕ) :
    |extRem (rndC p) P rhi n / 2 ^ (16 * (rhi - n))| < 2 ^ 16 := by
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (16 * (rhi - n))), div_lt_iff₀ (by positivity), ← pow_add]
  rcases n with _ | m
  · simpa [extRem, add_comm] using hP
  · have h := extRem_le (rndC_err p hp) P rhi m
    have h2 : (2 : ℝ) ^ (16 * (rhi - m)) ≤ 2 ^ (16 + 16 * (rhi - (m + 1))) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (0 : ℝ) < 2 ^ (16 + 16 * (rhi - (m + 1))) := by positivity
    linarith

/-- the code's remainder is the model's, and its digit the model's `rndC` -/
theorem cRem_eq (hp : p = 53) {P : ℝ} (hF : F p P) {rhi : ℕ} (hP : |P| < 2 ^ (16 * rhi + 16)) (n : ℕ) :
    cRem p P rhi n = extRem (rndC p) P rhi n ∧
      cq p (cRem p P rhi n) (rhi - n) = rndC p (extRem (rndC p) P rhi n / 2 ^ (16 * (rhi - n))) := by
  have hy : ∀ n, |extRem (rndC p) P rhi n / 2 ^ (16 * (rhi - n))| < 2 ^ 51 := fun n =>
    (lvl_range hp hP n).trans (by norm_num)
  -- the model's remainders are floats
  have hFr : ∀ n, cRem p P rhi n = extRem (rndC p) P rhi n → F p (extRem (rndC p) P rhi n) := fun n h => by
    rcases n with _ | m
    · simpa [extRem] using hF
    · rw [← h, cRem]; exact F_RN p _
  have hq : ∀ n, cRem p P rhi n = extRem (rndC p) P rhi n →
      cq p (cRem p P rhi n) (rhi - n) = rndC p (extRem (rndC p) P rhi n / 2 ^ (16 * (rhi - n))) := fun n h => by
    rw [cq, h, (step_exact p hp (hFr n h) (rhi - n) (hy n)).1, ← rndC_code p hp (hy n)]
  induction n with
  | zero => exact ⟨rfl, hq 0 rfl⟩
  | succ n ih =>
    have e : cRem p P rhi (n + 1) = extRem (rndC p) P rhi (n + 1) := by
      rw [cRem, ih.2, rndC_code p hp (hy n), ih.1, (step_exact p hp (hFr n ih.1) (rhi - n) (hy n)).2, extRem]
    exact ⟨e, hq (n + 1) e⟩

/-- the model's digits of a part: `|q| ≤ 2^{16}` -/
theorem qd_le (hp : p = 53) {P : ℝ} {rhi : ℕ} (hP : |P| < 2 ^ (16 * rhi + 16)) (rlo r : ℕ) :
    |qd p P rhi rlo r| ≤ 2 ^ 16 := by
  unfold qd
  split_ifs with h
  · have h1 := lvl_range hp hP (rhi - r)
    rw [show rhi - (rhi - r) = r by omega] at h1
    have h2 := rndC_err p hp (extRem (rndC p) P rhi (rhi - r) / 2 ^ (16 * r))
    have h3 : |(rndC p (extRem (rndC p) P rhi (rhi - r) / 2 ^ (16 * r)) : ℝ)| < 2 ^ 16 + 1 := by
      have := abs_sub_abs_le_abs_sub (rndC p (extRem (rndC p) P rhi (rhi - r) / 2 ^ (16 * r)) : ℝ)
        (extRem (rndC p) P rhi (rhi - r) / 2 ^ (16 * r))
      rw [abs_sub_comm] at this
      linarith
    have h4 : |rndC p (extRem (rndC p) P rhi (rhi - r) / 2 ^ (16 * r))| < 2 ^ 16 + 1 := by exact_mod_cast h3
    omega
  · simp

/-- the model's digits of a part over its levels: the part less its remainder -/
theorem extRem_tele (rnd : ℝ → ℤ) (P : ℝ) (rhi : ℕ) :
    ∀ n ≤ rhi + 1, P - extRem rnd P rhi n =
      ∑ r ∈ Ico (rhi + 1 - n) (rhi + 1), (rnd (extRem rnd P rhi (rhi - r) / 2 ^ (16 * r)) : ℝ) * 2 ^ (16 * r) := by
  intro n
  induction n with
  | zero => intro _; simp [extRem]
  | succ n ih =>
    intro hn
    rw [show rhi + 1 - (n + 1) = rhi - n by omega, sum_eq_sum_Ico_succ_bot (by omega),
      show rhi - n + 1 = rhi + 1 - n by omega, ← ih (by omega), show rhi - (rhi - n) = n by omega, extRem]
    ring

omit [Prec_gt_0 p] in
/-- a part's digits over `r < t`, levels `r_lo..=r_hi`, `r_hi < t`: the part less its last remainder -/
theorem qd_sum (P : ℝ) {rhi rlo t : ℕ} (hr : rlo ≤ rhi) (ht : rhi < t) :
    ∑ r ∈ range t, (qd p P rhi rlo r : ℝ) * 2 ^ (16 * r) = P - extRem (rndC p) P rhi (rhi - rlo + 1) := by
  rw [extRem_tele (rndC p) P rhi _ (by omega), show rhi + 1 - (rhi - rlo + 1) = rlo by omega]
  have e : ∀ r ∈ range t, (qd p P rhi rlo r : ℝ) * 2 ^ (16 * r) =
      if r ∈ Ico rlo (rhi + 1) then (rndC p (extRem (rndC p) P rhi (rhi - r) / 2 ^ (16 * r)) : ℝ) * 2 ^ (16 * r)
      else 0 := fun r _ => by
    unfold qd
    by_cases h : rlo ≤ r ∧ r ≤ rhi
    · rw [ite_eq_left h, ite_eq_left (mem_Ico.mpr ⟨h.1, by omega⟩)]
    · rw [ite_eq_right h, ite_eq_right (fun hm => h (by rw [mem_Ico] at hm; omega))]; simp
  rw [sum_congr rfl e, sum_ite_mem, inter_eq_right.mpr]
  intro r hr'
  rw [mem_Ico] at hr'
  exact mem_range.mpr (by omega)

variable (p) in
/-- the code's digit sums at level `r` over the first `j` parts (a skipped part adds nothing) -/
noncomputable def cD (P : ℕ → ℝ) (rhi rlo : ℕ → ℕ) (sk : ℕ → Prop) [DecidablePred sk] (r : ℕ) : ℕ → ℝ
  | 0 => 0
  | j + 1 =>
    if ¬ sk j ∧ min (rlo j) (rhi j) ≤ r ∧ r ≤ rhi j then
      RN p (cD P rhi rlo sk r j + cq p (cRem p (P j) (rhi j) (rhi j - r)) r)
    else cD P rhi rlo sk r j

variable (p) in
/-- the model's digit sums -/
noncomputable def mD (P : ℕ → ℝ) (rhi rlo : ℕ → ℕ) (sk : ℕ → Prop) [DecidablePred sk] (j r : ℕ) : ℤ :=
  ∑ i ∈ range j, if sk i then 0 else qd p (P i) (rhi i) (min (rlo i) (rhi i)) r

/-- the code's digit sums are the model's, for `j ≤ 8` parts -/
theorem cD_eq (hp : p = 53) {P : ℕ → ℝ} {rhi rlo : ℕ → ℕ} {sk : ℕ → Prop} [DecidablePred sk]
    (hF : ∀ i, F p (P i)) (hP : ∀ i, |P i| < 2 ^ (16 * rhi i + 16)) (r : ℕ) :
    ∀ j ≤ 8, cD p P rhi rlo sk r j = mD p P rhi rlo sk j r ∧ |mD p P rhi rlo sk j r| ≤ j * 2 ^ 16 := by
  intro j
  induction j with
  | zero => intro _; simp [cD, mD]
  | succ j ih =>
    intro hj
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hm : mD p P rhi rlo sk (j + 1) r =
        mD p P rhi rlo sk j r + if sk j then 0 else qd p (P j) (rhi j) (min (rlo j) (rhi j)) r := by
      simp only [mD, sum_range_succ]
    have hb : |(if sk j then 0 else qd p (P j) (rhi j) (min (rlo j) (rhi j)) r)| ≤ 2 ^ 16 := by
      split_ifs
      · simp
      · exact qd_le hp (hP j) _ r
    have hsum : |mD p P rhi rlo sk (j + 1) r| ≤ (j + 1 : ℕ) * 2 ^ 16 := by
      rw [hm]
      calc _ ≤ |mD p P rhi rlo sk j r| + |(if sk j then 0 else qd p (P j) (rhi j) (min (rlo j) (rhi j)) r)| :=
            abs_add_le _ _
        _ ≤ j * 2 ^ 16 + 2 ^ 16 := add_le_add ih2 hb
        _ = (j + 1 : ℕ) * 2 ^ 16 := by push_cast; ring
    refine ⟨?_, hsum⟩
    rw [hm, cD]
    by_cases hc : ¬ sk j ∧ min (rlo j) (rhi j) ≤ r ∧ r ≤ rhi j
    · rw [ite_eq_left hc, ih1]
      have h2 := (cRem_eq hp (hF j) (hP j) (rhi j - r)).2
      rw [show rhi j - (rhi j - r) = r by omega] at h2
      rw [h2]
      have hq : qd p (P j) (rhi j) (min (rlo j) (rhi j)) r =
          rndC p (extRem (rndC p) (P j) (rhi j) (rhi j - r) / 2 ^ (16 * r)) := by
        unfold qd; rw [ite_eq_left ⟨hc.2.1, hc.2.2⟩]
      rw [ite_eq_right hc.1, ← hq]
      have hF' : F p ((mD p P rhi rlo sk j r + qd p (P j) (rhi j) (min (rlo j) (rhi j)) r : ℤ) : ℝ) := by
        refine F_int_le p ?_
        rw [hm, ite_eq_right hc.1] at hsum
        have : |((mD p P rhi rlo sk j r + qd p (P j) (rhi j) (min (rlo j) (rhi j)) r : ℤ) : ℝ)| ≤ 9 * 2 ^ 16 := by
          have h9 : ((j + 1 : ℕ) : ℤ) * 2 ^ 16 ≤ 9 * 2 ^ 16 := by push_cast; omega
          exact_mod_cast hsum.trans h9
        exact this.trans (by rw [hp]; norm_num)
      push_cast at hF' ⊢
      exact RN_of_F p hF'
    · rw [ite_eq_right hc, ih1]
      by_cases hs : sk j
      · rw [ite_eq_left hs]; simp
      · rw [ite_eq_right hs]
        have : ¬ (min (rlo j) (rhi j) ≤ r ∧ r ≤ rhi j) := fun h => hc ⟨hs, h⟩
        unfold qd; rw [ite_eq_right this]; simp

/-- the code's `rnd(rem 2^{-16r})` of a float is `rndC(rem/2^{16r})` where that is below `2^{51}` -/
theorem cq_eq (hp : p = 53) {rem : ℝ} (hF : F p rem) {r : ℕ} (hy : |rem / 2 ^ (16 * r)| < 2 ^ 51) :
    cq p rem r = rndC p (rem / 2 ^ (16 * r)) := by
  rw [cq, (step_exact p hp hF r hy).1, ← rndC_code p hp hy]

variable (p) in
/-- the code's carry into level `r` -/
noncomputable def cCarry (D : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | r + 1 => cq p (RN p (D r + cCarry D r)) 1

variable (p) in
/-- the code's balanced digit at level `r` -/
noncomputable def cDig (D : ℕ → ℝ) (r : ℕ) : ℝ :=
  RN p (RN p (D r + cCarry p D r) - RN p (cCarry p D (r + 1) * 2 ^ 16))

/-- the code's carries are the model's, at most `2^{35}`, for digit sums at most `2^{50}` -/
theorem cCarry_eq (hp : p = 53) {D : ℕ → ℝ} {Dz : ℕ → ℤ} (hD : ∀ r, D r = Dz r) (hb : ∀ r, |Dz r| ≤ 2 ^ 50) :
    ∀ r, cCarry p D r = carryIn (rndC p) Dz r ∧ |carryIn (rndC p) Dz r| ≤ 2 ^ 35 := by
  intro r
  induction r with
  | zero => simp [cCarry, carryIn]
  | succ r ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hv : |((Dz r + carryIn (rndC p) Dz r : ℤ) : ℝ)| ≤ 2 ^ 50 + 2 ^ 35 := by
      have : |Dz r + carryIn (rndC p) Dz r| ≤ 2 ^ 50 + 2 ^ 35 := (abs_add_le _ _).trans (add_le_add (hb r) ih2)
      exact_mod_cast this
    have hF : F p ((Dz r + carryIn (rndC p) Dz r : ℤ) : ℝ) := F_int_le p (hv.trans (by rw [hp]; norm_num))
    have hRN : RN p (D r + cCarry p D r) = ((Dz r + carryIn (rndC p) Dz r : ℤ) : ℝ) := by
      rw [hD, ih1, ← RN_of_F p hF]; push_cast; rfl
    have hy : |((Dz r + carryIn (rndC p) Dz r : ℤ) : ℝ) / 2 ^ (16 * 1)| < 2 ^ 51 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (16 * 1)), div_lt_iff₀ (by positivity)]
      have : (2 : ℝ) ^ 50 + 2 ^ 35 < 2 ^ 51 * 2 ^ (16 * 1) := by norm_num
      linarith
    have e : cCarry p D (r + 1) = carryIn (rndC p) Dz (r + 1) := by
      rw [cCarry, hRN, cq_eq hp hF hy, carryIn]
    refine ⟨e, ?_⟩
    have h1 := rndC_err p hp (((Dz r + carryIn (rndC p) Dz r : ℤ) : ℝ) / 2 ^ 16)
    have h2 : |(carryIn (rndC p) Dz (r + 1) : ℝ)| < 2 ^ 35 + 1 := by
      rw [carryIn]
      have := abs_sub_abs_le_abs_sub (rndC p (((Dz r + carryIn (rndC p) Dz r : ℤ) : ℝ) / 2 ^ 16) : ℝ)
        (((Dz r + carryIn (rndC p) Dz r : ℤ) : ℝ) / 2 ^ 16)
      rw [abs_sub_comm] at this
      have h3 : |((Dz r + carryIn (rndC p) Dz r : ℤ) : ℝ) / 2 ^ 16| ≤ (2 ^ 50 + 2 ^ 35) / 2 ^ 16 := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 16)]
        exact div_le_div_of_nonneg_right hv (by positivity)
      have h4 : ((2 : ℝ) ^ 50 + 2 ^ 35) / 2 ^ 16 ≤ 2 ^ 35 - 1 := by norm_num
      linarith
    have : |carryIn (rndC p) Dz (r + 1)| < 2 ^ 35 + 1 := by exact_mod_cast h2
    omega

/-- the code's balanced digits are the model's -/
theorem cDig_eq (hp : p = 53) {D : ℕ → ℝ} {Dz : ℕ → ℤ} (hD : ∀ r, D r = Dz r) (hb : ∀ r, |Dz r| ≤ 2 ^ 50)
    (r : ℕ) : cDig p D r = balDig (rndC p) Dz r := by
  obtain ⟨c1, c2⟩ := cCarry_eq hp hD hb r
  have hv : |((Dz r + carryIn (rndC p) Dz r : ℤ) : ℝ)| ≤ 2 ^ 50 + 2 ^ 35 := by
    have : |Dz r + carryIn (rndC p) Dz r| ≤ 2 ^ 50 + 2 ^ 35 := (abs_add_le _ _).trans (add_le_add (hb r) c2)
    exact_mod_cast this
  have hF : F p ((Dz r + carryIn (rndC p) Dz r : ℤ) : ℝ) := F_int_le p (hv.trans (by rw [hp]; norm_num))
  have hRN : RN p (D r + cCarry p D r) = ((Dz r + carryIn (rndC p) Dz r : ℤ) : ℝ) := by
    rw [hD, c1, ← RN_of_F p hF]; push_cast; rfl
  have hy : |((Dz r + carryIn (rndC p) Dz r : ℤ) : ℝ) / 2 ^ (16 * 1)| < 2 ^ 51 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (16 * 1)), div_lt_iff₀ (by positivity)]
    have : (2 : ℝ) ^ 50 + 2 ^ 35 < 2 ^ 51 * 2 ^ (16 * 1) := by norm_num
    linarith
  have hc : cCarry p D (r + 1) = RN p (RN p (((Dz r + carryIn (rndC p) Dz r : ℤ) : ℝ) / 2 ^ (16 * 1) + magicM) -
      magicM) := by
    rw [cCarry, hRN, cq, (step_exact p hp hF 1 hy).1]
  rw [cDig, hRN, hc, (step_exact p hp hF 1 hy).2, balDig, carryIn]
  push_cast
  norm_num

end ExpansionBounds

/-!
## `series::load`: a block's scaled coefficients

A coefficient `a = ∑ a_i`, each part at most `u` times the one before, with `2^{e-1} ≤ |a_0| < 2^e`, scaled to
`α = 2^k a`, `W - h ≤ e + k ≤ W` (the block's frame and spread), has `|α|` in `[2^{W-h-1}(1 - 2u), 2^W(1 + 2u)]`
(`alpha_bounds`). The code's `r_hi` puts every scaled part below `2^{16 r_hi + 16}` (`rhi_code`); the scaling by
`2^{k/2}` then `2^{k - k/2}`, `/` truncating as in Rust, is exact (`scale_exact`), and the pair's read-out exponent
less the `16 q_0` of the dropped weights cancels the two scales (`scale_sum`).
-/

namespace ExpansionBounds

open Finset

/-- the tail of a part sequence, each part at most `u` times the one before -/
theorem abs_tail_le {u : ℝ} (hu0 : 0 ≤ u) {a : ℕ → ℝ} (hord : ∀ i, |a (i + 1)| ≤ u * |a i|) (n : ℕ) :
    ∑ i ∈ range n, |a (i + 1)| ≤ u * ∑ i ∈ range (n + 1), |a i| :=
  calc ∑ i ∈ range n, |a (i + 1)| ≤ ∑ i ∈ range n, u * |a i| := sum_le_sum fun i _ => hord i
    _ = u * ∑ i ∈ range n, |a i| := by rw [mul_sum]
    _ ≤ u * ∑ i ∈ range (n + 1), |a i| := mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.le_succ n)) fun i _ _ => abs_nonneg (a i)) hu0

/-- a part sequence, each at most `u` times the one before, has `(1 - u) ∑ |a_i| ≤ |a_0|` -/
theorem abs_parts_le {u : ℝ} (hu0 : 0 ≤ u) {a : ℕ → ℝ} (hord : ∀ i, |a (i + 1)| ≤ u * |a i|) (n : ℕ) :
    (1 - u) * ∑ i ∈ range (n + 1), |a i| ≤ |a 0| := by
  have h := abs_tail_le hu0 hord n
  have e := sum_range_succ' (fun i => |a i|) n
  rw [e] at h ⊢
  nlinarith [h]

/-- a scaled coefficient's bounds: `2^{W-h-1}(1 - 2u) ≤ |α| ≤ 2^W(1 + 2u)` -/
theorem alpha_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 4) {a : ℕ → ℝ} (hord : ∀ i, |a (i + 1)| ≤ u * |a i|)
    {np : ℕ} (hnp : 1 ≤ np) {e k : ℤ} (he1 : (2 : ℝ) ^ (e - 1) ≤ |a 0|) (he2 : |a 0| < 2 ^ e) {W h : ℕ}
    (hWh : h + 1 ≤ W) (hk1 : ((W - h : ℕ) : ℤ) ≤ e + k) (hk2 : e + k ≤ W) :
    (2 : ℝ) ^ (W - h - 1) * (1 - 2 * u) ≤ |(2 : ℝ) ^ k * ∑ i ∈ range np, a i| ∧
      |(2 : ℝ) ^ k * ∑ i ∈ range np, a i| ≤ 2 ^ W * (1 + 2 * u) := by
  obtain ⟨n, rfl⟩ : ∃ n, np = n + 1 := ⟨np - 1, by omega⟩
  have hK : (0 : ℝ) < 2 ^ k := by positivity
  -- the tail is at most `u|a_0|/(1 - u) ≤ 2u|a_0|`
  have hT := abs_parts_le hu0 hord n
  have hsum : |∑ i ∈ range (n + 1), a i - a 0| ≤ 2 * u * |a 0| := by
    rw [sum_range_succ', add_sub_cancel_right]
    have h1 : |∑ i ∈ range n, a (i + 1)| ≤ ∑ i ∈ range n, |a (i + 1)| := abs_sum_le_sum_abs _ _
    have h2 := sum_range_succ' (fun i => |a i|) n
    have h3 := abs_tail_le hu0 hord n
    have h4 : ∑ i ∈ range (n + 1), |a i| ≤ 2 * |a 0| := by nlinarith [abs_nonneg (a 0)]
    nlinarith [abs_nonneg (a 0)]
  have hlo : |a 0| * (1 - 2 * u) ≤ |∑ i ∈ range (n + 1), a i| := by
    have := abs_sub_abs_le_abs_sub (a 0) (∑ i ∈ range (n + 1), a i)
    rw [abs_sub_comm] at this
    nlinarith
  have hhi : |∑ i ∈ range (n + 1), a i| ≤ |a 0| * (1 + 2 * u) := by
    have := abs_add_le (∑ i ∈ range (n + 1), a i - a 0) (a 0)
    rw [sub_add_cancel] at this
    nlinarith
  rw [abs_mul, abs_of_pos hK]
  have hc : 0 ≤ 1 - 2 * u := by linarith
  constructor
  · -- `2^{W-h-1} ≤ 2^{e-1+k} ≤ 2^k |a_0|`
    have hz : (2 : ℝ) ^ (W - h - 1) ≤ 2 ^ k * |a 0| := by
      calc (2 : ℝ) ^ (W - h - 1) = 2 ^ (((W - h - 1 : ℕ) : ℤ)) := (zpow_natCast 2 _).symm
        _ ≤ 2 ^ (k + (e - 1)) := zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 2 ^ k * 2 ^ (e - 1) := zpow_add₀ two_ne_zero _ _
        _ ≤ 2 ^ k * |a 0| := by gcongr
    calc (2 : ℝ) ^ (W - h - 1) * (1 - 2 * u) ≤ 2 ^ k * |a 0| * (1 - 2 * u) := by gcongr
      _ ≤ 2 ^ k * |∑ i ∈ range (n + 1), a i| := by rw [mul_assoc]; gcongr
  · have hz : 2 ^ k * |a 0| ≤ (2 : ℝ) ^ W := by
      calc 2 ^ k * |a 0| ≤ 2 ^ k * 2 ^ e := by gcongr
        _ = 2 ^ (k + e) := (zpow_add₀ two_ne_zero _ _).symm
        _ ≤ 2 ^ ((W : ℕ) : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 2 ^ W := zpow_natCast 2 _
    calc 2 ^ k * |∑ i ∈ range (n + 1), a i| ≤ 2 ^ k * (|a 0| * (1 + 2 * u)) := by gcongr
      _ = 2 ^ k * |a 0| * (1 + 2 * u) := by ring
      _ ≤ 2 ^ W * (1 + 2 * u) := by gcongr

/-- the code's `r_hi = min(t - 1, ⌊max(0, e - 1)/16⌋)` from `a_max < 2^e`, `e ≤ 16t`, puts each lane's part below
`2^{16 r_hi + 16}`, and `r_hi < t` -/
theorem rhi_code {P amax : ℝ} {e : ℤ} {t : ℕ} (ht : 1 ≤ t) (hP : |P| ≤ amax) (ha : amax < 2 ^ e)
    (he : e ≤ 16 * t) :
    |P| < 2 ^ (16 * min (t - 1) (max 0 (e - 1) / 16).toNat + 16) ∧ min (t - 1) (max 0 (e - 1) / 16).toNat < t := by
  refine ⟨?_, by omega⟩
  have hle : e ≤ ((16 * min (t - 1) (max 0 (e - 1) / 16).toNat + 16 : ℕ) : ℤ) := by
    have h0 : 0 ≤ max 0 (e - 1) / 16 := by omega
    have h1 := Int.toNat_of_nonneg h0
    rcases le_total (t - 1) (max 0 (e - 1) / 16).toNat with h | h
    · rw [min_eq_left h]; push_cast [Nat.cast_sub ht]; omega
    · rw [min_eq_right h]; push_cast; omega
  calc |P| ≤ amax := hP
    _ < 2 ^ e := ha
    _ ≤ 2 ^ (((16 * min (t - 1) (max 0 (e - 1) / 16).toNat + 16 : ℕ) : ℤ)) := zpow_le_zpow_right₀ (by norm_num) hle
    _ = _ := zpow_natCast 2 _

variable (p : ℤ) [Prec_gt_0 p]

/-- the code's scaling by `2^{k/2}` then `2^{k - k/2}`, `/` truncating as in Rust (`Int.tdiv`), is exact, as neither
step underflows (A2) -/
theorem scale_exact {x : ℝ} (hx : F p x) (k : ℤ) :
    RN p (RN p (x * 2 ^ (k.tdiv 2)) * 2 ^ (k - k.tdiv 2)) = x * 2 ^ k := by
  have h1 : F p (x * 2 ^ (k.tdiv 2)) := by rw [mul_comm]; exact F_zpow_mul p _ hx
  rw [RN_of_F p h1]
  have h2 : x * 2 ^ (k.tdiv 2) * 2 ^ (k - k.tdiv 2) = x * 2 ^ k := by
    rw [mul_assoc, ← zpow_add₀ two_ne_zero]; ring_nf
  rw [h2, RN_of_F p (by rw [mul_comm]; exact F_zpow_mul p _ hx)]

omit [Prec_gt_0 p] in
/-- the pair's scales cancel on output index `m`: `k_i = s(o_a + i) + W - f_a`, `k'_j = s(o_b + j) + W - f_b` and the
read-out's exponent less the `16 q_0` of the dropped weights, `e = f_a + f_b - 2W - s(o_a + o_b + m) + e_2`, sum to
`e_2` for `i + j = m` -/
theorem scale_sum (s oa ob W fa fb e2 : ℤ) {i j m : ℕ} (h : i + j = m) :
    (s * (oa + i) + W - fa) + (s * (ob + j) + W - fb) + (fa + fb - 2 * W - s * (oa + ob + m) + e2) = e2 := by
  have : (i : ℤ) + j = m := by exact_mod_cast h
  rw [← this]; ring

end ExpansionBounds
