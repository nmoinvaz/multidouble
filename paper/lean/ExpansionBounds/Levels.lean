import ExpansionBounds.Renorm

/-!
# Lemma 11: levels

A run on levels `s_0, …, s_n` that start at zero and change only by (i) assignments `s_m ← y` to a zero level,
(ii) calls `dep(s, l, t)` and (iii) roundings `s_n ← RN(s_n + y)` for real `y`. Besides the levels, the state keeps
the totals the proof sums: of everything put into each level, of the carries out of it, and of the rounding errors at
level `n`, with the counts of `TwoSum`s and roundings. The run lists every state it passes through, inside the deps
too, which is what "at every moment" ranges over.
-/

namespace ExpansionBounds

open Finset

/-- an operation of the run: (i) `assign m y` is `s_m ← y`, (ii) `dep l t` is `dep(s, l, t)`, (iii) `round y` is
`s_n ← RN(s_n + y)` -/
inductive LOp
  | assign (m : ℕ) (y : ℝ)
  | dep (l : ℕ) (t : ℝ)
  | round (y : ℝ)

/-- the levels, and the totals the proof of Lemma 11 sums -/
structure LState where
  /-- the levels `s_0, …, s_n` -/
  s : ℕ → ℝ
  /-- the total of `|·|` put into each level: assigned, deposited, carried in and, at level `n`, the `y` of (iii) -/
  inA : ℕ → ℝ
  /-- the total of the carries out of each level -/
  outA : ℕ → ℝ
  /-- `∑ |r|` over the rounding errors `r = z - RN(z)` at level `n` -/
  rA : ℝ
  /-- `∑ r` -/
  rS : ℝ
  /-- the part of each `A_m` done -/
  adone : ℕ → ℝ
  /-- the `TwoSum`s done at each level -/
  cnt : ℕ → ℕ
  /-- the roundings done at level `n` -/
  qcnt : ℕ
  /-- the signed sum of the `y` of (i) and (iii) and the `t` of (ii) done -/
  Y : ℝ
  /-- every assignment done was to a zero level -/
  ok : Prop

/-- the state before the run -/
def LState.init : LState := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, True⟩

variable (p : ℤ) (n : ℕ)

/-- (i) `s_m ← y` -/
noncomputable def assignS (m : ℕ) (y : ℝ) (st : LState) : LState :=
  { st with
    s := Function.update st.s m y
    inA := Function.update st.inA m (st.inA m + |y|)
    adone := Function.update st.adone m (st.adone m + |y|)
    Y := st.Y + y
    ok := st.ok ∧ st.s m = 0 }

/-- a `TwoSum` of a dep at level `m`, taking `e` in; the carry out, `(twoSum p (st.s m) e).2`, goes on -/
noncomputable def twoAt (m : ℕ) (e : ℝ) (st : LState) : LState :=
  { st with
    s := Function.update st.s m (twoSum p (st.s m) e).1
    inA := Function.update st.inA m (st.inA m + |e|)
    outA := Function.update st.outA m (st.outA m + |(twoSum p (st.s m) e).2|)
    cnt := Function.update st.cnt m (st.cnt m + 1) }

/-- `s_n ← RN(s_n + y)`: (iii), or the last step of a dep -/
noncomputable def roundN (y : ℝ) (st : LState) : LState :=
  { st with
    s := Function.update st.s n (RN p (st.s n + y))
    inA := Function.update st.inA n (st.inA n + |y|)
    rA := st.rA + |RN p (st.s n + y) - (st.s n + y)|
    rS := st.rS + (st.s n + y - RN p (st.s n + y))
    qcnt := st.qcnt + 1 }

/-- a dep from level `m`, `k = n - m` `TwoSum`s before level `n`: the states after each step, and the last -/
noncomputable def depRun : ℕ → ℕ → ℝ → LState → List LState × LState
  | 0, _, e, st => ([roundN p n e st], roundN p n e st)
  | k + 1, m, e, st =>
    (twoAt p m e st :: (depRun k (m + 1) (twoSum p (st.s m) e).2 (twoAt p m e st)).1,
      (depRun k (m + 1) (twoSum p (st.s m) e).2 (twoAt p m e st)).2)

/-- the state a dep or a rounding (iii) starts from, with its input counted -/
def entering (l : ℕ) (t : ℝ) (st : LState) : LState :=
  { st with
    adone := Function.update st.adone l (st.adone l + |t|)
    Y := st.Y + t }

/-- an operation: the states after each of its steps, and the last -/
noncomputable def stepOp : LOp → LState → List LState × LState
  | .assign m y, st => ([assignS m y st], assignS m y st)
  | .dep l t, st => depRun p n (n - l) l t (entering l t st)
  | .round y, st => ([roundN p n y (entering n y st)], roundN p n y (entering n y st))

/-- the run: every state it passes through, and the last -/
noncomputable def runOps : List LOp → LState → List LState × LState
  | [], st => ([], st)
  | o :: os, st => ((stepOp p n o st).1 ++ (runOps os (stepOp p n o st).2).1, (runOps os (stepOp p n o st).2).2)

/-- an operation's part of `A_m`: `|y|` for (i) at level `m`, `|t|` for a dep with `l = m`, `|y|` for (iii) if
`m = n` -/
def opA (m : ℕ) : LOp → ℝ
  | .assign k y => if k = m then |y| else 0
  | .dep l t => if l = m then |t| else 0
  | .round y => if m = n then |y| else 0

/-- an operation's `TwoSum`s at a level `m < n` -/
def opT (m : ℕ) : LOp → ℕ
  | .dep l _ => if l ≤ m then 1 else 0
  | _ => 0

/-- an operation's roundings at level `n` -/
def opQ : LOp → ℕ
  | .assign _ _ => 0
  | _ => 1

/-- an operation's input, with its sign -/
def opY : LOp → ℝ
  | .assign _ y => y
  | .dep _ t => t
  | .round y => y

/-- `A_m` -/
noncomputable def opsA (ops : List LOp) (m : ℕ) : ℝ := (ops.map (opA n m)).sum

/-- `T_m` -/
def opsT (ops : List LOp) (m : ℕ) : ℕ := (ops.map (opT m)).sum

/-- `Q` -/
def opsQ (ops : List LOp) : ℕ := (ops.map opQ).sum

/-- `Y` -/
noncomputable def opsY (ops : List LOp) : ℝ := (ops.map opY).sum

/-- an operation of the lemma: at a level at most `n`, the assigned or deposited value in `F p` -/
def LOp.wf : LOp → Prop
  | .assign m y => m ≤ n ∧ F p y
  | .dep l t => l ≤ n ∧ F p t
  | .round _ => True

/-- `D_0 = A_0` and `D_{m+1} = A_{m+1} + C_m` -/
noncomputable def levD (A : ℕ → ℝ) (T : ℕ → ℕ) (uu : ℝ) : ℕ → ℝ
  | 0 => A 0
  | m + 1 => A (m + 1) + T m * uu * levD A T uu m / (1 - T m * uu)

/-- `C_m = T_m u D_m / (1 - T_m u)` -/
noncomputable def levC (A : ℕ → ℝ) (T : ℕ → ℕ) (uu : ℝ) (m : ℕ) : ℝ :=
  T m * uu * levD A T uu m / (1 - T m * uu)

/-- `X_m = D_m / (1 - T_m u)` for `m < n` -/
noncomputable def levX (A : ℕ → ℝ) (T : ℕ → ℕ) (uu : ℝ) (m : ℕ) : ℝ := levD A T uu m / (1 - T m * uu)

/-- the carries into level `k`: out of level `k - 1`, none into level `0` -/
def prevOut (st : LState) (k : ℕ) : ℝ := if k = 0 then 0 else st.outA (k - 1)

/-- the bounds the proof keeps, with `w` more on its way into level `j` (a carry or a deposit) -/
def BndE (j : ℕ) (w : ℝ) (st : LState) : Prop :=
  (∀ k, 0 ≤ st.inA k ∧ 0 ≤ st.outA k) ∧ 0 ≤ st.rA ∧
  (∀ m < n, st.outA m ≤ (st.cnt m : ℝ) * u p * (st.inA m + st.outA m) ∧ |st.s m| ≤ st.inA m + st.outA m) ∧
  st.rA ≤ (st.qcnt : ℝ) * u p * (st.inA n + st.rA) ∧ |st.s n| ≤ st.inA n + st.rA ∧
  ∀ k ≤ n, st.inA k + (if k = j then w else 0) ≤ st.adone k + prevOut st k

/-- the bounds at every moment -/
def Bnd (st : LState) : Prop := BndE p n 0 0 st

/-- the invariant between operations -/
def Inv (st : LState) : Prop :=
  st.ok → Bnd p n st ∧ (∀ k, F p (st.s k)) ∧ ∑ k ∈ range (n + 1), st.s k = st.Y - st.rS

/-- the invariant inside a dep about to round `e` into level `n` -/
def DInvN (e : ℝ) (st : LState) : Prop :=
  st.ok → BndE p n n |e| st ∧ (∀ k, F p (st.s k)) ∧ ∑ k ∈ range (n + 1), st.s k + e = st.Y - st.rS

/-- the invariant inside a dep about to take `e` into level `m` -/
def DInv (m : ℕ) (e : ℝ) (st : LState) : Prop :=
  st.ok → BndE p n m |e| st ∧ (∀ k, F p (st.s k)) ∧ F p e ∧ ∑ k ∈ range (n + 1), st.s k + e = st.Y - st.rS

theorem sum_update_range {f : ℕ → ℝ} {i N : ℕ} (hi : i < N) (b : ℝ) :
    ∑ k ∈ range N, Function.update f i b k = ∑ k ∈ range N, f k - f i + b := by
  rw [sum_update_of_mem (mem_range.mpr hi), sdiff_singleton_eq_erase, ← add_sum_erase _ f (mem_range.mpr hi)]
  ring

theorem BndE.weaken {j : ℕ} {w : ℝ} {st : LState} (h : BndE p n j w st) (hw : 0 ≤ w) : Bnd p n st := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun k hk => ?_⟩
  have := h6 k hk
  split_ifs at this ⊢ <;> linarith

variable [Prec_gt_0 p]

omit [Prec_gt_0 p] in
theorem assign_inv {m : ℕ} {y : ℝ} (hm : m ≤ n) (hy : F p y) {st : LState} (h : Inv p n st) :
    Inv p n (assignS m y st) := by
  intro hok'
  obtain ⟨hok, hz⟩ : st.ok ∧ st.s m = 0 := hok'
  obtain ⟨⟨hnn, hr0, hlev, hq, hsn, hin⟩, hF, hsum⟩ := h hok
  have hu := (u_pos p).le
  refine ⟨⟨fun k => ?_, hr0, fun j hj => ?_, ?_, ?_, fun k hk => ?_⟩, fun k => ?_, ?_⟩
  · rcases eq_or_ne k m with rfl | hk
    · simp only [assignS, Function.update_self]
      exact ⟨by linarith [(hnn k).1, abs_nonneg y], (hnn k).2⟩
    · simpa [assignS, Function.update_of_ne hk] using hnn k
  · have h := hlev j hj
    have hc : 0 ≤ (st.cnt j : ℝ) * u p := mul_nonneg (Nat.cast_nonneg _) hu
    rcases eq_or_ne j m with rfl | hjm
    · simp only [assignS, Function.update_self]
      rw [hz] at h
      refine ⟨h.1.trans (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg y]) hc), ?_⟩
      linarith [(hnn j).1, (hnn j).2]
    · simpa [assignS, Function.update_of_ne hjm] using h
  · have hc : 0 ≤ (st.qcnt : ℝ) * u p := mul_nonneg (Nat.cast_nonneg _) hu
    rcases eq_or_ne n m with hnm | hnm
    · simp only [assignS, ← hnm, Function.update_self]
      exact hq.trans (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg y]) hc)
    · simpa [assignS, Function.update_of_ne hnm] using hq
  · rcases eq_or_ne n m with hnm | hnm
    · simp only [assignS, ← hnm, Function.update_self]
      linarith [(hnn n).1, hr0]
    · simpa [assignS, Function.update_of_ne hnm] using hsn
  · have h := hin k hk
    simp only [ite_self, add_zero] at h
    have hp' : prevOut (assignS m y st) k = prevOut st k := rfl
    rw [hp', ite_self, add_zero]
    rcases eq_or_ne k m with rfl | hkm
    · simp only [assignS, Function.update_self] at h ⊢
      linarith
    · simpa [assignS, Function.update_of_ne hkm] using h
  · rcases eq_or_ne k m with rfl | hkm
    · simpa [assignS] using hy
    · simpa [assignS, Function.update_of_ne hkm] using hF k
  · show ∑ k ∈ range (n + 1), Function.update st.s m y k = st.Y + y - st.rS
    rw [sum_update_range (by omega), hz, hsum]
    ring

omit [Prec_gt_0 p] in
theorem entering_dinv {l : ℕ} {t : ℝ} (ht : F p t) {st : LState} (h : Inv p n st) :
    DInv p n l t (entering l t st) := by
  intro hok
  obtain ⟨⟨hnn, hr0, hlev, hq, hsn, hin⟩, hF, hsum⟩ := h hok
  refine ⟨⟨hnn, hr0, hlev, hq, hsn, fun k hk => ?_⟩, hF, ht, ?_⟩
  · have h := hin k hk
    simp only [ite_self, add_zero] at h
    have hp' : prevOut (entering l t st) k = prevOut st k := rfl
    rw [hp']
    rcases eq_or_ne k l with rfl | hkl
    · simp only [entering, Function.update_self, ite_true] at h ⊢
      linarith
    · simp only [entering, Function.update_of_ne hkl, hkl, ite_false] at h ⊢
      linarith
  · show ∑ k ∈ range (n + 1), st.s k + t = st.Y + t - st.rS
    rw [hsum]
    ring

omit [Prec_gt_0 p] in
theorem entering_dinvN {y : ℝ} {st : LState} (h : Inv p n st) : DInvN p n y (entering n y st) := by
  intro hok
  obtain ⟨⟨hnn, hr0, hlev, hq, hsn, hin⟩, hF, hsum⟩ := h hok
  refine ⟨⟨hnn, hr0, hlev, hq, hsn, fun k hk => ?_⟩, hF, ?_⟩
  · have h := hin k hk
    simp only [ite_self, add_zero] at h
    have hp' : prevOut (entering n y st) k = prevOut st k := rfl
    rw [hp']
    rcases eq_or_ne k n with rfl | hkn
    · simp only [entering, Function.update_self, ite_true] at h ⊢
      linarith
    · simp only [entering, Function.update_of_ne hkn, hkn, ite_false] at h ⊢
      linarith
  · show ∑ k ∈ range (n + 1), st.s k + y = st.Y + y - st.rS
    rw [hsum]
    ring

omit [Prec_gt_0 p] in
theorem DInv.toN {e : ℝ} {st : LState} (h : DInv p n n e st) : DInvN p n e st := by
  intro hok
  obtain ⟨hB, hF, -, hsum⟩ := h hok
  exact ⟨hB, hF, hsum⟩

theorem roundN_inv {e : ℝ} {st : LState} (h : DInvN p n e st) : Inv p n (roundN p n e st) := by
  intro hok
  obtain ⟨⟨hnn, hr0, hlev, hq, hsn, hin⟩, hF, hsum⟩ := h hok
  have hu := (u_pos p).le
  set z := st.s n + e with hz
  have hr : |RN p z - z| ≤ u p * (|st.s n| + |e|) :=
    (abs_RN_sub_le_us p z).trans ((mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (abs_add_le _ _) hu))
  have hRN : |RN p z| ≤ |z| + |RN p z - z| := by
    calc |RN p z| = |z + (RN p z - z)| := by ring_nf
      _ ≤ |z| + |RN p z - z| := abs_add_le _ _
  have hn' := hin n le_rfl
  simp only [ite_true] at hn'
  refine ⟨⟨fun k => ?_, ?_, fun j hj => ?_, ?_, ?_, fun k hk => ?_⟩, fun k => ?_, ?_⟩
  · rcases eq_or_ne k n with rfl | hk
    · simp only [roundN, Function.update_self]
      exact ⟨by linarith [(hnn k).1, abs_nonneg e], (hnn k).2⟩
    · simpa [roundN, Function.update_of_ne hk] using hnn k
  · show 0 ≤ st.rA + |RN p z - z|
    linarith [abs_nonneg (RN p z - z)]
  · have hjn : j ≠ n := by omega
    simpa [roundN, Function.update_of_ne hjn] using hlev j hj
  · show st.rA + |RN p z - z| ≤ ((st.qcnt + 1 : ℕ) : ℝ) * u p * (Function.update st.inA n (st.inA n + |e|) n +
      (st.rA + |RN p z - z|))
    rw [Function.update_self]
    push_cast
    have h1 := (abs_add_le (st.s n) e)
    nlinarith [abs_nonneg e, abs_nonneg (RN p z - z), (hnn n).1, Nat.cast_nonneg (α := ℝ) st.qcnt,
      mul_le_mul_of_nonneg_left (show st.inA n + st.rA ≤ st.inA n + |e| + (st.rA + |RN p z - z|) by
        linarith [abs_nonneg e, abs_nonneg (RN p z - z)]) (mul_nonneg (Nat.cast_nonneg (α := ℝ) st.qcnt) hu)]
  · show |Function.update st.s n (RN p z) n| ≤ Function.update st.inA n (st.inA n + |e|) n + (st.rA + |RN p z - z|)
    rw [Function.update_self, Function.update_self]
    linarith [abs_add_le (st.s n) e]
  · have h := hin k hk
    have hp' : prevOut (roundN p n e st) k = prevOut st k := rfl
    rw [hp', ite_self, add_zero]
    rcases eq_or_ne k n with rfl | hkn
    · simp only [roundN, Function.update_self, ite_true] at h ⊢
      linarith
    · simp only [roundN, Function.update_of_ne hkn, hkn, ite_false] at h ⊢
      linarith
  · rcases eq_or_ne k n with rfl | hkn
    · simpa [roundN] using F_RN p z
    · simpa [roundN, Function.update_of_ne hkn] using hF k
  · show ∑ k ∈ range (n + 1), Function.update st.s n (RN p z) k = st.Y - (st.rS + (z - RN p z))
    rw [sum_update_range (by omega)]
    linarith

omit [Prec_gt_0 p] in
theorem prevOut_twoAt (m : ℕ) (e : ℝ) (st : LState) (k : ℕ) :
    prevOut (twoAt p m e st) k = prevOut st k + (if k = m + 1 then |(twoSum p (st.s m) e).2| else 0) := by
  unfold prevOut twoAt
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel, Function.update_apply, Nat.add_right_cancel_iff, add_eq_zero, one_ne_zero,
      and_false, ite_false]
    by_cases hk : k = m <;> simp [hk]

theorem twoAt_dinv (hp : 1 < p) {m : ℕ} (hm : m < n) {e : ℝ} {st : LState} (h : DInv p n m e st) :
    DInv p n (m + 1) (twoSum p (st.s m) e).2 (twoAt p m e st) := by
  intro hok
  obtain ⟨⟨hnn, hr0, hlev, hq, hsn, hin⟩, hF, he, hsum⟩ := h hok
  have hu := (u_pos p).le
  have hfa := facts_a p hp (hF m) he
  have hadd : (twoSum p (st.s m) e).1 + (twoSum p (st.s m) e).2 = st.s m + e := hfa.1
  have hr2 : |(twoSum p (st.s m) e).2| ≤ u p * (|st.s m| + |e|) :=
    (hfa.2.1.trans (min_le_right _ _)).trans ((mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (abs_add_le _ _) hu))
  have hr1 : |(twoSum p (st.s m) e).1| ≤ |st.s m| + |e| + |(twoSum p (st.s m) e).2| := by
    rw [show (twoSum p (st.s m) e).1 = st.s m + e + -(twoSum p (st.s m) e).2 by linarith]
    calc |st.s m + e + -(twoSum p (st.s m) e).2| ≤ |st.s m + e| + |-(twoSum p (st.s m) e).2| := abs_add_le _ _
      _ ≤ |st.s m| + |e| + |(twoSum p (st.s m) e).2| := by rw [abs_neg]; linarith [abs_add_le (st.s m) e]
  have hlm := hlev m hm
  have hinm := hin m (by omega)
  simp only [ite_true] at hinm
  have hnm : n ≠ m := by omega
  have hr2nn := abs_nonneg (twoSum p (st.s m) e).2
  have hene := abs_nonneg e
  refine ⟨⟨fun k => ?_, hr0, fun j hj => ?_, ?_, ?_, fun k hk => ?_⟩, fun k => ?_, F_twoSum_snd p _ _, ?_⟩
  · rcases eq_or_ne k m with rfl | hk
    · simp only [twoAt, Function.update_self]
      exact ⟨by linarith [(hnn k).1], by linarith [(hnn k).2]⟩
    · simpa [twoAt, Function.update_of_ne hk] using hnn k
  · rcases eq_or_ne j m with rfl | hjm
    · simp only [twoAt, Function.update_self]
      push_cast
      have hc : 0 ≤ (st.cnt j : ℝ) * u p := mul_nonneg (Nat.cast_nonneg _) hu
      have h1 : (st.cnt j : ℝ) * u p * (st.inA j + st.outA j) ≤
          (st.cnt j : ℝ) * u p * (st.inA j + |e| + (st.outA j + |(twoSum p (st.s j) e).2|)) :=
        mul_le_mul_of_nonneg_left (by linarith) hc
      have h2 : u p * (|st.s j| + |e|) ≤ u p * (st.inA j + |e| + (st.outA j + |(twoSum p (st.s j) e).2|)) :=
        mul_le_mul_of_nonneg_left (by linarith [hlm.2]) hu
      constructor
      · nlinarith [hlm.1]
      · linarith [hlm.2]
    · simpa [twoAt, Function.update_of_ne hjm] using hlev j hj
  · simpa [twoAt, Function.update_of_ne hnm] using hq
  · simpa [twoAt, Function.update_of_ne hnm] using hsn
  · rw [prevOut_twoAt]
    rcases eq_or_ne k m with rfl | hkm
    · simp only [twoAt, Function.update_self, show k ≠ k + 1 by omega, ite_false, add_zero]
      linarith
    · have h := hin k hk
      simp only [hkm, ite_false, add_zero] at h
      simp only [twoAt, Function.update_of_ne hkm]
      split_ifs <;> linarith
  · rcases eq_or_ne k m with rfl | hkm
    · simpa [twoAt] using F_twoSum_fst p (st.s k) e
    · simpa [twoAt, Function.update_of_ne hkm] using hF k
  · show ∑ k ∈ range (n + 1), Function.update st.s m (twoSum p (st.s m) e).1 k + (twoSum p (st.s m) e).2 =
      st.Y - st.rS
    rw [sum_update_range (by omega)]
    linarith

omit [Prec_gt_0 p] in
theorem stepOp_dep (l : ℕ) (t : ℝ) (st : LState) :
    stepOp p n (.dep l t) st = depRun p n (n - l) l t (entering l t st) := rfl

theorem depRun_spec (hp : 1 < p) : ∀ (k m : ℕ) (e : ℝ) (st : LState), m + k = n → DInv p n m e st →
    (∀ x ∈ (depRun p n k m e st).1, x.ok = st.ok ∧ (x.ok → Bnd p n x)) ∧
      (depRun p n k m e st).2.ok = st.ok ∧ Inv p n (depRun p n k m e st).2
  | 0, m, e, st, hmk, h => by
    obtain rfl : m = n := by omega
    have hinv := roundN_inv p m (DInv.toN p m h)
    refine ⟨fun x hx => ?_, rfl, hinv⟩
    simp only [depRun, List.mem_singleton] at hx
    subst hx
    exact ⟨rfl, fun hok => (hinv hok).1⟩
  | k + 1, m, e, st, hmk, h => by
    have h1 := twoAt_dinv p n hp (by omega : m < n) h
    obtain ⟨ih1, ih2, ih3⟩ := depRun_spec hp k (m + 1) _ (twoAt p m e st) (by omega) h1
    refine ⟨fun x hx => ?_, ih2, ih3⟩
    simp only [depRun, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨rfl, fun hok => ((h1 hok).1).weaken p n (abs_nonneg _)⟩
    · exact ih1 x hx

theorem stepOp_spec (hp : 1 < p) (o : LOp) (ho : o.wf p n) (st : LState) (h : Inv p n st) :
    (∀ x ∈ (stepOp p n o st).1, x.ok → Bnd p n x) ∧ (∀ x ∈ (stepOp p n o st).1, (stepOp p n o st).2.ok → x.ok) ∧
      ((stepOp p n o st).2.ok → st.ok) ∧ Inv p n (stepOp p n o st).2 := by
  cases o with
  | assign m y =>
    have hinv := assign_inv p n ho.1 ho.2 h
    refine ⟨fun x hx hok => ?_, fun x hx hok => ?_, fun hok => hok.1, hinv⟩
    · simp only [stepOp, List.mem_singleton] at hx
      subst hx
      exact (hinv hok).1
    · simp only [stepOp, List.mem_singleton] at hx
      subst hx
      exact hok
  | dep l t =>
    obtain ⟨h1, h2, h3⟩ := depRun_spec p n hp (n - l) l t (entering l t st) (by have := ho.1; omega)
      (entering_dinv p n ho.2 h)
    rw [stepOp_dep]
    refine ⟨fun x hx => (h1 x hx).2, fun x hx hok => ?_, fun hok => ?_, h3⟩
    · rw [(h1 x hx).1]
      rw [h2] at hok
      exact hok
    · rw [h2] at hok
      exact hok
  | round y =>
    have hinv := roundN_inv p n (entering_dinvN p n (y := y) h)
    refine ⟨fun x hx hok => ?_, fun x hx hok => ?_, fun hok => hok, hinv⟩
    · simp only [stepOp, List.mem_singleton] at hx
      subst hx
      exact (hinv hok).1
    · simp only [stepOp, List.mem_singleton] at hx
      subst hx
      exact hok

theorem runOps_spec (hp : 1 < p) (ops : List LOp) : ∀ st : LState, (∀ o ∈ ops, o.wf p n) → Inv p n st →
    (∀ x ∈ (runOps p n ops st).1, x.ok → Bnd p n x) ∧ (∀ x ∈ (runOps p n ops st).1, (runOps p n ops st).2.ok → x.ok) ∧
      ((runOps p n ops st).2.ok → st.ok) ∧ Inv p n (runOps p n ops st).2 := by
  induction ops with
  | nil => intro st _ h; exact ⟨by simp [runOps], by simp [runOps], fun hok => hok, h⟩
  | cons o os ih =>
    intro st hwf h
    obtain ⟨s1, s2, s3, s4⟩ := stepOp_spec p n hp o (hwf o (by simp)) st h
    obtain ⟨r1, r2, r3, r4⟩ := ih _ (fun o' ho' => hwf o' (by simp [ho'])) s4
    refine ⟨fun x hx => ?_, fun x hx hok => ?_, fun hok => s3 (r3 hok), r4⟩
    · simp only [runOps, List.mem_append] at hx
      rcases hx with hx | hx
      · exact s1 x hx
      · exact r1 x hx
    · simp only [runOps, List.mem_append] at hx
      rcases hx with hx | hx
      · exact s2 x hx (r3 hok)
      · exact r2 x hx hok

/-- the counted totals of `st` are at most those of `st'` -/
def LState.le (st st' : LState) : Prop :=
  (∀ k, st.adone k ≤ st'.adone k) ∧ (∀ k, st.cnt k ≤ st'.cnt k) ∧ st.qcnt ≤ st'.qcnt

theorem LState.le.refl (st : LState) : st.le st := ⟨fun _ => le_rfl, fun _ => le_rfl, le_rfl⟩

theorem LState.le.trans {a b c : LState} (h1 : a.le b) (h2 : b.le c) : a.le c :=
  ⟨fun k => (h1.1 k).trans (h2.1 k), fun k => (h1.2.1 k).trans (h2.2.1 k), h1.2.2.trans h2.2.2⟩

omit [Prec_gt_0 p] in
theorem le_update_add {f : ℕ → ℝ} {i : ℕ} {w : ℝ} (hw : 0 ≤ w) (k : ℕ) : f k ≤ Function.update f i (f i + w) k := by
  rcases eq_or_ne k i with rfl | hk
  · simp only [Function.update_self]
    linarith
  · rw [Function.update_of_ne hk]

omit [Prec_gt_0 p] in
theorem le_update_succ {f : ℕ → ℕ} {i : ℕ} (k : ℕ) : f k ≤ Function.update f i (f i + 1) k := by
  rcases eq_or_ne k i with rfl | hk
  · simp only [Function.update_self]
    omega
  · rw [Function.update_of_ne hk]

omit [Prec_gt_0 p] in
theorem depRun_le : ∀ (k m : ℕ) (e : ℝ) (st : LState),
    (∀ x ∈ (depRun p n k m e st).1, x.le (depRun p n k m e st).2) ∧ st.le (depRun p n k m e st).2
  | 0, m, e, st => by
    have h : st.le (roundN p n e st) := ⟨fun _ => le_rfl, fun _ => le_rfl, Nat.le_succ _⟩
    refine ⟨fun x hx => ?_, h⟩
    simp only [depRun, List.mem_singleton] at hx
    subst hx
    exact LState.le.refl _
  | k + 1, m, e, st => by
    obtain ⟨ih1, ih2⟩ := depRun_le k (m + 1) _ (twoAt p m e st)
    have h : st.le (twoAt p m e st) := ⟨fun _ => le_rfl, fun j => le_update_succ j, le_rfl⟩
    refine ⟨fun x hx => ?_, h.trans ih2⟩
    simp only [depRun, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ih2
    · exact ih1 x hx

omit [Prec_gt_0 p] in
theorem stepOp_le (o : LOp) (st : LState) :
    (∀ x ∈ (stepOp p n o st).1, x.le (stepOp p n o st).2) ∧ st.le (stepOp p n o st).2 := by
  cases o with
  | assign m y =>
    refine ⟨fun x hx => ?_, fun j => le_update_add (abs_nonneg y) j, fun _ => le_rfl, le_rfl⟩
    simp only [stepOp, List.mem_singleton] at hx
    subst hx
    exact LState.le.refl _
  | dep l t =>
    obtain ⟨h1, h2⟩ := depRun_le p n (n - l) l t (entering l t st)
    have he : st.le (entering l t st) := ⟨fun j => le_update_add (abs_nonneg t) j, fun _ => le_rfl, le_rfl⟩
    rw [stepOp_dep]
    exact ⟨h1, he.trans h2⟩
  | round y =>
    refine ⟨fun x hx => ?_, fun j => le_update_add (abs_nonneg y) j, fun _ => le_rfl, Nat.le_succ _⟩
    simp only [stepOp, List.mem_singleton] at hx
    subst hx
    exact LState.le.refl _

omit [Prec_gt_0 p] in
theorem runOps_le (ops : List LOp) : ∀ st : LState,
    (∀ x ∈ (runOps p n ops st).1, x.le (runOps p n ops st).2) ∧ st.le (runOps p n ops st).2 := by
  induction ops with
  | nil => intro st; exact ⟨by simp [runOps], LState.le.refl _⟩
  | cons o os ih =>
    intro st
    obtain ⟨s1, s2⟩ := stepOp_le p n o st
    obtain ⟨r1, r2⟩ := ih (stepOp p n o st).2
    refine ⟨fun x hx => ?_, s2.trans r2⟩
    simp only [runOps, List.mem_append] at hx
    rcases hx with hx | hx
    · exact (s1 x hx).trans r2
    · exact r1 x hx

omit [Prec_gt_0 p] in
theorem depRun_tot : ∀ (k m : ℕ) (e : ℝ) (st : LState), m + k = n →
    (depRun p n k m e st).2.adone = st.adone ∧
      (∀ j, (depRun p n k m e st).2.cnt j = st.cnt j + if m ≤ j ∧ j < n then 1 else 0) ∧
      (depRun p n k m e st).2.qcnt = st.qcnt + 1 ∧ (depRun p n k m e st).2.Y = st.Y
  | 0, m, e, st, h => by
    refine ⟨rfl, fun j => ?_, rfl, rfl⟩
    have hj : ¬(m ≤ j ∧ j < n) := by omega
    simp [depRun, roundN, hj]
  | k + 1, m, e, st, h => by
    obtain ⟨h1, h2, h3, h4⟩ := depRun_tot k (m + 1) _ (twoAt p m e st) (by omega)
    refine ⟨h1, fun j => ?_, h3, h4⟩
    rw [show (depRun p n (k + 1) m e st).2 = (depRun p n k (m + 1) (twoSum p (st.s m) e).2 (twoAt p m e st)).2
      from rfl, h2]
    by_cases hjm : j = m
    · subst hjm
      simp only [twoAt, Function.update_self]
      split_ifs <;> omega
    · simp only [twoAt, Function.update_of_ne hjm]
      split_ifs <;> omega

omit [Prec_gt_0 p] in
theorem stepOp_tot (o : LOp) (ho : o.wf p n) (st : LState) :
    (∀ j, (stepOp p n o st).2.adone j = st.adone j + opA n j o) ∧
      (∀ j < n, (stepOp p n o st).2.cnt j = st.cnt j + opT j o) ∧
      (stepOp p n o st).2.qcnt = st.qcnt + opQ o ∧ (stepOp p n o st).2.Y = st.Y + opY o := by
  cases o with
  | assign m y =>
    refine ⟨fun j => ?_, fun j _ => by simp [stepOp, assignS, opT], by simp [stepOp, assignS, opQ], rfl⟩
    simp only [stepOp, assignS, opA, Function.update_apply]
    by_cases hj : j = m
    · subst hj
      simp
    · simp [hj, Ne.symm hj]
  | dep l t =>
    obtain ⟨h1, h2, h3, h4⟩ := depRun_tot p n (n - l) l t (entering l t st) (by have := ho.1; omega)
    rw [stepOp_dep]
    refine ⟨fun j => ?_, fun j hj => ?_, by rw [h3]; rfl, by rw [h4]; rfl⟩
    · show (depRun p n (n - l) l t (entering l t st)).2.adone j = _
      rw [h1]
      simp only [entering, opA, Function.update_apply]
      by_cases hjl : j = l
      · subst hjl
        simp
      · simp [hjl, Ne.symm hjl]
    · show (depRun p n (n - l) l t (entering l t st)).2.cnt j = _
      rw [h2]
      simp only [entering, opT]
      by_cases hlj : l ≤ j <;> simp [hlj, hj]
  | round y =>
    refine ⟨fun j => ?_, fun j _ => by simp [stepOp, roundN, entering, opT], by simp [stepOp, roundN, entering, opQ],
      by simp [stepOp, roundN, entering, opY]⟩
    simp only [stepOp, roundN, entering, opA, Function.update_apply]
    by_cases hj : j = n
    · subst hj
      simp
    · simp [hj]

omit [Prec_gt_0 p] in
theorem runOps_tot (ops : List LOp) : ∀ st : LState, (∀ o ∈ ops, o.wf p n) →
    (∀ j, (runOps p n ops st).2.adone j = st.adone j + opsA n ops j) ∧
      (∀ j < n, (runOps p n ops st).2.cnt j = st.cnt j + opsT ops j) ∧
      (runOps p n ops st).2.qcnt = st.qcnt + opsQ ops ∧ (runOps p n ops st).2.Y = st.Y + opsY ops := by
  induction ops with
  | nil => intro st _; simp [runOps, opsA, opsT, opsQ, opsY]
  | cons o os ih =>
    intro st hwf
    obtain ⟨s1, s2, s3, s4⟩ := stepOp_tot p n o (hwf o (by simp)) st
    obtain ⟨r1, r2, r3, r4⟩ := ih (stepOp p n o st).2 (fun o' ho' => hwf o' (by simp [ho']))
    refine ⟨fun j => ?_, fun j hj => ?_, ?_, ?_⟩
    · show (runOps p n os (stepOp p n o st).2).2.adone j = _
      rw [r1, s1]
      simp only [opsA, List.map_cons, List.sum_cons]
      ring
    · show (runOps p n os (stepOp p n o st).2).2.cnt j = _
      rw [r2 j hj, s2 j hj]
      simp only [opsT, List.map_cons, List.sum_cons]
      ring
    · show (runOps p n os (stepOp p n o st).2).2.qcnt = _
      rw [r3, s3]
      simp only [opsQ, List.map_cons, List.sum_cons]
      ring
    · show (runOps p n os (stepOp p n o st).2).2.Y = _
      rw [r4, s4]
      simp only [opsY, List.map_cons, List.sum_cons]
      ring

theorem init_inv : Inv p n LState.init := by
  intro _
  refine ⟨?_, fun k => F_zero p, by simp [LState.init]⟩
  simp [Bnd, BndE, LState.init, prevOut]

omit [Prec_gt_0 p] in
/-- the step of the induction on levels: a level whose carries out `o` satisfy `o ≤ c u (a + o)` with `c ≤ T`, and
whose inputs `a` total at most `D`, has `o ≤ T u D / (1 - T u)` and `a + o ≤ D / (1 - T u)` -/
theorem geo_step {c T : ℕ} {uu a o D : ℝ} (hu : 0 ≤ uu) (ha : 0 ≤ a) (ho : 0 ≤ o) (hc : c ≤ T)
    (hTu : (T : ℝ) * uu < 1) (h : o ≤ c * uu * (a + o)) (hD : a ≤ D) :
    o ≤ T * uu * D / (1 - T * uu) ∧ a + o ≤ D / (1 - T * uu) := by
  have h1 : 0 < 1 - (T : ℝ) * uu := by linarith
  have hc' : (c : ℝ) * uu ≤ T * uu := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hu
  have h2 : o ≤ T * uu * (a + o) := h.trans (mul_le_mul_of_nonneg_right hc' (by linarith))
  have hT0 : 0 ≤ (T : ℝ) * uu := mul_nonneg (Nat.cast_nonneg _) hu
  have h3 := mul_le_mul_of_nonneg_left hD hT0
  constructor
  · rw [le_div_iff₀ h1]
    nlinarith
  · rw [le_div_iff₀ h1]
    nlinarith

omit [Prec_gt_0 p] in
/-- the induction on levels of Lemma 11's proof, at one moment: below level `n` the inputs total at most `D_m`, the
carries out at most `C_m` and the level at most `X_m`; at level `n` the rounding errors total at most `R` and the
level at most `X_n` -/
theorem bounds_of_Bnd {st : LState} (hB : Bnd p n st) {A : ℕ → ℝ} {T : ℕ → ℕ} {Q : ℕ}
    (hA : ∀ k ≤ n, st.adone k ≤ A k) (hT : ∀ m < n, st.cnt m ≤ T m) (hQ : st.qcnt ≤ Q)
    (hTu : ∀ m < n, (T m : ℝ) * u p < 1) (hQu : (Q : ℝ) * u p < 1) :
    (∀ m < n, st.inA m ≤ levD A T (u p) m ∧ st.outA m ≤ levC A T (u p) m ∧ |st.s m| ≤ levX A T (u p) m) ∧
      st.rA ≤ Q * u p * (levD A T (u p) n / (1 - Q * u p)) ∧ |st.s n| ≤ levD A T (u p) n / (1 - Q * u p) := by
  obtain ⟨hnn, hr0, hlev, hq, hsn, hin⟩ := hB
  have hu := (u_pos p).le
  have hin' : ∀ k ≤ n, st.inA k ≤ st.adone k + prevOut st k := fun k hk => by simpa using hin k hk
  have hm : ∀ m < n, st.inA m ≤ levD A T (u p) m ∧ st.outA m ≤ levC A T (u p) m ∧
      |st.s m| ≤ levX A T (u p) m := by
    intro m
    induction m with
    | zero =>
      intro h0
      have hD : st.inA 0 ≤ levD A T (u p) 0 := by
        have h := hin' 0 (by omega)
        simp only [prevOut, ite_true, add_zero] at h
        exact h.trans (hA 0 (by omega))
      obtain ⟨g1, g2⟩ := geo_step hu (hnn 0).1 (hnn 0).2 (hT 0 h0) (hTu 0 h0) (hlev 0 h0).1 hD
      exact ⟨hD, g1, (hlev 0 h0).2.trans g2⟩
    | succ m ih =>
      intro hm1
      obtain ⟨-, hCm, -⟩ := ih (by omega)
      have hD : st.inA (m + 1) ≤ levD A T (u p) (m + 1) := by
        have h := hin' (m + 1) (by omega)
        simp only [prevOut, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at h
        unfold levC at hCm
        simp only [levD]
        linarith [hA (m + 1) (by omega)]
      obtain ⟨g1, g2⟩ := geo_step hu (hnn _).1 (hnn _).2 (hT _ hm1) (hTu _ hm1) (hlev _ hm1).1 hD
      exact ⟨hD, g1, (hlev _ hm1).2.trans g2⟩
  have hDn : st.inA n ≤ levD A T (u p) n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · have h := hin' n le_rfl
      simp only [prevOut, h0, ite_true, add_zero] at h
      rw [h0]
      exact h.trans (hA 0 (by omega))
    · obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have h := hin' n le_rfl
      have hCn := (hm n' (by omega)).2.1
      rw [hn'] at h ⊢
      simp only [prevOut, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at h
      unfold levC at hCn
      simp only [levD]
      linarith [hA (n' + 1) (by omega)]
  obtain ⟨g1, g2⟩ := geo_step hu (hnn n).1 hr0 hQ hQu hq hDn
  refine ⟨hm, ?_, hsn.trans g2⟩
  rw [mul_div_assoc] at g1
  exact g1

omit [Prec_gt_0 p] in
theorem opsA_nonneg (ops : List LOp) (m : ℕ) : 0 ≤ opsA n ops m :=
  List.sum_nonneg fun x hx => by
    obtain ⟨o, -, rfl⟩ := List.mem_map.mp hx
    cases o <;> simp only [opA] <;> split_ifs <;> simp

/-- Lemma 11. Levels `s_0, …, s_n` start at zero and change only by (i) assignments `s_m ← y` to a zero level, (ii)
calls `dep(s, l, t)` and (iii) roundings `s_n ← RN(s_n + y)`; `A_m`, `T_m`, `Q`, `D_m`, `C_m`, `X_m` and `R` are as
the lemma defines them, with `T_m u < 1` and `Q u < 1`. Then (a) at every moment `|s_m| ≤ X_m`; (b) the carries out
of level `m` total at most `C_m`; (c) at the end `∑ s_m = Y - ∑ r`, and the rounding errors `r` at level `n` have
`∑ |r| ≤ R`. -/
theorem levels (hp : 1 < p) (ops : List LOp) (hwf : ∀ o ∈ ops, o.wf p n)
    (hTu : ∀ m < n, (opsT ops m : ℝ) * u p < 1) (hQu : (opsQ ops : ℝ) * u p < 1)
    (hok : (runOps p n ops LState.init).2.ok) :
    (∀ x ∈ LState.init :: (runOps p n ops LState.init).1,
      (∀ m < n, |x.s m| ≤ levX (opsA n ops) (opsT ops) (u p) m) ∧
        |x.s n| ≤ levD (opsA n ops) (opsT ops) (u p) n / (1 - opsQ ops * u p)) ∧
      (∀ m < n, (runOps p n ops LState.init).2.outA m ≤ levC (opsA n ops) (opsT ops) (u p) m) ∧
      ∑ m ∈ range (n + 1), (runOps p n ops LState.init).2.s m = opsY ops - (runOps p n ops LState.init).2.rS ∧
      (runOps p n ops LState.init).2.rA ≤
        opsQ ops * u p * (levD (opsA n ops) (opsT ops) (u p) n / (1 - opsQ ops * u p)) := by
  obtain ⟨r1, r2, -, r4⟩ := runOps_spec p n hp ops LState.init hwf (init_inv p n)
  obtain ⟨l1, -⟩ := runOps_le p n ops LState.init
  obtain ⟨t1, t2, t3, t4⟩ := runOps_tot p n ops LState.init hwf
  set fin := (runOps p n ops LState.init).2 with hfin
  have hA : ∀ k ≤ n, fin.adone k ≤ opsA n ops k := fun k _ => by rw [t1]; simp [LState.init]
  have hT : ∀ m < n, fin.cnt m ≤ opsT ops m := fun m hm => by rw [t2 m hm]; simp [LState.init]
  have hQ : fin.qcnt ≤ opsQ ops := by rw [t3]; simp [LState.init]
  obtain ⟨hB, -, hsum⟩ := r4 hok
  obtain ⟨b1, b2, -⟩ := bounds_of_Bnd p n hB hA hT hQ hTu hQu
  refine ⟨fun x hx => ?_, fun m hm => (b1 m hm).2.1, ?_, b2⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨c1, -, c2⟩ := bounds_of_Bnd p n ((init_inv p n) trivial).1 (fun k _ => opsA_nonneg n ops k)
        (fun _ _ => Nat.zero_le _) (Nat.zero_le _) hTu hQu
      exact ⟨fun m hm => (c1 m hm).2.2, c2⟩
    have hxB := r1 x hx (r2 x hx hok)
    have hle := l1 x hx
    obtain ⟨c1, -, c2⟩ := bounds_of_Bnd p n hxB (fun k hk => (hle.1 k).trans (hA k hk))
      (fun m hm => (hle.2.1 m).trans (hT m hm)) (hle.2.2.trans hQ) hTu hQu
    exact ⟨fun m hm => (c1 m hm).2.2, c2⟩
  · rw [hsum, t4]
    simp [LState.init]

end ExpansionBounds
