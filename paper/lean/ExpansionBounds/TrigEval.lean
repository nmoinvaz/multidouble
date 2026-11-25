import ExpansionBounds.GMono
import ExpansionBounds.RoundEval
import ExpansionBounds.SqrtEval
import ExpansionBounds.Trig

/-!
# Lemma 34's bounds in rational arithmetic, rounded up

`δ_S` and `δ_C` of Lemma 34 nest one `G_MUL` and one `G_ADD` per term of the series, and their exact values have
numerators of more than `10^5` bits after twenty terms. `trig_consts.py` rounds every value it carries up to 200 bits.
The same is done here: `sinDeltaU` and `cosDeltaU` are the recursions over `ℚ` with a rounding `ρ` where the
definitions below apply it, to both outputs of each step of Horner's rule and to `π̂^z`, `ε_z`, `ϑ`, `E_t`, `ω` and
`D`. Horner's first state, `ε_w` and the last sums and quotients are not rounded, and a script that reproduces the
stored states has to round at the same places. For any `ρ` with `q ≤ ρ q` the recursions are at least `δ_S` and `δ_C`,
because Lemma 13's bounds grow with their arguments (`GMono.lean`). `upQ b` is such a rounding, to `b` bits. Horner's
bounds are carried as a pair of a rational and a list (`hornerRunL`), and a run can be cut (`hornerRunL_add`), so that
the kernel checks it in pieces against stored states; `sinTail_le` and `cosTail_le` then bound `δ_S` and `δ_C` from
any state above Horner's.
-/

namespace ExpansionBounds

open Finset

/-- `q` rounded up to `b` bits: the next multiple of `2^{e-b}` for `2^{e-1} ≤ |q| < 2^e` -/
def upQ (b : ℕ) (q : ℚ) : ℚ := (⌈q * (2 : ℚ) ^ ((b : ℤ) - magQ q)⌉ : ℚ) * (2 : ℚ) ^ (magQ q - (b : ℤ))

theorem le_upQ (b : ℕ) (q : ℚ) : q ≤ upQ b q := by
  have h2 : (0 : ℚ) < 2 ^ (magQ q - (b : ℤ)) := zpow_pos (by norm_num) _
  have e : q = q * (2 : ℚ) ^ ((b : ℤ) - magQ q) * 2 ^ (magQ q - (b : ℤ)) := by
    rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    simp
  calc q = q * (2 : ℚ) ^ ((b : ℤ) - magQ q) * 2 ^ (magQ q - (b : ℤ)) := e
    _ ≤ upQ b q := mul_le_mul_of_nonneg_right (Int.le_ceil _) h2.le

section Mirrors

variable (uq : ℚ) (n : ℕ) (ρ : ℚ → ℚ)

/-- one step of Horner's bounds of Lemma 33 over `ℚ`, from `(e_{k+1}, π^{(k+1)})` to `(e_k, π^{(k)})`, each rounded by
`ρ`; the part bounds are a list, so that a state can be compared with stored data -/
def hornerStepL (πz : ℕ → ℚ) (zb εz η : ℚ) (Fk : ℕ → ℕ → ℚ) (φ v : ℕ → ℚ) (k : ℕ) (st : ℚ × List ℚ) :
    ℚ × List ℚ :=
  (ρ ((1 + εz) * zb * st.1 + εz * zb * v (k + 1) + φ k +
        (GmulEQ uq n πz (fun i => st.2.getD i 0) ((1 + εz) * zb * (v (k + 1) + st.1)) + n * η) +
      GaddEQ uq n (fun i => |Fk k i|)
        (fun i => GmulPQ uq n πz (fun i => st.2.getD i 0) ((1 + εz) * zb * (v (k + 1) + st.1)) i + η)
        (v k + ((1 + εz) * zb * st.1 + εz * zb * v (k + 1) + φ k +
          (GmulEQ uq n πz (fun i => st.2.getD i 0) ((1 + εz) * zb * (v (k + 1) + st.1)) + n * η)))),
    (List.range n).map fun i => ρ (GaddPQ uq n (fun i => |Fk k i|)
      (fun i => GmulPQ uq n πz (fun i => st.2.getD i 0) ((1 + εz) * zb * (v (k + 1) + st.1)) i + η)
      (v k + ((1 + εz) * zb * st.1 + εz * zb * v (k + 1) + φ k +
        (GmulEQ uq n πz (fun i => st.2.getD i 0) ((1 + εz) * zb * (v (k + 1) + st.1)) + n * η))) i))

/-- the steps `j_0 ≤ j < j_0 + m` of Horner's bounds down from degree `d`, from a given state -/
def hornerRunL (πz : ℕ → ℚ) (zb εz η : ℚ) (Fk : ℕ → ℕ → ℚ) (φ v : ℕ → ℚ) (d : ℕ) :
    ℕ → ℕ → ℚ × List ℚ → ℚ × List ℚ
  | _, 0, st => st
  | j0, m + 1, st =>
    hornerRunL πz zb εz η Fk φ v d (j0 + 1) m (hornerStepL uq n ρ πz zb εz η Fk φ v (d - (j0 + 1)) st)

/-- `(e_d, π^{(d)}) = (φ_d, |F_d|)` -/
def hornerInitL (Fk : ℕ → ℕ → ℚ) (φ : ℕ → ℚ) (d : ℕ) : ℚ × List ℚ := (φ d, (List.range n).map fun i => |Fk d i|)

/-- a run can be cut: `m_1 + m_2` steps are `m_1` steps and then `m_2` -/
theorem hornerRunL_add (πz : ℕ → ℚ) (zb εz η : ℚ) (Fk : ℕ → ℕ → ℚ) (φ v : ℕ → ℚ) (d : ℕ) :
    ∀ (m1 m2 j0 : ℕ) (st : ℚ × List ℚ), hornerRunL uq n ρ πz zb εz η Fk φ v d j0 (m1 + m2) st =
      hornerRunL uq n ρ πz zb εz η Fk φ v d (j0 + m1) m2 (hornerRunL uq n ρ πz zb εz η Fk φ v d j0 m1 st)
  | 0, m2, j0, st => by simp [hornerRunL]
  | m1 + 1, m2, j0, st => by
    rw [show m1 + 1 + m2 = (m1 + m2) + 1 by omega]
    simp only [hornerRunL]
    rw [hornerRunL_add πz zb εz η Fk φ v d m1 m2 (j0 + 1), show j0 + 1 + m1 = j0 + (m1 + 1) by omega]

theorem hornerRunL_succ (πz : ℕ → ℚ) (zb εz η : ℚ) (Fk : ℕ → ℕ → ℚ) (φ v : ℕ → ℚ) (d j : ℕ) (st : ℚ × List ℚ) :
    hornerRunL uq n ρ πz zb εz η Fk φ v d 0 (j + 1) st =
      hornerStepL uq n ρ πz zb εz η Fk φ v (d - (j + 1)) (hornerRunL uq n ρ πz zb εz η Fk φ v d 0 j st) := by
  rw [hornerRunL_add uq n ρ πz zb εz η Fk φ v d j 1 0 st]
  simp [hornerRunL]

/-- `π̂^z`, of `(ε_z, π̂^z) = G_MUL(ā, ā; 1)`, rounded -/
def scZetaU (ab : ℕ → ℚ) (i : ℕ) : ℚ := ρ (GmulPQ uq n ab ab 1 i)

/-- `ε_z`, rounded -/
def scEzU (ab : ℕ → ℚ) : ℚ := ρ (GmulEQ uq n ab ab 1)

/-- Horner's bounds `(E_1, π^{(1)})` for `z = MUL(r, r)` and the coefficients `F_k` of `C_k` -/
def scHU (ab : ℕ → ℚ) (rb : ℚ) (C : ℕ → ℚ) (Fk : ℕ → ℕ → ℚ) (K : ℕ) : ℚ × List ℚ :=
  hornerRunL uq n ρ (fun i => rb ^ 2 * scZetaU uq n ρ ab i) (rb ^ 2) (scEzU uq n ρ ab) 0 Fk
    (fun k => |∑ i ∈ range n, Fk k i - C k|) (fun k => |C k|) (K - 1) 0 (K - 2)
    (hornerInitL n Fk (fun k => |∑ i ∈ range n, Fk k i - C k|) (K - 1))

/-- `(1 + ε_z)(|C_1| + E_1)`, from Horner's `(E_1, π^{(1)})` -/
def scZtL (ab : ℕ → ℚ) (C : ℕ → ℚ) (st : ℚ × List ℚ) : ℚ := (1 + scEzU uq n ρ ab) * (|C 1| + st.1)

/-- `ϑ`, rounded -/
def scThL (ab : ℕ → ℚ) (C : ℕ → ℚ) (st : ℚ × List ℚ) (i : ℕ) : ℚ :=
  ρ (GmulPQ uq n (scZetaU uq n ρ ab) (fun i => st.2.getD i 0) (scZtL uq n ρ ab C st) i)

/-- `E_t`, rounded -/
def scEtL (ab : ℕ → ℚ) (C : ℕ → ℚ) (st : ℚ × List ℚ) : ℚ :=
  ρ ((1 + scEzU uq n ρ ab) * st.1 + scEzU uq n ρ ab * |C 1| +
    GmulEQ uq n (scZetaU uq n ρ ab) (fun i => st.2.getD i 0) (scZtL uq n ρ ab C st))

/-- `s_k = (-1)^k/(2k + 1)!` -/
def sinCQ (k : ℕ) : ℚ := (-1) ^ k / ((2 * k + 1).factorial : ℚ)

/-- `c_k = (-1)^k/(2k)!` -/
def cosCQ (k : ℕ) : ℚ := (-1) ^ k / ((2 * k).factorial : ℚ)

/-- `cos₋ x = 1 - x²/2 + x⁴/24 - x⁶/720` -/
def cosLoQ (x : ℚ) : ℚ := 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720

/-- `tan₊ x = (x - x³/6 + x⁵/120)/cos₋ x` -/
def tanHiQ (x : ℚ) : ℚ := (x - x ^ 3 / 6 + x ^ 5 / 120) / cosLoQ x

/-- `ε_w` -/
def sinWEL (ab : ℕ → ℚ) (st : ℚ × List ℚ) : ℚ :=
  GmulEQ uq n ab (scThL uq n ρ ab sinCQ st) (|sinCQ 1| + scEtL uq n ρ ab sinCQ st)

/-- `ω`, rounded -/
def sinWPL (ab : ℕ → ℚ) (st : ℚ × List ℚ) (i : ℕ) : ℚ :=
  ρ (GmulPQ uq n ab (scThL uq n ρ ab sinCQ st) (|sinCQ 1| + scEtL uq n ρ ab sinCQ st) i)

/-- `D`, rounded -/
def sinDL (ab : ℕ → ℚ) (rb : ℚ) (K : ℕ) (st : ℚ × List ℚ) : ℚ :=
  ρ (rb ^ 2 * (scEtL uq n ρ ab sinCQ st + sinWEL uq n ρ ab st) + rb ^ (2 * K) / ((2 * K + 1).factorial : ℚ))

/-- a bound on `δ_S`, from Horner's `(E_1, π^{(1)})` -/
def sinDeltaL (ab : ℕ → ℚ) (rb : ℚ) (K : ℕ) (st : ℚ × List ℚ) : ℚ :=
  uq ^ n + (sinDL uq n ρ ab rb K st + GaddEQ uq n ab (fun i => rb ^ 2 * sinWPL uq n ρ ab st i)
    (1 + sinDL uq n ρ ab rb K st) - uq ^ n) / (1 - rb ^ 2 / 6)

/-- `D_c`, rounded -/
def cosDL (ab : ℕ → ℚ) (rb : ℚ) (K : ℕ) (st : ℚ × List ℚ) : ℚ :=
  ρ (rb ^ 2 * scEtL uq n ρ ab cosCQ st + rb ^ (2 * K) / ((2 * K).factorial : ℚ))

/-- a bound on `δ_C`, from Horner's `(E_1, π^{(1)})` -/
def cosDeltaL (ab : ℕ → ℚ) (rb : ℚ) (K : ℕ) (st : ℚ × List ℚ) : ℚ :=
  uq ^ n + (cosDL uq n ρ ab rb K st + GaddfEQ uq n (fun i => rb ^ 2 * scThL uq n ρ ab cosCQ st i) 1
    (1 + cosDL uq n ρ ab rb K st) - uq ^ n) / cosLoQ rb

/-- `ψ_s`, a bound on the parts of SINR's result in units of `|r|` -/
def sinPsiL (ab : ℕ → ℚ) (rb : ℚ) (K : ℕ) (st : ℚ × List ℚ) (i : ℕ) : ℚ :=
  GaddPQ uq n ab (fun i => rb ^ 2 * sinWPL uq n ρ ab st i) (1 + sinDL uq n ρ ab rb K st) i

/-- `ψ_c`, a bound on the parts of COSR's result -/
def cosPsiL (ab : ℕ → ℚ) (rb : ℚ) (K : ℕ) (st : ℚ × List ℚ) (i : ℕ) : ℚ :=
  GaddfPQ uq n (fun i => rb ^ 2 * scThL uq n ρ ab cosCQ st i) 1 (1 + cosDL uq n ρ ab rb K st) i

/-- a bound on `δ_S` -/
def sinDeltaU (ab : ℕ → ℚ) (rb : ℚ) (Fk : ℕ → ℕ → ℚ) (K : ℕ) : ℚ :=
  sinDeltaL uq n ρ ab rb K (scHU uq n ρ ab rb sinCQ Fk K)

/-- a bound on `δ_C` -/
def cosDeltaU (ab : ℕ → ℚ) (rb : ℚ) (Fk : ℕ → ℕ → ℚ) (K : ℕ) : ℚ :=
  cosDeltaL uq n ρ ab rb K (scHU uq n ρ ab rb cosCQ Fk K)

/-- `C = ε max(δ_S + εu^n, δ_C + εu^n r̄ tan₊ r̄)`, `ε = 1 + 2u^n` -/
def trigCQ (dS dC rb : ℚ) : ℚ :=
  (1 + 2 * uq ^ n) * max (dS + (1 + 2 * uq ^ n) * uq ^ n) (dC + (1 + 2 * uq ^ n) * uq ^ n * (rb * tanHiQ rb))

end Mirrors

theorem cast_sinC (k : ℕ) : ((sinCQ k : ℚ) : ℝ) = sinC k := by simp [sinCQ, sinC]

theorem cast_cosC (k : ℕ) : ((cosCQ k : ℚ) : ℝ) = cosC k := by simp [cosCQ, cosC]

theorem cast_cosLo (x : ℚ) : ((cosLoQ x : ℚ) : ℝ) = cosLo x := by simp [cosLoQ, cosLo]

theorem cast_tanHi (x : ℚ) : ((tanHiQ x : ℚ) : ℝ) = tanHi x := by simp [tanHiQ, tanHi, sinHi, cast_cosLo]

section Bounds

variable (p : ℤ) (n : ℕ) {uq : ℚ} (h : (uq : ℝ) = u p) {ρ : ℚ → ℚ} (hρ : ∀ q, q ≤ ρ q)
include h hρ

/-- one step of Horner's bounds: from `(e_{k+1}, π^{(k+1)})` below their rounded mirrors to `(e_k, π^{(k)})` -/
theorem horner_step_le (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {πz : ℕ → ℝ} {πzq : ℕ → ℚ} (hπ0 : ∀ i, 0 ≤ πz i)
    (hπ : ∀ i, πz i ≤ ((πzq i : ℚ) : ℝ)) {zb : ℚ} (hzb : 0 ≤ zb) {εz : ℝ} {εzq : ℚ} (hε0 : 0 ≤ εz)
    (hε : εz ≤ ((εzq : ℚ) : ℝ)) (η : ℚ) (Fq : ℕ → ℚ) (φk vk : ℚ) {vk1 : ℚ} (hv1 : 0 ≤ vk1) {e1 : ℝ} {e1q : ℚ}
    (he0 : 0 ≤ e1) (he : e1 ≤ ((e1q : ℚ) : ℝ)) {π1 : ℕ → ℝ} {π1q : ℕ → ℚ} (hp0 : ∀ i, 0 ≤ π1 i)
    (hp1 : ∀ i, π1 i ≤ ((π1q i : ℚ) : ℝ)) :
    (1 + εz) * (zb : ℝ) * e1 + εz * (zb : ℝ) * (vk1 : ℝ) + (φk : ℝ) +
          (GmulE p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) + (n : ℝ) * (η : ℝ)) +
        GaddE p n (fun i => |((Fq i : ℚ) : ℝ)|)
          (fun i => GmulP p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) i + (η : ℝ))
          ((vk : ℝ) + ((1 + εz) * (zb : ℝ) * e1 + εz * (zb : ℝ) * (vk1 : ℝ) + (φk : ℝ) +
            (GmulE p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) + (n : ℝ) * (η : ℝ)))) ≤
        ((ρ ((1 + εzq) * zb * e1q + εzq * zb * vk1 + φk +
            (GmulEQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) + n * η) +
          GaddEQ uq n (fun i => |Fq i|) (fun i => GmulPQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) i + η)
            (vk + ((1 + εzq) * zb * e1q + εzq * zb * vk1 + φk +
              (GmulEQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) + n * η)))) : ℚ) : ℝ) ∧
      ∀ i, GaddP p n (fun i => |((Fq i : ℚ) : ℝ)|)
          (fun i => GmulP p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) i + (η : ℝ))
          ((vk : ℝ) + ((1 + εz) * (zb : ℝ) * e1 + εz * (zb : ℝ) * (vk1 : ℝ) + (φk : ℝ) +
            (GmulE p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) + (n : ℝ) * (η : ℝ)))) i ≤
        ((ρ (GaddPQ uq n (fun i => |Fq i|)
            (fun i => GmulPQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) i + η)
            (vk + ((1 + εzq) * zb * e1q + εzq * zb * vk1 + φk +
              (GmulEQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) + n * η))) i) : ℚ) : ℝ) := by
  have hzb' : (0 : ℝ) ≤ (zb : ℝ) := by exact_mod_cast hzb
  have hv1' : (0 : ℝ) ≤ (vk1 : ℝ) := by exact_mod_cast hv1
  have hεq : (0 : ℝ) ≤ (εzq : ℝ) := hε0.trans hε
  have heq : (0 : ℝ) ≤ (e1q : ℝ) := he0.trans he
  have hc : (1 + εz) * (zb : ℝ) ≤ (1 + (εzq : ℝ)) * (zb : ℝ) := mul_le_mul_of_nonneg_right (by linarith) hzb'
  have hc0 : 0 ≤ (1 + εz) * (zb : ℝ) := mul_nonneg (by linarith) hzb'
  have hZ : (1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1) ≤ (((1 + εzq) * zb * (vk1 + e1q) : ℚ) : ℝ) := by
    push_cast
    exact mul_le_mul hc (by linarith) (add_nonneg hv1' he0) (hc0.trans hc)
  obtain ⟨m1, m2⟩ := Gmul_mono p n hA3 hπ0 hp0 hπ hp1 hZ
  have m1' : GmulE p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) ≤
      ((GmulEQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) : ℚ) : ℝ) := by
    rw [cast_GmulE p n h]
    exact m1
  have m2' : ∀ i, GmulP p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) i + (η : ℝ) ≤
      ((GmulPQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) i + η : ℚ) : ℝ) := fun i => by
    rw [Rat.cast_add, cast_GmulP p n h]
    exact add_le_add (m2 i) le_rfl
  have hD : (1 + εz) * (zb : ℝ) * e1 + εz * (zb : ℝ) * (vk1 : ℝ) + (φk : ℝ) +
        (GmulE p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) + (n : ℝ) * (η : ℝ)) ≤
      (((1 + εzq) * zb * e1q + εzq * zb * vk1 + φk +
        (GmulEQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) + n * η) : ℚ) : ℝ) := by
    have a1 : (1 + εz) * (zb : ℝ) * e1 ≤ (1 + (εzq : ℝ)) * (zb : ℝ) * (e1q : ℝ) := mul_le_mul hc he he0 (hc0.trans hc)
    have a2 : εz * (zb : ℝ) * (vk1 : ℝ) ≤ (εzq : ℝ) * (zb : ℝ) * (vk1 : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hε hzb') hv1'
    push_cast
    linarith
  have hvD : (vk : ℝ) + ((1 + εz) * (zb : ℝ) * e1 + εz * (zb : ℝ) * (vk1 : ℝ) + (φk : ℝ) +
        (GmulE p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) + (n : ℝ) * (η : ℝ))) ≤
      ((vk + ((1 + εzq) * zb * e1q + εzq * zb * vk1 + φk +
        (GmulEQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) + n * η)) : ℚ) : ℝ) := by
    rw [Rat.cast_add]
    exact add_le_add le_rfl hD
  obtain ⟨g1, g2⟩ := Gadd_mono p n hA3 (α := fun i => |((Fq i : ℚ) : ℝ)|) (α' := fun i => ((|Fq i| : ℚ) : ℝ))
    (fun i => (Rat.cast_abs (Fq i)).ge) m2' hvD
  refine ⟨?_, fun i => ?_⟩
  · refine le_trans ?_ ((Rat.cast_le (K := ℝ)).mpr (hρ _))
    rw [Rat.cast_add, cast_GaddE p n h]
    exact add_le_add hD g1
  · refine le_trans ?_ ((Rat.cast_le (K := ℝ)).mpr (hρ _))
    rw [cast_GaddP p n h]
    exact g2 i

omit h hρ in
theorem getD_map_range (f : ℕ → ℚ) (N i : ℕ) : ((List.range N).map f).getD i 0 = if i < N then f i else 0 := by
  by_cases hi : i < N <;> simp [List.getD_eq_getElem?_getD, hi]

omit h hρ in
/-- Lemma 13's part bounds stop at `n` -/
theorem gParts_of_le (hn : 1 ≤ n) (X : ℕ → ℝ) (Zb Fb : ℝ) {i : ℕ} (hi : n ≤ i) : gParts p n X Zb Fb i = 0 := by
  cases i with
  | zero => omega
  | succ i =>
    have hi' : ¬i + 1 < n := by omega
    simp only [gParts, hi', ↓reduceIte]

/-- Horner's bounds are at most their rounded mirrors, which may start from larger `π^z` and `ε_z` -/
theorem hornerRunL_ge (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {πz : ℕ → ℝ} {πzq : ℕ → ℚ}
    (hπ0 : ∀ i, 0 ≤ πz i) (hπ : ∀ i, πz i ≤ ((πzq i : ℚ) : ℝ)) {zb : ℚ} (hzb : 0 ≤ zb) {εz : ℝ} {εzq : ℚ}
    (hε0 : 0 ≤ εz) (hε : εz ≤ ((εzq : ℚ) : ℝ)) {η : ℚ} (hη : 0 ≤ η) (Fk : ℕ → ℕ → ℚ)
    (hF0 : ∀ k i, n ≤ i → Fk k i = 0) {φ v : ℕ → ℚ} (hφ : ∀ k, 0 ≤ φ k) (hv : ∀ k, 0 ≤ v k) (d : ℕ) : ∀ j,
    (hornerB p n πz (zb : ℝ) εz (η : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φ k : ℚ) : ℝ))
          (fun k => ((v k : ℚ) : ℝ)) d j).1 ≤
        (((hornerRunL uq n ρ πzq zb εzq η Fk φ v d 0 j (hornerInitL n Fk φ d)).1 : ℚ) : ℝ) ∧
      ∀ i, (hornerB p n πz (zb : ℝ) εz (η : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φ k : ℚ) : ℝ))
          (fun k => ((v k : ℚ) : ℝ)) d j).2 i ≤
        ((((hornerRunL uq n ρ πzq zb εzq η Fk φ v d 0 j (hornerInitL n Fk φ d)).2.getD i 0 : ℚ)) : ℝ)
  | 0 => by
    refine ⟨le_rfl, fun i => ?_⟩
    simp only [hornerB, hornerRunL, hornerInitL]
    rw [getD_map_range]
    split_ifs with hi
    · exact (Rat.cast_abs (Fk d i)).ge
    · rw [hF0 d i (by omega)]
      simp
  | j + 1 => by
    obtain ⟨i1, i2⟩ := hornerRunL_ge hn hA3 hπ0 hπ hzb hε0 hε hη Fk hF0 hφ hv d j
    have hzb' : (0 : ℝ) ≤ (zb : ℝ) := by exact_mod_cast hzb
    have hη' : (0 : ℝ) ≤ (η : ℝ) := by exact_mod_cast hη
    obtain ⟨n1, n2⟩ := hornerB_nonneg p n hA3 hπ0 hzb' hε0 hη' (fun k i => ((Fk k i : ℚ) : ℝ))
      (φ := fun k => ((φ k : ℚ) : ℝ)) (v := fun k => ((v k : ℚ) : ℝ)) (fun k => by exact_mod_cast hφ k)
      (fun k => by exact_mod_cast hv k) d j
    obtain ⟨s1, s2⟩ := horner_step_le p n h hρ hA3 hπ0 hπ hzb hε0 hε η (Fk (d - (j + 1))) (φ (d - (j + 1)))
      (v (d - (j + 1))) (hv (d - (j + 1) + 1)) n1 i1 n2 i2
    rw [hornerRunL_succ]
    refine ⟨s1, fun i => ?_⟩
    simp only [hornerStepL]
    rw [getD_map_range]
    split_ifs with hi
    · exact s2 i
    · rw [Rat.cast_zero]
      exact (gParts_of_le p n hn _ _ _ (by omega)).le

/-- `π̂^z` is nonnegative and at most its rounded mirror -/
theorem scZeta_le (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {ab : ℕ → ℚ} (hab : ∀ i, 0 ≤ ab i) (i : ℕ) :
    0 ≤ GmulP p n (fun i => ((ab i : ℚ) : ℝ)) (fun i => ((ab i : ℚ) : ℝ)) 1 i ∧
      GmulP p n (fun i => ((ab i : ℚ) : ℝ)) (fun i => ((ab i : ℚ) : ℝ)) 1 i ≤ ((scZetaU uq n ρ ab i : ℚ) : ℝ) := by
  have hab' : ∀ i, (0 : ℝ) ≤ ((ab i : ℚ) : ℝ) := fun i => by exact_mod_cast hab i
  have e := cast_GmulP p n h ab ab 1 i
  rw [Rat.cast_one] at e
  refine ⟨(Gmul_nonneg p n hA3 hab' hab' zero_le_one).2 i, ?_⟩
  rw [← e]
  exact (Rat.cast_le (K := ℝ)).mpr (hρ _)

/-- `ε_z` is nonnegative and at most its rounded mirror -/
theorem scEz_le (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {ab : ℕ → ℚ} (hab : ∀ i, 0 ≤ ab i) :
    0 ≤ GmulE p n (fun i => ((ab i : ℚ) : ℝ)) (fun i => ((ab i : ℚ) : ℝ)) 1 ∧
      GmulE p n (fun i => ((ab i : ℚ) : ℝ)) (fun i => ((ab i : ℚ) : ℝ)) 1 ≤ ((scEzU uq n ρ ab : ℚ) : ℝ) := by
  have hab' : ∀ i, (0 : ℝ) ≤ ((ab i : ℚ) : ℝ) := fun i => by exact_mod_cast hab i
  have e := cast_GmulE p n h ab ab 1
  rw [Rat.cast_one] at e
  refine ⟨(Gmul_nonneg p n hA3 hab' hab' zero_le_one).1, ?_⟩
  rw [← e]
  exact (Rat.cast_le (K := ℝ)).mpr (hρ _)

/-- Horner's `(E_1, π^{(1)})` of Lemma 34 are nonnegative and at most their rounded mirrors -/
theorem scHU_ge (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {ab : ℕ → ℚ} (hab : ∀ i, 0 ≤ ab i) (rb : ℚ)
    (C : ℕ → ℚ) (CR : ℕ → ℝ) (hC : ∀ k, ((C k : ℚ) : ℝ) = CR k) (Fk : ℕ → ℕ → ℚ)
    (hF0 : ∀ k i, n ≤ i → Fk k i = 0) (K : ℕ) :
    (0 ≤ (scH p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) CR (fun k i => ((Fk k i : ℚ) : ℝ)) K).1 ∧
        (scH p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) CR (fun k i => ((Fk k i : ℚ) : ℝ)) K).1 ≤
          (((scHU uq n ρ ab rb C Fk K).1 : ℚ) : ℝ)) ∧
      ∀ i, 0 ≤ (scH p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) CR (fun k i => ((Fk k i : ℚ) : ℝ)) K).2 i ∧
        (scH p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) CR (fun k i => ((Fk k i : ℚ) : ℝ)) K).2 i ≤
          ((((scHU uq n ρ ab rb C Fk K).2.getD i 0 : ℚ)) : ℝ) := by
  have hz := fun i => scZeta_le p n h hρ hA3 hab i
  obtain ⟨e0, e1⟩ := scEz_le p n h hρ hA3 hab
  have hrb2 : (0 : ℚ) ≤ rb ^ 2 := sq_nonneg rb
  have hrb2' : (0 : ℝ) ≤ (rb : ℝ) ^ 2 := sq_nonneg _
  have hπ0 : ∀ i, 0 ≤ (rb : ℝ) ^ 2 * GmulP p n (fun i => ((ab i : ℚ) : ℝ)) (fun i => ((ab i : ℚ) : ℝ)) 1 i :=
    fun i => mul_nonneg hrb2' (hz i).1
  have hπ : ∀ i, (rb : ℝ) ^ 2 * GmulP p n (fun i => ((ab i : ℚ) : ℝ)) (fun i => ((ab i : ℚ) : ℝ)) 1 i ≤
      ((rb ^ 2 * scZetaU uq n ρ ab i : ℚ) : ℝ) := fun i => by
    push_cast
    exact mul_le_mul_of_nonneg_left (hz i).2 hrb2'
  have key := hornerRunL_ge p n h hρ hn hA3 hπ0 hπ hrb2 e0 e1 (η := 0) le_rfl Fk hF0
    (φ := fun k => |∑ i ∈ range n, Fk k i - C k|) (v := fun k => |C k|) (fun k => abs_nonneg _)
    (fun k => abs_nonneg _) (K - 1) (K - 2)
  have nn := hornerB_nonneg p n hA3 hπ0 hrb2' e0 le_rfl (fun k i => ((Fk k i : ℚ) : ℝ))
    (φ := fun k => |∑ i ∈ range n, ((Fk k i : ℚ) : ℝ) - CR k|) (v := fun k => |CR k|) (fun k => abs_nonneg _)
    (fun k => abs_nonneg _) (K - 1) (K - 2)
  have eφ : (fun k => ((|∑ i ∈ range n, Fk k i - C k| : ℚ) : ℝ)) =
      fun k => |∑ i ∈ range n, ((Fk k i : ℚ) : ℝ) - CR k| := by
    funext k
    rw [Rat.cast_abs, Rat.cast_sub, Rat.cast_sum, hC k]
  have ev : (fun k => ((|C k| : ℚ) : ℝ)) = fun k => |CR k| := by
    funext k
    rw [Rat.cast_abs, hC k]
  beta_reduce at key
  rw [eφ, ev, Rat.cast_zero, Rat.cast_pow] at key
  exact ⟨⟨nn.1, key.1⟩, fun i => ⟨nn.2 i, key.2 i⟩⟩

/-- `ϑ` and `E_t` are nonnegative and at most their rounded mirrors on any state above Horner's `(E_1, π^{(1)})` -/
theorem scRest_le (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {ab : ℕ → ℚ} (hab : ∀ i, 0 ≤ ab i) (rb : ℚ) (C : ℕ → ℚ)
    (CR : ℕ → ℝ) (hC : ∀ k, ((C k : ℚ) : ℝ) = CR k) (Fk : ℕ → ℕ → ℚ) (K : ℕ) {st : ℚ × List ℚ}
    (hst : (0 ≤ (scH p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) CR (fun k i => ((Fk k i : ℚ) : ℝ)) K).1 ∧
        (scH p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) CR (fun k i => ((Fk k i : ℚ) : ℝ)) K).1 ≤ ((st.1 : ℚ) : ℝ)) ∧
      ∀ i, 0 ≤ (scH p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) CR (fun k i => ((Fk k i : ℚ) : ℝ)) K).2 i ∧
        (scH p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) CR (fun k i => ((Fk k i : ℚ) : ℝ)) K).2 i ≤
          ((st.2.getD i 0 : ℚ) : ℝ)) :
    (∀ i, 0 ≤ scTh p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) CR (fun k i => ((Fk k i : ℚ) : ℝ)) K i ∧
        scTh p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) CR (fun k i => ((Fk k i : ℚ) : ℝ)) K i ≤
          ((scThL uq n ρ ab C st i : ℚ) : ℝ)) ∧
      0 ≤ scEt p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) CR (fun k i => ((Fk k i : ℚ) : ℝ)) K ∧
      scEt p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) CR (fun k i => ((Fk k i : ℚ) : ℝ)) K ≤
        ((scEtL uq n ρ ab C st : ℚ) : ℝ) := by
  obtain ⟨⟨h0, h1⟩, hp⟩ := hst
  have hz := fun i => scZeta_le p n h hρ hA3 hab i
  obtain ⟨e0, e1⟩ := scEz_le p n h hρ hA3 hab
  have hZt0 : 0 ≤ scZt p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) CR (fun k i => ((Fk k i : ℚ) : ℝ)) K :=
    mul_nonneg (by linarith) (add_nonneg (abs_nonneg _) h0)
  have hZt : scZt p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) CR (fun k i => ((Fk k i : ℚ) : ℝ)) K ≤
      ((scZtL uq n ρ ab C st : ℚ) : ℝ) := by
    unfold scZt scZtL
    push_cast
    rw [hC 1]
    exact mul_le_mul (by linarith) (by linarith) (add_nonneg (abs_nonneg _) h0) (by linarith)
  obtain ⟨m1, m2⟩ := Gmul_mono p n hA3 (fun i => (hz i).1) (fun i => (hp i).1) (fun i => (hz i).2)
    (fun i => (hp i).2) hZt
  obtain ⟨g1, g2⟩ := Gmul_nonneg p n hA3 (fun i => (hz i).1) (fun i => (hp i).1) hZt0
  refine ⟨fun i => ⟨g2 i, ?_⟩, add_nonneg (add_nonneg (mul_nonneg (by linarith) h0)
    (mul_nonneg e0 (abs_nonneg _))) g1, ?_⟩
  · unfold scThL
    refine le_trans ?_ ((Rat.cast_le (K := ℝ)).mpr (hρ _))
    rw [cast_GmulP p n h]
    exact m2 i
  · unfold scEt scEtL
    refine le_trans ?_ ((Rat.cast_le (K := ℝ)).mpr (hρ _))
    rw [Rat.cast_add, cast_GmulE p n h]
    refine add_le_add ?_ m1
    push_cast
    rw [hC 1]
    exact add_le_add (mul_le_mul (by linarith) h1 h0 (by linarith)) (mul_le_mul_of_nonneg_right e1 (abs_nonneg _))

/-- Lemma 34's `δ_S` is nonnegative and at most `sinDeltaL`, and SINR's part bounds `ψ_s` at most `sinPsiL`, on any
state above Horner's `(E_1, π^{(1)})`, for `0 ≤ r̄` with `r̄² < 6` -/
theorem sinTail_le (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {ab : ℕ → ℚ} (hab : ∀ i, 0 ≤ ab i) {rb : ℚ} (hrb0 : 0 ≤ rb)
    (hrb : rb ^ 2 < 6) (Fk : ℕ → ℕ → ℚ) (K : ℕ) {st : ℚ × List ℚ}
    (hst : (0 ≤ (scH p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) sinC (fun k i => ((Fk k i : ℚ) : ℝ)) K).1 ∧
        (scH p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) sinC (fun k i => ((Fk k i : ℚ) : ℝ)) K).1 ≤
          ((st.1 : ℚ) : ℝ)) ∧
      ∀ i, 0 ≤ (scH p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) sinC (fun k i => ((Fk k i : ℚ) : ℝ)) K).2 i ∧
        (scH p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) sinC (fun k i => ((Fk k i : ℚ) : ℝ)) K).2 i ≤
          ((st.2.getD i 0 : ℚ) : ℝ)) :
    0 ≤ sinDelta p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K ∧
      sinDelta p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K ≤
        ((sinDeltaL uq n ρ ab rb K st : ℚ) : ℝ) ∧
      ∀ i, sinPsi p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K i ≤
        ((sinPsiL uq n ρ ab rb K st i : ℚ) : ℝ) := by
  have hu := u_pos p
  have hab' : ∀ i, (0 : ℝ) ≤ ((ab i : ℚ) : ℝ) := fun i => by exact_mod_cast hab i
  have hrb0' : (0 : ℝ) ≤ (rb : ℝ) := by exact_mod_cast hrb0
  have hrb2 : (0 : ℝ) ≤ (rb : ℝ) ^ 2 := sq_nonneg _
  obtain ⟨hTh, hEt0, hEt⟩ := scRest_le p n h hρ hA3 hab rb sinCQ sinC cast_sinC Fk K hst
  have hs1 : ((|sinCQ 1| : ℚ) : ℝ) = |sinC 1| := by rw [Rat.cast_abs, cast_sinC]
  have hZw0 : 0 ≤ |sinC 1| + scEt p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) sinC (fun k i => ((Fk k i : ℚ) : ℝ)) K :=
    add_nonneg (abs_nonneg _) hEt0
  have hZw : |sinC 1| + scEt p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) sinC (fun k i => ((Fk k i : ℚ) : ℝ)) K ≤
      ((|sinCQ 1| + scEtL uq n ρ ab sinCQ st : ℚ) : ℝ) := by
    rw [Rat.cast_add, hs1]
    linarith
  obtain ⟨w1, w2⟩ := Gmul_mono p n hA3 hab' (fun i => (hTh i).1) (fun i => le_refl ((ab i : ℚ) : ℝ))
    (fun i => (hTh i).2) hZw
  obtain ⟨v1, v2⟩ := Gmul_nonneg p n hA3 hab' (fun i => (hTh i).1) hZw0
  have hWE : sinWE p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K ≤
      ((sinWEL uq n ρ ab st : ℚ) : ℝ) := by
    unfold sinWE sinWEL
    rw [cast_GmulE p n h]
    exact w1
  have hWP : ∀ i, sinWP p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K i ≤
      ((sinWPL uq n ρ ab st i : ℚ) : ℝ) := fun i => by
    unfold sinWP sinWPL
    refine le_trans ?_ ((Rat.cast_le (K := ℝ)).mpr (hρ _))
    rw [cast_GmulP p n h]
    exact w2 i
  have hD0 : 0 ≤ sinD p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K :=
    add_nonneg (mul_nonneg hrb2 (add_nonneg hEt0 v1)) (div_nonneg (pow_nonneg hrb0' _) (Nat.cast_nonneg _))
  have hD : sinD p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K ≤
      ((sinDL uq n ρ ab rb K st : ℚ) : ℝ) := by
    unfold sinD sinDL
    refine le_trans ?_ ((Rat.cast_le (K := ℝ)).mpr (hρ _))
    push_cast
    have := mul_le_mul_of_nonneg_left (add_le_add hEt hWE) hrb2
    linarith
  have hβ0 : ∀ i, 0 ≤ (rb : ℝ) ^ 2 *
      sinWP p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K i :=
    fun i => mul_nonneg hrb2 (v2 i)
  obtain ⟨y1, y2⟩ := Gadd_mono p n hA3 (fun i => le_refl ((ab i : ℚ) : ℝ))
    (β := fun i => (rb : ℝ) ^ 2 * sinWP p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K i)
    (β' := fun i => ((rb ^ 2 * sinWPL uq n ρ ab st i : ℚ) : ℝ))
    (fun i => by push_cast; exact mul_le_mul_of_nonneg_left (hWP i) hrb2)
    (Zb := 1 + sinD p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K)
    (Zb' := ((1 + sinDL uq n ρ ab rb K st : ℚ) : ℝ)) (by push_cast; linarith)
  have hY : sinY p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K ≤
      ((GaddEQ uq n ab (fun i => rb ^ 2 * sinWPL uq n ρ ab st i) (1 + sinDL uq n ρ ab rb K st) : ℚ) : ℝ) := by
    unfold sinY
    rw [cast_GaddE p n h]
    exact y1
  have hY0 : u p ^ n * (1 + sinD p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K) ≤
      sinY p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K := by
    unfold sinY
    rw [gaddE_split]
    linarith [(Gadd_nonneg p n hA3 hab' hβ0 (le_refl (0 : ℝ))).1]
  have h6 : (0 : ℝ) < 1 - (rb : ℝ) ^ 2 / 6 := by
    have : ((rb ^ 2 : ℚ) : ℝ) < 6 := by exact_mod_cast hrb
    push_cast at this
    linarith
  have hun : 0 ≤ u p ^ n := pow_nonneg hu.le _
  refine ⟨?_, ?_, fun i => ?_⟩
  · unfold sinDelta
    have : 0 ≤ u p ^ n * sinD p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K :=
      mul_nonneg hun hD0
    exact add_nonneg hun (div_nonneg (by linarith) h6.le)
  · unfold sinDelta sinDeltaL
    push_cast
    rw [h]
    refine add_le_add le_rfl (div_le_div_of_nonneg_right ?_ h6.le)
    linarith
  · unfold sinPsi sinPsiL
    rw [cast_GaddP p n h]
    exact y2 i

/-- Lemma 34's `δ_C` is nonnegative and at most `cosDeltaL`, and COSR's part bounds `ψ_c` at most `cosPsiL`, on any
state above Horner's `(E_1, π^{(1)})`, for `0 ≤ r̄` with `cos₋ r̄ > 0` -/
theorem cosTail_le (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {ab : ℕ → ℚ} (hab : ∀ i, 0 ≤ ab i) {rb : ℚ} (hrb0 : 0 ≤ rb)
    (hc : 0 < cosLoQ rb) (Fk : ℕ → ℕ → ℚ) (K : ℕ) {st : ℚ × List ℚ}
    (hst : (0 ≤ (scH p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) cosC (fun k i => ((Fk k i : ℚ) : ℝ)) K).1 ∧
        (scH p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) cosC (fun k i => ((Fk k i : ℚ) : ℝ)) K).1 ≤
          ((st.1 : ℚ) : ℝ)) ∧
      ∀ i, 0 ≤ (scH p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) cosC (fun k i => ((Fk k i : ℚ) : ℝ)) K).2 i ∧
        (scH p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) cosC (fun k i => ((Fk k i : ℚ) : ℝ)) K).2 i ≤
          ((st.2.getD i 0 : ℚ) : ℝ)) :
    0 ≤ cosDelta p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K ∧
      cosDelta p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K ≤
        ((cosDeltaL uq n ρ ab rb K st : ℚ) : ℝ) ∧
      ∀ i, cosPsi p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K i ≤
        ((cosPsiL uq n ρ ab rb K st i : ℚ) : ℝ) := by
  have hu := u_pos p
  have hrb0' : (0 : ℝ) ≤ (rb : ℝ) := by exact_mod_cast hrb0
  have hrb2 : (0 : ℝ) ≤ (rb : ℝ) ^ 2 := sq_nonneg _
  obtain ⟨hTh, hEt0, hEt⟩ := scRest_le p n h hρ hA3 hab rb cosCQ cosC cast_cosC Fk K hst
  have hD0 : 0 ≤ cosD p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K :=
    add_nonneg (mul_nonneg hrb2 hEt0) (div_nonneg (pow_nonneg hrb0' _) (Nat.cast_nonneg _))
  have hD : cosD p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K ≤
      ((cosDL uq n ρ ab rb K st : ℚ) : ℝ) := by
    unfold cosD cosDL
    refine le_trans ?_ ((Rat.cast_le (K := ℝ)).mpr (hρ _))
    push_cast
    have := mul_le_mul_of_nonneg_left hEt hrb2
    linarith
  have hα0 : ∀ i, 0 ≤ (rb : ℝ) ^ 2 *
      scTh p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) cosC (fun k i => ((Fk k i : ℚ) : ℝ)) K i :=
    fun i => mul_nonneg hrb2 (hTh i).1
  have hα : ∀ i, (rb : ℝ) ^ 2 *
        scTh p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) cosC (fun k i => ((Fk k i : ℚ) : ℝ)) K i ≤
      ((rb ^ 2 * scThL uq n ρ ab cosCQ st i : ℚ) : ℝ) := fun i => by
    push_cast
    exact mul_le_mul_of_nonneg_left (hTh i).2 hrb2
  have hZ : 1 + cosD p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K ≤
      ((1 + cosDL uq n ρ ab rb K st : ℚ) : ℝ) := by
    push_cast
    linarith
  have y1 := GaddfE_mono p n hα (β0 := 1) (β0' := ((1 : ℚ) : ℝ)) (by norm_num) hZ
  have y2 := GaddfP_mono p n hα (β0 := 1) (β0' := ((1 : ℚ) : ℝ)) (by norm_num) hZ
  have hY : cosY p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K ≤
      ((GaddfEQ uq n (fun i => rb ^ 2 * scThL uq n ρ ab cosCQ st i) 1 (1 + cosDL uq n ρ ab rb K st) : ℚ) : ℝ) := by
    unfold cosY
    rw [cast_GaddfE p n h]
    exact y1
  have hY0 : u p ^ n * (1 + cosD p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K) ≤
      cosY p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K := by
    unfold cosY
    rw [gaddfE_split]
    linarith [(Gaddf_nonneg p n hα0 zero_le_one (le_refl (0 : ℝ))).1]
  have hc' : (0 : ℝ) < cosLo (rb : ℝ) := by
    rw [← cast_cosLo]
    exact_mod_cast hc
  have hun : 0 ≤ u p ^ n := pow_nonneg hu.le _
  refine ⟨?_, ?_, fun i => ?_⟩
  · unfold cosDelta
    have : 0 ≤ u p ^ n * cosD p n (fun i => ((ab i : ℚ) : ℝ)) (rb : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) K :=
      mul_nonneg hun hD0
    exact add_nonneg hun (div_nonneg (by linarith) hc'.le)
  · unfold cosDelta cosDeltaL
    push_cast
    rw [h, cast_cosLo]
    refine add_le_add le_rfl (div_le_div_of_nonneg_right ?_ hc'.le)
    linarith
  · unfold cosPsi cosPsiL
    rw [cast_GaddfP p n h]
    exact y2 i

end Bounds

/-- `C` grows with `δ_S` and `δ_C`, and its mirror computes it -/
theorem trigC_le (p : ℤ) (n : ℕ) {uq : ℚ} (h : (uq : ℝ) = u p) {dS dC : ℝ} {dSq dCq : ℚ} (rb : ℚ)
    (hS : dS ≤ ((dSq : ℚ) : ℝ)) (hC : dC ≤ ((dCq : ℚ) : ℝ)) :
    trigC p n dS dC (rb : ℝ) ≤ ((trigCQ uq n dSq dCq rb : ℚ) : ℝ) := by
  have hu := u_pos p
  unfold trigC trigCQ
  rw [Rat.cast_mul, Rat.cast_max]
  push_cast
  rw [h, cast_tanHi]
  exact mul_le_mul_of_nonneg_left (max_le_max (by linarith) (by linarith)) (by positivity)

end ExpansionBounds
