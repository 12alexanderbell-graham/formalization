import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Checked.Sim.ODETools
import Checked.Sim.QPoly
import Work.Math.LE32Cell

/-! Lane–Emden equation of index three halves: the validated cells of `Work.Math.LE32Cell.cell`
checked by kernel evaluation. All side conditions and both defect bounds of a cell are one
proposition over the rationals (`CellProp`). The power θ ^ (3/2) of the Taylor polynomial `pt` is
replaced in the defect by `pw ^ 3`, with `pw` a polynomial whose square is certified close to `pt`
and which is bounded away from zero (`g32_close`); in a cell next to the zero of θ, `pw = []` and
θ ^ (3/2) of the polynomial is bounded by `P ^ 3` from `pt ≤ P ^ 2` (crude cell). The chain
lemmas are those of `Checked.Math.LENCellQ` with the field of index three halves.
Run 2026-11-19T1028Z. -/

namespace Work.Math.LE32CellQ
open Set Checked.Sim Checked.Sim.QPoly Checked.Math.LENCell Work.Math.LE32Cell

/-- One cell: start time `t0`, length `h`, input radius `δ` around the constant terms of the
Taylor polynomials `pt` (θ) and `pp` (φ) in σ = t − t0, defect bound `ε`, output radius `B`,
slab half-width `TH` with `TH ≤ S ^ 2`, Lipschitz constant `K`; `pw` approximates √θ (empty in a
crude cell), `c` and `P` bound `pw` (in a crude cell `P ^ 2` bounds `pt`), `η` bounds
`pw ^ 2 − pt`, and `γ` bounds the error of `pw ^ 3` against θ ^ (3/2) of `pt`. -/
structure Cell where
  t0 : ℚ
  h : ℚ
  δ : ℚ
  ε : ℚ
  B : ℚ
  TH : ℚ
  K : ℚ
  S : ℚ
  c : ℚ
  P : ℚ
  η : ℚ
  γ : ℚ
  pt : List ℚ
  pp : List ℚ
  pw : List ℚ

/-- The cube of a polynomial. -/
def qcube (p : List ℚ) : List ℚ := qmul (qmul p p) p

theorem evalQ_qcube (p : List ℚ) (s : ℝ) : evalQ (qcube p) s = evalQ p s ^ 3 := by
  rw [qcube, evalQ_qmul, evalQ_qmul]; ring

/-- The multiplied-out defect of the second component with `pw ^ 3` for θ ^ (3/2):
(t0+σ)pp' + 2pp + (t0+σ)pw³. -/
def defect2 (c : Cell) : List ℚ :=
  qadd (qadd (qmul [c.t0, 1] (qderiv c.pp)) (qsmul 2 c.pp)) (qmul [c.t0, 1] (qcube c.pw))

/-- The bound `γ` on |θ ^ (3/2) of `pt` − `pw ^ 3|: crude (`pw = []`) or from the square
certificate. -/
def GamProp (c : Cell) : Prop :=
  (c.pw = [] ∧ 0 ≤ c.P ∧ c.pt.headD 0 + c.h * qabs c.pt.tail c.h ≤ c.P ^ 2 ∧ c.P ^ 3 ≤ c.γ) ∨
  (0 < c.c ∧ c.c ≤ c.pw.headD 0 - c.h * qabs c.pw.tail c.h ∧
    c.pw.headD 0 + c.h * qabs c.pw.tail c.h ≤ c.P ∧
    qabs (qsub (qmul c.pw c.pw) c.pt) c.h ≤ c.η ∧ c.η < c.c ^ 2 ∧
    c.η / c.c * (3 * c.P ^ 2 + 3 / 2 * c.η) ≤ c.γ)

instance (c : Cell) : Decidable (GamProp c) := by unfold GamProp; infer_instance

/-- All hypotheses of `LE32Cell.cell` except the solution's own, as one proposition over ℚ. -/
def CellProp (T : ℚ) (c : Cell) : Prop :=
  0 < c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h ∧ 1 ≤ c.K ∧ 0 ≤ c.S ∧ c.TH ≤ c.S ^ 2 ∧
  2 / c.t0 + 3 / 2 * c.S ≤ c.K ∧ c.K * c.h < 1 ∧
  0 ≤ c.δ ∧ 0 ≤ c.ε ∧
  -(c.TH - 1 / 100) ≤ c.pt.headD 0 - c.h * qabs c.pt.tail c.h ∧
  c.pt.headD 0 + c.h * qabs c.pt.tail c.h ≤ c.TH - 1 / 100 ∧
  qabs (qsub (qderiv c.pt) c.pp) c.h ≤ c.ε ∧
  qabs (defect2 c) c.h + (c.t0 + c.h) * c.γ ≤ c.ε * c.t0 ∧
  GamProp c ∧
  c.δ * (1 / (1 - c.K * c.h)) + c.ε / c.K * (1 / (1 - c.K * c.h) - 1) ≤ c.B ∧
  c.B < 1 / 100

instance (T : ℚ) (c : Cell) : Decidable (CellProp T c) := by unfold CellProp; infer_instance

/-- `CellProp` as a Boolean, for evaluation by the kernel. -/
def cellOK (T : ℚ) (c : Cell) : Bool := decide (CellProp T c)

theorem cellOK_basic {T : ℚ} (c : Cell) (hok : cellOK T c = true) :
    0 < c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h := by
  obtain ⟨k1, k2, k3, -⟩ : CellProp T c := of_decide_eq_true hok
  exact ⟨k1, k2, k3⟩

theorem defect2_eval (c : Cell) (σ : ℝ) :
    ((c.t0 : ℝ) + σ) * dEvalQ c.pp σ + 2 * evalQ c.pp σ +
      ((c.t0 : ℝ) + σ) * evalQ c.pw σ ^ 3 = evalQ (defect2 c) σ := by
  simp only [defect2, evalQ_qadd, evalQ_qsmul, evalQ_qmul, evalQ_qcube, ← dEvalQ_eq, evalQ]
  push_cast; ring

/-- The γ bound from its rational certificate. -/
theorem gam_bound (c : Cell) (hg : GamProp c) {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ c.h) :
    |g32 (evalQ c.pt σ) - evalQ c.pw σ ^ 3| ≤ c.γ := by
  rcases hg with ⟨hpw, hP0, hpt, hγ⟩ | ⟨hc, hlo, hhi, hη, hηc, hγ⟩
  · have hP0' : (0 : ℝ) ≤ c.P := by exact_mod_cast hP0
    have hu := upper_q c.pt h0 h1
    have hpt' : ((c.pt.headD 0 + c.h * qabs c.pt.tail c.h : ℚ) : ℝ) ≤ ((c.P ^ 2 : ℚ) : ℝ) := by
      exact_mod_cast hpt
    have hγ' : ((c.P ^ 3 : ℚ) : ℝ) ≤ c.γ := by exact_mod_cast hγ
    push_cast at hpt' hγ'
    have hs : Real.sqrt (evalQ c.pt σ) ≤ c.P := by
      calc Real.sqrt (evalQ c.pt σ) ≤ Real.sqrt ((c.P : ℝ) ^ 2) := Real.sqrt_le_sqrt (by
            push_cast at hu; linarith)
        _ = c.P := Real.sqrt_sq hP0'
    rw [hpw]
    simp only [evalQ]
    rw [zero_pow (by norm_num), sub_zero, abs_of_nonneg (g32_nonneg _)]
    unfold g32
    calc Real.sqrt (evalQ c.pt σ) ^ 3 ≤ (c.P : ℝ) ^ 3 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 3
      _ ≤ c.γ := hγ'
  · have hc' : (0 : ℝ) < c.c := by exact_mod_cast hc
    have hl := lower_q c.pw h0 h1
    have hu := upper_q c.pw h0 h1
    have hlo' : (c.c : ℝ) ≤ ((c.pw.headD 0 - c.h * qabs c.pw.tail c.h : ℚ) : ℝ) := by
      exact_mod_cast hlo
    have hhi' : ((c.pw.headD 0 + c.h * qabs c.pw.tail c.h : ℚ) : ℝ) ≤ c.P := by
      exact_mod_cast hhi
    have hη' : ((qabs (qsub (qmul c.pw c.pw) c.pt) c.h : ℚ) : ℝ) ≤ c.η := by exact_mod_cast hη
    have hηc' : ((c.η : ℚ) : ℝ) < ((c.c ^ 2 : ℚ) : ℝ) := by exact_mod_cast hηc
    have hγ' : ((c.η / c.c * (3 * c.P ^ 2 + 3 / 2 * c.η) : ℚ) : ℝ) ≤ c.γ := by exact_mod_cast hγ
    push_cast at hηc' hγ'
    have hsq : |evalQ c.pw σ ^ 2 - evalQ c.pt σ| ≤ c.η := by
      have := abs_le_qabs (qsub (qmul c.pw c.pw) c.pt) h0 h1
      rw [evalQ_qsub, evalQ_qmul] at this
      rw [sq]; exact this.trans hη'
    exact (g32_close hc' (hlo'.trans hl) (hu.trans hhi') hsq hηc').trans hγ'

/-- One validated cell from its Boolean check. -/
theorem cell_q {T : ℚ} (c : Cell) (hok : cellOK T c = true) {θ φ : ℝ → ℝ}
    (hθ : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), HasDerivWithinAt θ (φ t) (Icc 0 (T : ℝ)) t)
    (hφ : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt φ (-(2 / t * φ t) - g32 (θ t)) (Icc 0 (T : ℝ)) t)
    (h0 : |θ c.t0 - ((c.pt.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      |θ t - evalQ c.pt (t - c.t0)| ≤ c.B ∧ |φ t - evalQ c.pp (t - c.t0)| ≤ c.B := by
  obtain ⟨k1, k2, k3, k4, kS0, kTS, k5, k6, k7, k8, k9, k10, k11, k12, kg, k13, k14⟩ :
    CellProp T c := of_decide_eq_true hok
  have r14 : ((c.B : ℚ) : ℝ) < ((1 / 100 : ℚ) : ℝ) := by exact_mod_cast k14
  have r5 : ((2 / c.t0 + 3 / 2 * c.S : ℚ) : ℝ) ≤ (c.K : ℝ) := by exact_mod_cast k5
  have rTS : ((c.TH : ℚ) : ℝ) ≤ ((c.S ^ 2 : ℚ) : ℝ) := by exact_mod_cast kTS
  have r9 : ((-(c.TH - 1 / 100) : ℚ) : ℝ) ≤ ((c.pt.headD 0 - c.h * qabs c.pt.tail c.h : ℚ) : ℝ) := by
    exact_mod_cast k9
  have r10 : ((c.pt.headD 0 + c.h * qabs c.pt.tail c.h : ℚ) : ℝ) ≤ ((c.TH - 1 / 100 : ℚ) : ℝ) := by
    exact_mod_cast k10
  have r11 : ((qabs (qsub (qderiv c.pt) c.pp) c.h : ℚ) : ℝ) ≤ (c.ε : ℝ) := by exact_mod_cast k11
  have r12 : ((qabs (defect2 c) c.h + (c.t0 + c.h) * c.γ : ℚ) : ℝ) ≤ ((c.ε * c.t0 : ℚ) : ℝ) := by
    exact_mod_cast k12
  have r13 : ((c.δ * (1 / (1 - c.K * c.h)) + c.ε / c.K * (1 / (1 - c.K * c.h) - 1) : ℚ) : ℝ) ≤
      (c.B : ℝ) := by exact_mod_cast k13
  push_cast at r5 rTS r9 r10 r12 r13 r14
  refine cell c.pt c.pp (T := (T : ℝ)) (t0 := (c.t0 : ℝ)) (h := (c.h : ℝ)) (δ := (c.δ : ℝ))
    (ε := (c.ε : ℝ)) (B := (c.B : ℝ)) (TH := (c.TH : ℝ)) (K := (c.K : ℝ)) (S := (c.S : ℝ))
    (by exact_mod_cast k1) (by exact_mod_cast k2) (by exact_mod_cast k3) (by exact_mod_cast k4)
    (by exact_mod_cast kS0) rTS
    (by linarith [r5]) (by exact_mod_cast k6) (by exact_mod_cast k7) (by exact_mod_cast k8)
    hθ hφ ?_ ?_ ?_ ?_ (by rw [evalQ_zero_head]; exact h0) (by rw [evalQ_zero_head]; exact h0')
    r13 r14
  · intro σ hσ
    have := lower_q c.pt (h := c.h) hσ.1 hσ.2
    push_cast at this; linarith
  · intro σ hσ
    have := upper_q c.pt (h := c.h) hσ.1 hσ.2
    push_cast at this; linarith
  · intro σ hσ
    rw [dEvalQ_eq, ← evalQ_qsub]
    exact (abs_le_qabs _ hσ.1 hσ.2).trans r11
  · intro σ hσ
    have hD := abs_le_qabs (defect2 c) hσ.1 hσ.2
    rw [← defect2_eval] at hD
    have hG := gam_bound c kg hσ.1 hσ.2
    have hσh : (c.t0 : ℝ) + σ ≤ c.t0 + c.h := by linarith [hσ.2]
    have ht0σ : (0 : ℝ) ≤ c.t0 + σ := by
      have : (0 : ℝ) < c.t0 := by exact_mod_cast k1
      linarith [hσ.1]
    have e : ((c.t0 : ℝ) + σ) * dEvalQ c.pp σ + 2 * evalQ c.pp σ +
        ((c.t0 : ℝ) + σ) * g32 (evalQ c.pt σ) =
        (((c.t0 : ℝ) + σ) * dEvalQ c.pp σ + 2 * evalQ c.pp σ +
          ((c.t0 : ℝ) + σ) * evalQ c.pw σ ^ 3) +
        ((c.t0 : ℝ) + σ) * (g32 (evalQ c.pt σ) - evalQ c.pw σ ^ 3) := by ring
    rw [e]
    calc _ ≤ |((c.t0 : ℝ) + σ) * dEvalQ c.pp σ + 2 * evalQ c.pp σ +
          ((c.t0 : ℝ) + σ) * evalQ c.pw σ ^ 3| +
          |((c.t0 : ℝ) + σ) * (g32 (evalQ c.pt σ) - evalQ c.pw σ ^ 3)| := abs_add_le _ _
      _ ≤ ((qabs (defect2 c) c.h : ℚ) : ℝ) + (c.t0 + c.h) * c.γ := by
          rw [abs_mul, abs_of_nonneg ht0σ]
          exact add_le_add hD (mul_le_mul hσh hG (abs_nonneg _) (by
            have : (0 : ℝ) < c.t0 := by exact_mod_cast k1
            have : (0 : ℝ) < c.h := by exact_mod_cast k3
            linarith))
      _ ≤ c.ε * c.t0 := r12

