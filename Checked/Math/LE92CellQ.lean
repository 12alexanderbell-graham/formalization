import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Checked.Sim.ODETools
import Checked.Sim.QPoly
import Checked.Math.LE92Cell

/-! Lane–Emden equation of index nine halves: the validated cells of `Checked.Math.LE92Cell.cell` checked by kernel evaluation. All side conditions and both defect bounds of a cell are one proposition over the rationals (`CellProp`); the power of the Taylor polynomial is replaced in the defect by the ninth power of a polynomial `pw` whose square is certified close to it and which is bounded away from zero, and in a cell next to the zero of θ (`pw` empty) it is bounded crudely. Each cell carries its own weight of φ; the links between cells rescale the radius by the ratio of the weights (`linkOK`). Promoted verbatim from `Work/Math/LE92CellQ.lean`. -/

namespace Checked.Math.LE92CellQ
open Set Checked.Sim Checked.Sim.QPoly Checked.Math.LENCell Checked.Math.LE92Cell

/-- One cell: start time `t0`, length `h`, input radius `δ` around the constant terms of the
Taylor polynomials `pt` (θ) and `pp` (φ) in σ = t − t0 in the norm max(|Δθ|, w |Δφ|), defect bound
`ε`, output radius `B`, slab half-width `TH` with `TH ≤ S ^ 2`, Lipschitz constant `K`; `pw`
approximates √θ (empty in a crude cell), `c` and `P` bound `pw` (in a crude cell `P ^ 2` bounds
`pt`), `η` bounds `pw ^ 2 − pt`, `γ` bounds the error of `pw ^ 9` against θ ^ (9/2) of `pt`, and
`w` is the weight of φ. -/
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
  w : ℚ

/-- The ninth power of a polynomial. -/
def qnon (p : List ℚ) : List ℚ :=
  qmul (qmul (qmul (qmul p p) (qmul p p)) (qmul (qmul p p) (qmul p p))) p

theorem evalQ_qnon (p : List ℚ) (s : ℝ) : evalQ (qnon p) s = evalQ p s ^ 9 := by
  simp only [qnon, evalQ_qmul]; ring

/-- The multiplied-out defect of the second component with `pw ^ 9` for θ ^ (9/2):
(t0+σ)pp' + 2pp + (t0+σ)pw⁹. -/
def defect2 (c : Cell) : List ℚ :=
  qadd (qadd (qmul [c.t0, 1] (qderiv c.pp)) (qsmul 2 c.pp)) (qmul [c.t0, 1] (qnon c.pw))

/-- The bound `γ` on |θ ^ (9/2) of `pt` − `pw ^ 9|: crude (`pw = []`) or from the square
certificate. -/
def GamProp (c : Cell) : Prop :=
  (c.pw = [] ∧ 0 ≤ c.P ∧ c.pt.headD 0 + c.h * qabs c.pt.tail c.h ≤ c.P ^ 2 ∧ c.P ^ 9 ≤ c.γ) ∨
  (0 < c.c ∧ c.c ≤ c.pw.headD 0 - c.h * qabs c.pw.tail c.h ∧
    c.pw.headD 0 + c.h * qabs c.pw.tail c.h ≤ c.P ∧
    qabs (qsub (qmul c.pw c.pw) c.pt) c.h ≤ c.η ∧ c.η < c.c ^ 2 ∧
    c.η / c.c * (9 * (c.P ^ 2 + c.η) ^ 4) ≤ c.γ)

instance (c : Cell) : Decidable (GamProp c) := by unfold GamProp; infer_instance

/-- All hypotheses of `LE92Cell.cell` except the solution's own, as one proposition over ℚ. -/
def CellProp (T : ℚ) (c : Cell) : Prop :=
  0 < c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h ∧ 0 < c.w ∧ 1 ≤ c.w * c.K ∧ 0 ≤ c.S ∧ c.TH ≤ c.S ^ 2 ∧
  2 / c.t0 + c.w * (9 / 2 * c.S ^ 7) ≤ c.K ∧ c.K * c.h < 1 ∧
  0 ≤ c.δ ∧ 0 ≤ c.ε ∧
  -(c.TH - 1 / 100) ≤ c.pt.headD 0 - c.h * qabs c.pt.tail c.h ∧
  c.pt.headD 0 + c.h * qabs c.pt.tail c.h ≤ c.TH - 1 / 100 ∧
  qabs (qsub (qderiv c.pt) c.pp) c.h ≤ c.ε ∧
  c.w * (qabs (defect2 c) c.h + (c.t0 + c.h) * c.γ) ≤ c.ε * c.t0 ∧
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

theorem cellOK_w {T : ℚ} (c : Cell) (hok : cellOK T c = true) : (0 : ℝ) < c.w := by
  obtain ⟨-, -, -, k, -⟩ : CellProp T c := of_decide_eq_true hok
  exact_mod_cast k

theorem defect2_eval (c : Cell) (σ : ℝ) :
    ((c.t0 : ℝ) + σ) * dEvalQ c.pp σ + 2 * evalQ c.pp σ +
      ((c.t0 : ℝ) + σ) * evalQ c.pw σ ^ 9 = evalQ (defect2 c) σ := by
  simp only [defect2, evalQ_qadd, evalQ_qsmul, evalQ_qmul, evalQ_qnon, ← dEvalQ_eq, evalQ]
  push_cast; ring

/-- The γ bound from its rational certificate. -/
theorem gam_bound (c : Cell) (hg : GamProp c) {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ c.h) :
    |g92 (evalQ c.pt σ) - evalQ c.pw σ ^ 9| ≤ c.γ := by
  rcases hg with ⟨hpw, hP0, hpt, hγ⟩ | ⟨hc, hlo, hhi, hη, hηc, hγ⟩
  · have hP0' : (0 : ℝ) ≤ c.P := by exact_mod_cast hP0
    have hu := upper_q c.pt h0 h1
    have hpt' : ((c.pt.headD 0 + c.h * qabs c.pt.tail c.h : ℚ) : ℝ) ≤ ((c.P ^ 2 : ℚ) : ℝ) := by
      exact_mod_cast hpt
    have hγ' : ((c.P ^ 9 : ℚ) : ℝ) ≤ c.γ := by exact_mod_cast hγ
    push_cast at hpt' hγ'
    have hs : Real.sqrt (evalQ c.pt σ) ≤ c.P := by
      calc Real.sqrt (evalQ c.pt σ) ≤ Real.sqrt ((c.P : ℝ) ^ 2) := Real.sqrt_le_sqrt (by
            push_cast at hu; linarith)
        _ = c.P := Real.sqrt_sq hP0'
    rw [hpw]
    simp only [evalQ]
    rw [zero_pow (by norm_num), sub_zero, abs_of_nonneg (g92_nonneg _)]
    unfold g92
    calc Real.sqrt (evalQ c.pt σ) ^ 9 ≤ (c.P : ℝ) ^ 9 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 9
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
    have hγ' : ((c.η / c.c * (9 * (c.P ^ 2 + c.η) ^ 4) : ℚ) : ℝ) ≤ c.γ := by exact_mod_cast hγ
    push_cast at hηc' hγ'
    have hsq : |evalQ c.pw σ ^ 2 - evalQ c.pt σ| ≤ c.η := by
      have := abs_le_qabs (qsub (qmul c.pw c.pw) c.pt) h0 h1
      rw [evalQ_qsub, evalQ_qmul] at this
      rw [sq]; exact this.trans hη'
    exact (g92_close hc' (hlo'.trans hl) (hu.trans hhi') hsq hηc').trans hγ'

/-- One validated cell from its Boolean check. -/
theorem cell_q {T : ℚ} (c : Cell) (hok : cellOK T c = true) {θ φ : ℝ → ℝ}
    (hθ : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), HasDerivWithinAt θ (φ t) (Icc 0 (T : ℝ)) t)
    (hφ : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt φ (-(2 / t * φ t) - g92 (θ t)) (Icc 0 (T : ℝ)) t)
    (h0 : |θ c.t0 - ((c.pt.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : (c.w : ℝ) * |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      |θ t - evalQ c.pt (t - c.t0)| ≤ c.B ∧ (c.w : ℝ) * |φ t - evalQ c.pp (t - c.t0)| ≤ c.B := by
  obtain ⟨k1, k2, k3, kw, k4, kS0, kTS, k5, k6, k7, k8, k9, k10, k11, k12, kg, k13, k14⟩ :
    CellProp T c := of_decide_eq_true hok
  have r14 : ((c.B : ℚ) : ℝ) < ((1 / 100 : ℚ) : ℝ) := by exact_mod_cast k14
  have r5 : ((2 / c.t0 + c.w * (9 / 2 * c.S ^ 7) : ℚ) : ℝ) ≤ (c.K : ℝ) := by exact_mod_cast k5
  have rw0 : (0 : ℝ) < c.w := by exact_mod_cast kw
  have r4 : ((1 : ℚ) : ℝ) ≤ ((c.w * c.K : ℚ) : ℝ) := by exact_mod_cast k4
  have rTS : ((c.TH : ℚ) : ℝ) ≤ ((c.S ^ 2 : ℚ) : ℝ) := by exact_mod_cast kTS
  have r9 : ((-(c.TH - 1 / 100) : ℚ) : ℝ) ≤ ((c.pt.headD 0 - c.h * qabs c.pt.tail c.h : ℚ) : ℝ) := by
    exact_mod_cast k9
  have r10 : ((c.pt.headD 0 + c.h * qabs c.pt.tail c.h : ℚ) : ℝ) ≤ ((c.TH - 1 / 100 : ℚ) : ℝ) := by
    exact_mod_cast k10
  have r11 : ((qabs (qsub (qderiv c.pt) c.pp) c.h : ℚ) : ℝ) ≤ (c.ε : ℝ) := by exact_mod_cast k11
  have r12 : ((c.w * (qabs (defect2 c) c.h + (c.t0 + c.h) * c.γ) : ℚ) : ℝ) ≤
      ((c.ε * c.t0 : ℚ) : ℝ) := by
    exact_mod_cast k12
  have r13 : ((c.δ * (1 / (1 - c.K * c.h)) + c.ε / c.K * (1 / (1 - c.K * c.h) - 1) : ℚ) : ℝ) ≤
      (c.B : ℝ) := by exact_mod_cast k13
  push_cast at r4 r5 rTS r9 r10 r12 r13 r14
  refine cell c.pt c.pp (w := (c.w : ℝ)) (T := (T : ℝ)) (t0 := (c.t0 : ℝ)) (h := (c.h : ℝ))
    (δ := (c.δ : ℝ))
    (ε := (c.ε : ℝ)) (B := (c.B : ℝ)) (TH := (c.TH : ℝ)) (K := (c.K : ℝ)) (S := (c.S : ℝ)) rw0
    (by exact_mod_cast k1) (by exact_mod_cast k2) (by exact_mod_cast k3) r4
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
    refine le_trans ?_ r12
    refine mul_le_mul_of_nonneg_left ?_ rw0.le
    have e : ((c.t0 : ℝ) + σ) * dEvalQ c.pp σ + 2 * evalQ c.pp σ +
        ((c.t0 : ℝ) + σ) * g92 (evalQ c.pt σ) =
        (((c.t0 : ℝ) + σ) * dEvalQ c.pp σ + 2 * evalQ c.pp σ +
          ((c.t0 : ℝ) + σ) * evalQ c.pw σ ^ 9) +
        ((c.t0 : ℝ) + σ) * (g92 (evalQ c.pt σ) - evalQ c.pw σ ^ 9) := by ring
    rw [e]
    calc _ ≤ |((c.t0 : ℝ) + σ) * dEvalQ c.pp σ + 2 * evalQ c.pp σ +
          ((c.t0 : ℝ) + σ) * evalQ c.pw σ ^ 9| +
          |((c.t0 : ℝ) + σ) * (g92 (evalQ c.pt σ) - evalQ c.pw σ ^ 9)| := abs_add_le _ _
      _ ≤ ((qabs (defect2 c) c.h : ℚ) : ℝ) + (c.t0 + c.h) * c.γ := by
          rw [abs_mul, abs_of_nonneg ht0σ]
          exact add_le_add hD (mul_le_mul hσh hG (abs_nonneg _) (by
            have : (0 : ℝ) < c.t0 := by exact_mod_cast k1
            have : (0 : ℝ) < c.h := by exact_mod_cast k3
            linarith))

/-- Consecutive cells meet, and the end enclosure of `c` lies in the input box of `d` (the
φ radius rescaled by the ratio of the weights). -/
def linkOK (c d : Cell) : Bool :=
  decide (c.t0 + c.h = d.t0 ∧ 0 < c.w ∧ 0 < d.w ∧
    |qeval c.pt c.h - d.pt.headD 0| + c.B ≤ d.δ ∧
    d.w * |qeval c.pp c.h - d.pp.headD 0| + d.w / c.w * c.B ≤ d.δ)

/-- θ stays positive on the cell. -/
def posOK (c : Cell) : Bool := decide (0 < c.pt.headD 0 - c.h * qabs c.pt.tail c.h - c.B)

/-- φ stays negative on the cell. -/
def negOK (c : Cell) : Bool :=
  decide (c.w * (c.pp.headD 0 + c.h * qabs c.pp.tail c.h) + c.B < 0)

/-- A chain of cells inside [0, T] whose last cell satisfies `term`. -/
def chainTo (T : ℚ) (pos neg : Bool) (term : Cell → Bool) : List Cell → Bool
  | [] => false
  | [c] => cellOK T c && (!pos || posOK c) && (!neg || negOK c) && term c
  | c :: d :: l => cellOK T c && (!pos || posOK c) && (!neg || negOK c) && linkOK c d &&
      chainTo T pos neg term (d :: l)

/-- A segment of a chain, ending in the input box of the cell `d`. -/
def segOK (T : ℚ) (pos neg : Bool) (d : Cell) (l : List Cell) : Bool :=
  chainTo T pos neg (fun c => linkOK c d) l

theorem chainTo_head {T : ℚ} {pos neg : Bool} {term : Cell → Bool} (c : Cell) (l : List Cell)
    (h : chainTo T pos neg term (c :: l) = true) : cellOK T c = true := by
  cases l with
  | nil => simp only [chainTo, Bool.and_eq_true] at h; exact h.1.1.1
  | cons _ _ => simp only [chainTo, Bool.and_eq_true] at h; exact h.1.1.1.1

/-- What one cell gives: the end enclosure and the sign invariants on the cell. -/
theorem cell_facts {T : ℚ} {pos neg : Bool} (c : Cell) (hok : cellOK T c = true)
    (hp : (!pos || posOK c) = true) (hn : (!neg || negOK c) = true) {θ φ : ℝ → ℝ}
    (hθ : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), HasDerivWithinAt θ (φ t) (Icc 0 (T : ℝ)) t)
    (hφ : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt φ (-(2 / t * φ t) - g92 (θ t)) (Icc 0 (T : ℝ)) t)
    (h0 : |θ c.t0 - ((c.pt.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : (c.w : ℝ) * |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (pos = true → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), 0 < θ t) ∧
    (neg = true → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), φ t < 0) ∧
    |θ (c.t0 + c.h) - ((qeval c.pt c.h : ℚ) : ℝ)| ≤ c.B ∧
    (c.w : ℝ) * |φ (c.t0 + c.h) - ((qeval c.pp c.h : ℚ) : ℝ)| ≤ c.B := by
  have hc := cell_q c hok hθ hφ h0 h0'
  have hh : (0 : ℝ) < c.h := by exact_mod_cast (cellOK_basic c hok).2.2
  have hw := cellOK_w c hok
  refine ⟨fun hpos t ht => ?_, fun hneg t ht => ?_, ?_, ?_⟩
  · subst hpos
    simp only [Bool.not_true, Bool.false_or, posOK] at hp
    have hp := of_decide_eq_true hp
    have hp' : ((0 : ℚ) : ℝ) < ((c.pt.headD 0 - c.h * qabs c.pt.tail c.h - c.B : ℚ) : ℝ) := by
      exact_mod_cast hp
    have hl := lower_q c.pt (h := c.h) (σ := t - c.t0) (by linarith [ht.1]) (by linarith [ht.2])
    have e := abs_le.1 (hc t ht).1
    push_cast at hp' hl
    linarith [e.1]
  · subst hneg
    simp only [Bool.not_true, Bool.false_or, negOK] at hn
    have hn := of_decide_eq_true hn
    have hn' : ((c.w * (c.pp.headD 0 + c.h * qabs c.pp.tail c.h) + c.B : ℚ) : ℝ) <
        ((0 : ℚ) : ℝ) := by
      exact_mod_cast hn
    have hu := upper_q c.pp (h := c.h) (σ := t - c.t0) (by linarith [ht.1]) (by linarith [ht.2])
    have e := (hc t ht).2
    push_cast at hn' hu
    have e2 : (c.w : ℝ) * (φ t - evalQ c.pp (t - c.t0)) ≤ c.B :=
      (mul_le_mul_of_nonneg_left (le_abs_self _) hw.le).trans e
    have e3 : (c.w : ℝ) * φ t < 0 := by nlinarith
    by_contra hcon
    push_neg at hcon
    have : (0 : ℝ) ≤ c.w * φ t := mul_nonneg hw.le hcon
    linarith
  · have e := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).1
    rwa [add_sub_cancel_left, ← qeval_cast] at e
  · have e := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).2
    rwa [add_sub_cancel_left, ← qeval_cast] at e

theorem abs_link {x v w B r : ℝ} (h1 : |x - v| ≤ B) (h2 : |v - w| + B ≤ r) : |x - w| ≤ r := by
  have := abs_sub_le x v w
  linarith

/-- The weighted link: from weight `a` to weight `b`. -/
theorem abs_linkw {x v u B r a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h1 : a * |x - v| ≤ B)
    (h2 : b * |v - u| + b / a * B ≤ r) : b * |x - u| ≤ r := by
  have h3 : b * |x - v| ≤ b / a * B := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]
    have := mul_le_mul_of_nonneg_left h1 hb.le
    linarith [this, show b * |x - v| * a = b * (a * |x - v|) by ring]
  calc b * |x - u| ≤ b * (|x - v| + |v - u|) := mul_le_mul_of_nonneg_left (abs_sub_le x v u) hb.le
    _ = b * |x - v| + b * |v - u| := by ring
    _ ≤ r := by linarith

/-- The link of two cells from its Boolean check. -/
theorem link_q (c d : Cell) (hl : linkOK c d = true) {x y : ℝ}
    (hx : |x - ((qeval c.pt c.h : ℚ) : ℝ)| ≤ c.B)
    (hy : (c.w : ℝ) * |y - ((qeval c.pp c.h : ℚ) : ℝ)| ≤ c.B) :
    ((c.t0 + c.h : ℚ) : ℝ) = (d.t0 : ℝ) ∧ |x - ((d.pt.headD 0 : ℚ) : ℝ)| ≤ d.δ ∧
      (d.w : ℝ) * |y - ((d.pp.headD 0 : ℚ) : ℝ)| ≤ d.δ := by
  obtain ⟨ke, kc, kd, kθ, kφ⟩ := of_decide_eq_true hl
  have kθ' : |((qeval c.pt c.h : ℚ) : ℝ) - ((d.pt.headD 0 : ℚ) : ℝ)| + c.B ≤ d.δ := by
    exact_mod_cast kθ
  have kφ' : (d.w : ℝ) * |((qeval c.pp c.h : ℚ) : ℝ) - ((d.pp.headD 0 : ℚ) : ℝ)| +
      (d.w : ℝ) / c.w * c.B ≤ d.δ := by
    exact_mod_cast kφ
  exact ⟨by exact_mod_cast ke, abs_link hx kθ',
    abs_linkw (by exact_mod_cast kc) (by exact_mod_cast kd) hy kφ'⟩

/-- A chain from its Boolean check: some last cell `e` meets `term`, the solution is enclosed
at its end, and the sign invariants hold from the first cell's start to there. -/
theorem chain_gen {T : ℚ} {pos neg : Bool} {term : Cell → Bool} :
    ∀ (l : List Cell) (c : Cell), chainTo T pos neg term (c :: l) = true →
    ∀ {θ φ : ℝ → ℝ},
    (∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt θ (φ t) (Icc 0 (T : ℝ)) t) →
    (∀ t ∈ Icc (c.t0 : ℝ) T,
      HasDerivWithinAt φ (-(2 / t * φ t) - g92 (θ t)) (Icc 0 (T : ℝ)) t) →
    |θ c.t0 - ((c.pt.headD 0 : ℚ) : ℝ)| ≤ c.δ →
    (c.w : ℝ) * |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ →
    ∃ e : Cell, term e = true ∧ cellOK T e = true ∧ (c.t0 : ℝ) ≤ e.t0 + e.h ∧
    (pos = true → ∀ t ∈ Icc (c.t0 : ℝ) (e.t0 + e.h), 0 < θ t) ∧
    (neg = true → ∀ t ∈ Icc (c.t0 : ℝ) (e.t0 + e.h), φ t < 0) ∧
    |θ (e.t0 + e.h) - ((qeval e.pt e.h : ℚ) : ℝ)| ≤ e.B ∧
    (e.w : ℝ) * |φ (e.t0 + e.h) - ((qeval e.pp e.h : ℚ) : ℝ)| ≤ e.B := by
  intro l
  induction l with
  | nil =>
    intro c hok θ φ hθ hφ h0 h0'
    simp only [chainTo, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨k1, kp⟩, kn⟩, kt⟩ := hok
    obtain ⟨-, k2, -⟩ := cellOK_basic c k1
    have k2' : ((c.t0 + c.h : ℚ) : ℝ) ≤ T := by exact_mod_cast k2
    push_cast at k2'
    have hf := cell_facts c k1 kp kn (θ := θ) (φ := φ)
      (fun t ht => hθ t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht => hφ t ⟨ht.1, by linarith [ht.2]⟩) h0 h0'
    have hh : (0 : ℝ) < c.h := by exact_mod_cast (cellOK_basic c k1).2.2
    exact ⟨c, kt, k1, by linarith, hf⟩
  | cons d l ih =>
    intro c hok θ φ hθ hφ h0 h0'
    simp only [chainTo, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨⟨k1, kp⟩, kn⟩, kl⟩, krest⟩ := hok
    have he : ((c.t0 + c.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast (of_decide_eq_true kl).1
    push_cast at he
    have hdT : (d.t0 : ℝ) ≤ T := by
      obtain ⟨_, h2, h3⟩ := cellOK_basic d (chainTo_head d l krest)
      exact_mod_cast (by linarith : d.t0 ≤ T)
    have hf := cell_facts c k1 kp kn (θ := θ) (φ := φ)
      (fun t ht => hθ t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht => hφ t ⟨ht.1, by linarith [ht.2]⟩) h0 h0'
    obtain ⟨-, ha, hb⟩ := link_q c d kl hf.2.2.1 hf.2.2.2
    rw [he] at ha hb
    have hcd : (c.t0 : ℝ) ≤ d.t0 := by
      have : (0 : ℝ) < c.h := by exact_mod_cast (cellOK_basic c k1).2.2
      linarith
    rw [he] at hf
    obtain ⟨e, het, heok, hce, hpos, hneg, hb1, hb2⟩ := ih d krest (θ := θ) (φ := φ)
      (fun t ht => hθ t ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht => hφ t ⟨by linarith [ht.1], ht.2⟩) ha hb
    refine ⟨e, het, heok, by linarith, fun hp t ht => ?_, fun hn t ht => ?_, hb1, hb2⟩
    · rcases le_or_gt t d.t0 with h1 | h1
      · exact hf.1 hp t ⟨ht.1, h1⟩
      · exact hpos hp t ⟨h1.le, ht.2⟩
    · rcases le_or_gt t d.t0 with h1 | h1
      · exact hf.2.1 hn t ⟨ht.1, h1⟩
      · exact hneg hn t ⟨h1.le, ht.2⟩

/-- A segment of a chain from its Boolean check: the solution enters the input box of `d` at
`d.t0`, with the sign invariants up to there. -/
theorem seg_q {T : ℚ} {pos neg : Bool} (d : Cell) (l : List Cell) (c : Cell)
    (hok : segOK T pos neg d (c :: l) = true) {θ φ : ℝ → ℝ}
    (hθ : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt θ (φ t) (Icc 0 (T : ℝ)) t)
    (hφ : ∀ t ∈ Icc (c.t0 : ℝ) T,
      HasDerivWithinAt φ (-(2 / t * φ t) - g92 (θ t)) (Icc 0 (T : ℝ)) t)
    (h0 : |θ c.t0 - ((c.pt.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : (c.w : ℝ) * |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (c.t0 : ℝ) ≤ d.t0 ∧
    (pos = true → ∀ t ∈ Icc (c.t0 : ℝ) d.t0, 0 < θ t) ∧
    (neg = true → ∀ t ∈ Icc (c.t0 : ℝ) d.t0, φ t < 0) ∧
    |θ d.t0 - ((d.pt.headD 0 : ℚ) : ℝ)| ≤ d.δ ∧
    (d.w : ℝ) * |φ d.t0 - ((d.pp.headD 0 : ℚ) : ℝ)| ≤ d.δ := by
  obtain ⟨e, het, -, hce, hpos, hneg, hb1, hb2⟩ := chain_gen l c hok hθ hφ h0 h0'
  obtain ⟨he, ha, hb⟩ := link_q e d het hb1 hb2
  push_cast at he
  rw [he] at hce hpos hneg ha hb
  exact ⟨hce, hpos, hneg, ha, hb⟩

/-- A box with weight one is the unweighted box. -/
theorem w_one {c : Cell} (hw : c.w = 1) {x δ : ℝ} (h : |x| ≤ δ) : (c.w : ℝ) * |x| ≤ δ := by
  rw [hw]; push_cast; rw [one_mul]; exact h


theorem icc_glue {P : ℝ → Prop} {a b c : ℝ} (h1 : ∀ t ∈ Icc a b, P t) (h2 : ∀ t ∈ Icc b c, P t) :
    ∀ t ∈ Icc a c, P t := fun t ht => by
  rcases le_or_gt t b with h | h
  · exact h1 t ⟨ht.1, h⟩
  · exact h2 t ⟨h.le, ht.2⟩

theorem ioc_glue {P : ℝ → Prop} {a b c : ℝ} (h1 : ∀ t ∈ Ioc a b, P t) (h2 : ∀ t ∈ Icc b c, P t) :
    ∀ t ∈ Ioc a c, P t := fun t ht => by
  rcases le_or_gt t b with h | h
  · exact h1 t ⟨ht.1, h⟩
  · exact h2 t ⟨h.le, ht.2⟩

end Checked.Math.LE92CellQ
