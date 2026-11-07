import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Checked.Sim.ODETools
import Checked.Sim.QPoly
import Checked.Math.LECell
import Checked.Math.GCell

/-! Gelfand problem, `GCellQ`: the validated cells of `Checked.Math.GCell.cell` checked by kernel evaluation. All side conditions and both defect bounds of a cell, and the positivity invariant carried along the chain, are one proposition over the rationals, with the defect polynomials computed from the cell's Taylor polynomials (`Checked.Sim.QPoly`) instead of supplied and proved by `ring`; a chain of cells is one Boolean, decided by the kernel. -/

namespace Checked.Math.GCellQ
open Set Checked.Sim Checked.Sim.QPoly Checked.Math.GCell

/-- One cell: start `t0`, length `h`, input radius `δ` around the constant terms of the Taylor
polynomials `pe` (of E) and `pp` (of φ) in σ = t − t0, defect bound `ε`, output radius `B`, box
half-widths `EH`, `PH` and Lipschitz constant `K`. -/
structure Cell where
  t0 : ℚ
  h : ℚ
  δ : ℚ
  ε : ℚ
  B : ℚ
  EH : ℚ
  PH : ℚ
  K : ℚ
  pe : List ℚ
  pp : List ℚ

/-- Lower bound c₀ − h·Σ|cₖ₊₁|hᵏ of a polynomial on [0, h]. -/
def lo (p : List ℚ) (h : ℚ) : ℚ := p.headD 0 - h * qabs p.tail h

/-- Upper bound c₀ + h·Σ|cₖ₊₁|hᵏ of a polynomial on [0, h]. -/
def hi (p : List ℚ) (h : ℚ) : ℚ := p.headD 0 + h * qabs p.tail h

/-- pe′ − pe·pp, computed. -/
def defect1 (c : Cell) : List ℚ := qsub (qderiv c.pe) (qmul c.pe c.pp)

/-- (t0+σ)pp′ + 2pp + (t0+σ)pe, computed. -/
def defect2 (c : Cell) : List ℚ :=
  qadd (qadd (qmul [c.t0, 1] (qderiv c.pp)) (qsmul 2 c.pp)) (qmul [c.t0, 1] c.pe)

/-- 2 + (t0+σ)pp, computed. -/
def invA (c : Cell) : List ℚ := qadd [2] (qmul [c.t0, 1] c.pp)

/-- pp + (t0+σ)pe, computed. -/
def invB (c : Cell) : List ℚ := qadd c.pp (qmul [c.t0, 1] c.pe)

/-- All hypotheses of `GCell.cell` except the solution's own, as one proposition over ℚ. -/
def CellProp (T : ℚ) (c : Cell) : Prop :=
  0 < c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h ∧ 1 ≤ c.K ∧ c.PH + c.EH ≤ c.K ∧ 2 / c.t0 + 1 ≤ c.K ∧
  c.K * c.h < 1 ∧ 0 ≤ c.δ ∧ 0 ≤ c.ε ∧
  -(c.EH - 1 / 100) ≤ lo c.pe c.h ∧ hi c.pe c.h ≤ c.EH - 1 / 100 ∧
  -(c.PH - 1 / 100) ≤ lo c.pp c.h ∧ hi c.pp c.h ≤ c.PH - 1 / 100 ∧
  qabs (defect1 c) c.h ≤ c.ε ∧ qabs (defect2 c) c.h ≤ c.ε * c.t0 ∧
  c.δ * (1 / (1 - c.K * c.h)) + c.ε / c.K * (1 / (1 - c.K * c.h) - 1) ≤ c.B ∧
  c.B < 1 / 100

instance (T : ℚ) (c : Cell) : Decidable (CellProp T c) := by unfold CellProp; infer_instance

/-- The invariant of the chain on a cell: 2 + tφ > 0 (`false`) or φ + tE > 0 (`true`). -/
def InvProp (m : Bool) (c : Cell) : Prop :=
  match m with
  | false => 0 < lo (invA c) c.h - (c.t0 + c.h) * c.B
  | true => 0 < lo (invB c) c.h - (1 + (c.t0 + c.h)) * c.B

instance (m : Bool) (c : Cell) : Decidable (InvProp m c) := by
  cases m <;> (unfold InvProp; infer_instance)

/-- The invariant as a statement about the solution at time t. -/
def Inv (m : Bool) (E φ : ℝ → ℝ) (t : ℝ) : Prop :=
  match m with
  | false => 0 < 2 + t * φ t
  | true => 0 < φ t + t * E t

/-- Cell conditions and invariant, as a Boolean for evaluation by the kernel. -/
def cellOK (T : ℚ) (m : Bool) (c : Cell) : Bool := decide (CellProp T c) && decide (InvProp m c)

theorem lo_le (p : List ℚ) {h : ℚ} {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ h) :
    ((lo p h : ℚ) : ℝ) ≤ evalQ p σ := lower_q p h0 h1

theorem le_hi (p : List ℚ) {h : ℚ} {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ h) :
    evalQ p σ ≤ ((hi p h : ℚ) : ℝ) := upper_q p h0 h1

theorem defect1_eval (c : Cell) (σ : ℝ) :
    dEvalQ c.pe σ - evalQ c.pe σ * evalQ c.pp σ = evalQ (defect1 c) σ := by
  simp only [defect1, evalQ_qsub, evalQ_qmul, ← dEvalQ_eq]

theorem defect2_eval (c : Cell) (σ : ℝ) :
    ((c.t0 : ℝ) + σ) * dEvalQ c.pp σ + 2 * evalQ c.pp σ + ((c.t0 : ℝ) + σ) * evalQ c.pe σ =
      evalQ (defect2 c) σ := by
  simp only [defect2, evalQ_qadd, evalQ_qsmul, evalQ_qmul, ← dEvalQ_eq, evalQ]
  push_cast; ring

theorem invA_eval (c : Cell) (σ : ℝ) :
    2 + ((c.t0 : ℝ) + σ) * evalQ c.pp σ = evalQ (invA c) σ := by
  simp only [invA, evalQ_qadd, evalQ_qmul, evalQ]; push_cast; ring

theorem invB_eval (c : Cell) (σ : ℝ) :
    evalQ c.pp σ + ((c.t0 : ℝ) + σ) * evalQ c.pe σ = evalQ (invB c) σ := by
  simp only [invB, evalQ_qadd, evalQ_qmul, evalQ]; push_cast; ring

theorem cell_basic {T : ℚ} {m : Bool} (c : Cell) (hok : cellOK T m c = true) :
    0 < c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h := by
  simp only [cellOK, Bool.and_eq_true] at hok
  obtain ⟨k1, k2, k3, -⟩ : CellProp T c := of_decide_eq_true hok.1
  exact ⟨k1, k2, k3⟩

/-- One validated cell from its Boolean check. -/
theorem cell_q {T : ℚ} (c : Cell) (hok : decide (CellProp T c) = true) {E φ : ℝ → ℝ}
    (hE : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), HasDerivWithinAt E (E t * φ t) (Icc 0 (T : ℝ)) t)
    (hφ : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt φ (-(2 / t * φ t) - E t) (Icc 0 (T : ℝ)) t)
    (h0 : |E c.t0 - ((c.pe.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      |E t - evalQ c.pe (t - c.t0)| ≤ c.B ∧ |φ t - evalQ c.pp (t - c.t0)| ≤ c.B := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17⟩ :
    CellProp T c := of_decide_eq_true hok
  have r5 : ((c.PH + c.EH : ℚ) : ℝ) ≤ (c.K : ℝ) := by exact_mod_cast k5
  have r6 : ((2 / c.t0 + 1 : ℚ) : ℝ) ≤ (c.K : ℝ) := by exact_mod_cast k6
  have r10 : ((-(c.EH - 1 / 100) : ℚ) : ℝ) ≤ ((lo c.pe c.h : ℚ) : ℝ) := by exact_mod_cast k10
  have r11 : ((hi c.pe c.h : ℚ) : ℝ) ≤ ((c.EH - 1 / 100 : ℚ) : ℝ) := by exact_mod_cast k11
  have r12 : ((-(c.PH - 1 / 100) : ℚ) : ℝ) ≤ ((lo c.pp c.h : ℚ) : ℝ) := by exact_mod_cast k12
  have r13 : ((hi c.pp c.h : ℚ) : ℝ) ≤ ((c.PH - 1 / 100 : ℚ) : ℝ) := by exact_mod_cast k13
  have r14 : ((qabs (defect1 c) c.h : ℚ) : ℝ) ≤ (c.ε : ℝ) := by exact_mod_cast k14
  have r15 : ((qabs (defect2 c) c.h : ℚ) : ℝ) ≤ ((c.ε * c.t0 : ℚ) : ℝ) := by exact_mod_cast k15
  have r16 : ((c.δ * (1 / (1 - c.K * c.h)) + c.ε / c.K * (1 / (1 - c.K * c.h) - 1) : ℚ) : ℝ) ≤
      (c.B : ℝ) := by exact_mod_cast k16
  have r17 : ((c.B : ℚ) : ℝ) < ((1 / 100 : ℚ) : ℝ) := by exact_mod_cast k17
  push_cast at r5 r6 r10 r11 r12 r13 r15 r16 r17
  refine cell c.pe c.pp (E := E) (φ := φ) (T := (T : ℝ)) (t0 := (c.t0 : ℝ)) (h := (c.h : ℝ))
    (δ := (c.δ : ℝ)) (ε := (c.ε : ℝ)) (B := (c.B : ℝ)) (EH := (c.EH : ℝ)) (PH := (c.PH : ℝ))
    (K := (c.K : ℝ))
    (by exact_mod_cast k1) (by exact_mod_cast k2) (by exact_mod_cast k3) (by exact_mod_cast k4)
    r5 r6 (by exact_mod_cast k7) (by exact_mod_cast k8) (by exact_mod_cast k9)
    hE hφ ?_ ?_ ?_ ?_ ?_ ?_ (by rw [evalQ_zero_head]; exact h0) (by rw [evalQ_zero_head]; exact h0')
    r16 r17
  · intro σ hσ; have := lo_le c.pe (h := c.h) hσ.1 hσ.2; linarith
  · intro σ hσ; have := le_hi c.pe (h := c.h) hσ.1 hσ.2; linarith
  · intro σ hσ; have := lo_le c.pp (h := c.h) hσ.1 hσ.2; linarith
  · intro σ hσ; have := le_hi c.pp (h := c.h) hσ.1 hσ.2; linarith
  · intro σ hσ
    rw [defect1_eval]
    exact (abs_le_qabs _ hσ.1 hσ.2).trans r14
  · intro σ hσ
    rw [defect2_eval]
    exact (abs_le_qabs _ hσ.1 hσ.2).trans r15

/-- What one cell gives: the invariant on the cell and the end enclosure. -/
theorem cell_facts {T : ℚ} {m : Bool} (c : Cell) (hok : cellOK T m c = true) {E φ : ℝ → ℝ}
    (hE : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), HasDerivWithinAt E (E t * φ t) (Icc 0 (T : ℝ)) t)
    (hφ : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt φ (-(2 / t * φ t) - E t) (Icc 0 (T : ℝ)) t)
    (h0 : |E c.t0 - ((c.pe.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), Inv m E φ t) ∧
    |E (c.t0 + c.h) - ((qeval c.pe c.h : ℚ) : ℝ)| ≤ c.B ∧
    |φ (c.t0 + c.h) - ((qeval c.pp c.h : ℚ) : ℝ)| ≤ c.B := by
  have hok' := hok
  simp only [cellOK, Bool.and_eq_true] at hok'
  have hc := cell_q c hok'.1 hE hφ h0 h0'
  obtain ⟨k1, -, k3⟩ := cell_basic c hok
  have ht0 : (0 : ℝ) < c.t0 := by exact_mod_cast k1
  have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
  refine ⟨fun t ht => ?_, ?_, ?_⟩
  · have hσ0 : 0 ≤ t - c.t0 := by linarith [ht.1]
    have hσ1 : t - c.t0 ≤ c.h := by linarith [ht.2]
    have et : (c.t0 : ℝ) + (t - c.t0) = t := by ring
    obtain ⟨e1, e2⟩ := hc t ht
    have hB0 : (0 : ℝ) ≤ c.B := (abs_nonneg _).trans e1
    have htB : t * c.B ≤ (c.t0 + c.h) * c.B := mul_le_mul_of_nonneg_right ht.2 hB0
    have t0' : 0 ≤ t := by linarith [ht.1]
    have a1 := abs_le.1 e1
    have a2 := abs_le.1 e2
    cases m with
    | false =>
      have kv := of_decide_eq_true hok'.2
      have rv : ((0 : ℚ) : ℝ) < ((lo (invA c) c.h - (c.t0 + c.h) * c.B : ℚ) : ℝ) := by
        exact_mod_cast kv
      push_cast at rv
      have hl := lo_le (invA c) hσ0 hσ1
      rw [← invA_eval, et] at hl
      have m1 : -(t * c.B) ≤ t * (φ t - evalQ c.pp (t - c.t0)) := by nlinarith [a2.1, a2.2]
      show 0 < 2 + t * φ t
      nlinarith
    | true =>
      have kv := of_decide_eq_true hok'.2
      have rv : ((0 : ℚ) : ℝ) < ((lo (invB c) c.h - (1 + (c.t0 + c.h)) * c.B : ℚ) : ℝ) := by
        exact_mod_cast kv
      push_cast at rv
      have hl := lo_le (invB c) hσ0 hσ1
      rw [← invB_eval, et] at hl
      have m1 : -(t * c.B) ≤ t * (E t - evalQ c.pe (t - c.t0)) := by nlinarith [a1.1, a1.2]
      show 0 < φ t + t * E t
      nlinarith
  · have e := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).1
    rwa [add_sub_cancel_left, ← qeval_cast] at e
  · have e := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).2
    rwa [add_sub_cancel_left, ← qeval_cast] at e

/-- Consecutive cells meet, and the end enclosure of `c` lies in the input box of `d`. -/
def linkOK (c d : Cell) : Bool :=
  decide (c.t0 + c.h = d.t0 ∧
    |qeval c.pe c.h - d.pe.headD 0| + c.B ≤ d.δ ∧
    |qeval c.pp c.h - d.pp.headD 0| + c.B ≤ d.δ)

/-- A chain of cells inside [0, T] with invariant `m`, whose last cell satisfies `term`. -/
def chainTo (T : ℚ) (m : Bool) (term : Cell → Bool) : List Cell → Bool
  | [] => false
  | [c] => cellOK T m c && term c
  | c :: d :: l => cellOK T m c && linkOK c d && chainTo T m term (d :: l)

/-- Terminal condition: the last cell ends at `te` with its enclosure within `r` of (fE, fφ). -/
def endOK (te fE fφ r : ℚ) (c : Cell) : Bool :=
  decide (c.t0 + c.h = te ∧ |qeval c.pe c.h - fE| + c.B ≤ r ∧ |qeval c.pp c.h - fφ| + c.B ≤ r)

theorem abs_link {x v w B r : ℝ} (h1 : |x - v| ≤ B) (h2 : |v - w| + B ≤ r) : |x - w| ≤ r := by
  have := abs_sub_le x v w
  linarith

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

/-- A chain from its Boolean check: some last cell `e` meets `term`, the solution is enclosed
at its end, and the invariant holds from the first cell's start to there. -/
theorem chain_gen {T : ℚ} {m : Bool} {term : Cell → Bool} {E φ : ℝ → ℝ} :
    ∀ (l : List Cell) (c : Cell), chainTo T m term (c :: l) = true →
    (∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt E (E t * φ t) (Icc 0 (T : ℝ)) t) →
    (∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt φ (-(2 / t * φ t) - E t) (Icc 0 (T : ℝ)) t) →
    |E c.t0 - ((c.pe.headD 0 : ℚ) : ℝ)| ≤ c.δ →
    |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ →
    ∃ e : Cell, term e = true ∧ (c.t0 : ℝ) ≤ e.t0 + e.h ∧
    (∀ t ∈ Icc (c.t0 : ℝ) (e.t0 + e.h), Inv m E φ t) ∧
    |E (e.t0 + e.h) - ((qeval e.pe e.h : ℚ) : ℝ)| ≤ e.B ∧
    |φ (e.t0 + e.h) - ((qeval e.pp e.h : ℚ) : ℝ)| ≤ e.B := by
  intro l
  induction l with
  | nil =>
    intro c hok hE hφ h0 h0'
    simp only [chainTo, Bool.and_eq_true] at hok
    obtain ⟨k1, kt⟩ := hok
    obtain ⟨-, k2, k3⟩ := cell_basic c k1
    have k2' : ((c.t0 + c.h : ℚ) : ℝ) ≤ T := by exact_mod_cast k2
    have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
    push_cast at k2'
    have hf := cell_facts c k1 (E := E) (φ := φ)
      (fun t ht => hE t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht => hφ t ⟨ht.1, by linarith [ht.2]⟩) h0 h0'
    exact ⟨c, kt, by linarith, hf⟩
  | cons d l ih =>
    intro c hok hE hφ h0 h0'
    simp only [chainTo, Bool.and_eq_true] at hok
    obtain ⟨⟨k1, kl⟩, krest⟩ := hok
    obtain ⟨ke, kE, kφ⟩ := of_decide_eq_true kl
    have he : ((c.t0 + c.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
    push_cast at he
    obtain ⟨-, k2, k3⟩ := cell_basic c k1
    have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
    have k2' : ((c.t0 + c.h : ℚ) : ℝ) ≤ T := by exact_mod_cast k2
    push_cast at k2'
    have hf := cell_facts c k1 (E := E) (φ := φ)
      (fun t ht => hE t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht => hφ t ⟨ht.1, by linarith [ht.2]⟩) h0 h0'
    rw [he] at hf
    have kE' : |((qeval c.pe c.h : ℚ) : ℝ) - ((d.pe.headD 0 : ℚ) : ℝ)| + c.B ≤ d.δ := by
      exact_mod_cast kE
    have kφ' : |((qeval c.pp c.h : ℚ) : ℝ) - ((d.pp.headD 0 : ℚ) : ℝ)| + c.B ≤ d.δ := by
      exact_mod_cast kφ
    obtain ⟨e, het, hce, hinv, hb1, hb2⟩ := ih d krest
      (fun t ht => hE t ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht => hφ t ⟨by linarith [ht.1], ht.2⟩)
      (abs_link hf.2.1 kE') (abs_link hf.2.2 kφ')
    exact ⟨e, het, by linarith, icc_glue hf.1 hinv, hb1, hb2⟩

/-- A segment of a chain from its Boolean check: the solution enters the input box of `d`. -/
theorem seg_q {T : ℚ} {m : Bool} {E φ : ℝ → ℝ} (d : Cell) (l : List Cell) (c : Cell)
    (hok : chainTo T m (fun e => linkOK e d) (c :: l) = true)
    (hE : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt E (E t * φ t) (Icc 0 (T : ℝ)) t)
    (hφ : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt φ (-(2 / t * φ t) - E t) (Icc 0 (T : ℝ)) t)
    (h0 : |E c.t0 - ((c.pe.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (c.t0 : ℝ) ≤ d.t0 ∧ (∀ t ∈ Icc (c.t0 : ℝ) d.t0, Inv m E φ t) ∧
    |E d.t0 - ((d.pe.headD 0 : ℚ) : ℝ)| ≤ d.δ ∧ |φ d.t0 - ((d.pp.headD 0 : ℚ) : ℝ)| ≤ d.δ := by
  obtain ⟨e, het, hce, hinv, hb1, hb2⟩ := chain_gen l c hok hE hφ h0 h0'
  obtain ⟨ke, kE, kφ⟩ := of_decide_eq_true het
  have he : ((e.t0 + e.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
  push_cast at he
  rw [he] at hce hinv hb1 hb2
  have kE' : |((qeval e.pe e.h : ℚ) : ℝ) - ((d.pe.headD 0 : ℚ) : ℝ)| + e.B ≤ d.δ := by
    exact_mod_cast kE
  have kφ' : |((qeval e.pp e.h : ℚ) : ℝ) - ((d.pp.headD 0 : ℚ) : ℝ)| + e.B ≤ d.δ := by
    exact_mod_cast kφ
  exact ⟨hce, hinv, abs_link hb1 kE', abs_link hb2 kφ'⟩

/-- The last segment of a chain: the solution is within `r` of (fE, fφ) at `te`. -/
theorem end_q {T te fE fφ r : ℚ} {m : Bool} {E φ : ℝ → ℝ} (l : List Cell) (c : Cell)
    (hok : chainTo T m (endOK te fE fφ r) (c :: l) = true)
    (hE : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt E (E t * φ t) (Icc 0 (T : ℝ)) t)
    (hφ : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt φ (-(2 / t * φ t) - E t) (Icc 0 (T : ℝ)) t)
    (h0 : |E c.t0 - ((c.pe.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (∀ t ∈ Icc (c.t0 : ℝ) te, Inv m E φ t) ∧ |E te - fE| ≤ r ∧ |φ te - fφ| ≤ r := by
  obtain ⟨e, het, -, hinv, hb1, hb2⟩ := chain_gen l c hok hE hφ h0 h0'
  obtain ⟨ke, kE, kφ⟩ := of_decide_eq_true het
  have he : ((e.t0 + e.h : ℚ) : ℝ) = (te : ℝ) := by exact_mod_cast ke
  push_cast at he
  rw [he] at hinv hb1 hb2
  have kE' : |((qeval e.pe e.h : ℚ) : ℝ) - fE| + e.B ≤ r := by exact_mod_cast kE
  have kφ' : |((qeval e.pp e.h : ℚ) : ℝ) - fφ| + e.B ≤ r := by exact_mod_cast kφ
  exact ⟨hinv, abs_link hb1 kE', abs_link hb2 kφ'⟩

end Checked.Math.GCellQ
