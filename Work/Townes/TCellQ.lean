import Mathlib
import Work.Sim.QPoly
import Work.Townes.TCell
import Work.Townes.TStart

/-!
# Townes radial equation: validated cells checked by kernel evaluation (run 2026-11-07T0828Z)

The same validated Grönwall step as `Work.Townes.TCell.cell`, but every numeric side condition
and both defect bounds are one Boolean check over ℚ (`cellOK`): the defect polynomials are
*computed* from the cell's Taylor polynomials (`Work.Sim.QPoly`), not supplied by a generator
and proved by `ring`. A whole chain of cells is one Boolean (`chainOK`), and `chain_q` turns
`chainOK … = true` (decided by the kernel) into the enclosure of every solution at the end
time, plus positivity of θ (`pos`) or negativity of φ (`neg`) on the way when asked.
-/

namespace Work.Townes.TCellQ
open Set Work.Sim Work.Sim.QPoly Work.Townes.TCell

/-- One cell: start time `t0`, length `h`, input radius `δ` around the constant terms of the
Taylor polynomials `pt` (θ) and `pp` (φ) in σ = t − t0, defect bound `ε`, output radius `B`,
slab half-width `TH` and Lipschitz constant `K`. -/
structure Cell where
  t0 : ℚ
  h : ℚ
  δ : ℚ
  ε : ℚ
  B : ℚ
  TH : ℚ
  K : ℚ
  pt : List ℚ
  pp : List ℚ

/-- The multiplied-out defect of the second component, (t0+σ)pp' + pp − (t0+σ)(pt − pt³). -/
def defect2 (c : Cell) : List ℚ :=
  qsub (qadd (qmul [c.t0, 1] (qderiv c.pp)) c.pp)
    (qmul [c.t0, 1] (qsub c.pt (qmul c.pt (qmul c.pt c.pt))))

/-- All hypotheses of `TCell.cell` except the solution's own, as one proposition over ℚ. -/
def CellProp (T : ℚ) (c : Cell) : Prop :=
  0 < c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h ∧ 1 ≤ c.K ∧
  1 / c.t0 + 1 + 3 * (c.TH * c.TH) ≤ c.K ∧ c.K * c.h < 1 ∧
  0 ≤ c.δ ∧ 0 ≤ c.ε ∧
  -(c.TH - 1 / 100) ≤ c.pt.headD 0 - c.h * qabs c.pt.tail c.h ∧
  c.pt.headD 0 + c.h * qabs c.pt.tail c.h ≤ c.TH - 1 / 100 ∧
  qabs (qsub (qderiv c.pt) c.pp) c.h ≤ c.ε ∧
  qabs (defect2 c) c.h ≤ c.ε * c.t0 ∧
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
    ((c.t0 : ℝ) + σ) * dEvalQ c.pp σ + evalQ c.pp σ -
      ((c.t0 : ℝ) + σ) * (evalQ c.pt σ - evalQ c.pt σ ^ 3) = evalQ (defect2 c) σ := by
  simp only [defect2, evalQ_qsub, evalQ_qadd, evalQ_qmul, ← dEvalQ_eq, evalQ]
  push_cast; ring

/-- One validated cell from its Boolean check. -/
theorem cell_q {T : ℚ} (c : Cell) (hok : cellOK T c = true) {θ φ : ℝ → ℝ}
    (hθ : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), HasDerivWithinAt θ (φ t) (Icc 0 (T : ℝ)) t)
    (hφ : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt φ (-(1 / t * φ t) + θ t - θ t ^ 3) (Icc 0 (T : ℝ)) t)
    (h0 : |θ c.t0 - ((c.pt.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      |θ t - evalQ c.pt (t - c.t0)| ≤ c.B ∧ |φ t - evalQ c.pp (t - c.t0)| ≤ c.B := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14⟩ :
    CellProp T c := of_decide_eq_true hok
  have r14 : ((c.B : ℚ) : ℝ) < ((1 / 100 : ℚ) : ℝ) := by exact_mod_cast k14
  have r5 : ((1 / c.t0 + 1 + 3 * (c.TH * c.TH) : ℚ) : ℝ) ≤ (c.K : ℝ) := by exact_mod_cast k5
  have r9 : ((-(c.TH - 1 / 100) : ℚ) : ℝ) ≤ ((c.pt.headD 0 - c.h * qabs c.pt.tail c.h : ℚ) : ℝ) := by
    exact_mod_cast k9
  have r10 : ((c.pt.headD 0 + c.h * qabs c.pt.tail c.h : ℚ) : ℝ) ≤ ((c.TH - 1 / 100 : ℚ) : ℝ) := by
    exact_mod_cast k10
  have r11 : ((qabs (qsub (qderiv c.pt) c.pp) c.h : ℚ) : ℝ) ≤ (c.ε : ℝ) := by exact_mod_cast k11
  have r12 : ((qabs (defect2 c) c.h : ℚ) : ℝ) ≤ ((c.ε * c.t0 : ℚ) : ℝ) := by exact_mod_cast k12
  have r13 : ((c.δ * (1 / (1 - c.K * c.h)) + c.ε / c.K * (1 / (1 - c.K * c.h) - 1) : ℚ) : ℝ) ≤
      (c.B : ℝ) := by exact_mod_cast k13
  push_cast at r5 r9 r10 r12 r13 r14
  refine cell c.pt c.pp (T := (T : ℝ)) (t0 := (c.t0 : ℝ)) (h := (c.h : ℝ)) (δ := (c.δ : ℝ))
    (ε := (c.ε : ℝ)) (B := (c.B : ℝ)) (TH := (c.TH : ℝ)) (K := (c.K : ℝ))
    (by exact_mod_cast k1) (by exact_mod_cast k2) (by exact_mod_cast k3) (by exact_mod_cast k4)
    (by nlinarith [r5]) (by exact_mod_cast k6) (by exact_mod_cast k7) (by exact_mod_cast k8)
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
    rw [defect2_eval]
    exact (abs_le_qabs _ hσ.1 hσ.2).trans r12

/-- Consecutive cells meet, and the end enclosure of `c` lies in the input box of `d`. -/
def linkOK (c d : Cell) : Bool :=
  decide (c.t0 + c.h = d.t0 ∧
    |qeval c.pt c.h - d.pt.headD 0| + c.B ≤ d.δ ∧
    |qeval c.pp c.h - d.pp.headD 0| + c.B ≤ d.δ)

/-- θ stays positive on the cell. -/
def posOK (c : Cell) : Bool := decide (0 < c.pt.headD 0 - c.h * qabs c.pt.tail c.h - c.B)

/-- φ stays negative on the cell. -/
def negOK (c : Cell) : Bool := decide (c.pp.headD 0 + c.h * qabs c.pp.tail c.h + c.B < 0)

/-- A chain of cells inside [0, T] whose last cell satisfies `term`. -/
def chainTo (T : ℚ) (pos neg : Bool) (term : Cell → Bool) : List Cell → Bool
  | [] => false
  | [c] => cellOK T c && (!pos || posOK c) && (!neg || negOK c) && term c
  | c :: d :: l => cellOK T c && (!pos || posOK c) && (!neg || negOK c) && linkOK c d &&
      chainTo T pos neg term (d :: l)

/-- Terminal condition: the last cell ends at `T` with its enclosure within `r` of (fθ, fφ). -/
def endOK (T fθ fφ r : ℚ) (c : Cell) : Bool :=
  decide (c.t0 + c.h = T ∧ |qeval c.pt c.h - fθ| + c.B ≤ r ∧ |qeval c.pp c.h - fφ| + c.B ≤ r)

/-- A chain of cells ending at `T`, whose final enclosure lies within `r` of (fθ, fφ). -/
def chainOK (T : ℚ) (pos neg : Bool) (fθ fφ r : ℚ) (l : List Cell) : Bool :=
  chainTo T pos neg (endOK T fθ fφ r) l

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
      HasDerivWithinAt φ (-(1 / t * φ t) + θ t - θ t ^ 3) (Icc 0 (T : ℝ)) t)
    (h0 : |θ c.t0 - ((c.pt.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (pos = true → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), 0 < θ t) ∧
    (neg = true → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), φ t < 0) ∧
    |θ (c.t0 + c.h) - ((qeval c.pt c.h : ℚ) : ℝ)| ≤ c.B ∧
    |φ (c.t0 + c.h) - ((qeval c.pp c.h : ℚ) : ℝ)| ≤ c.B := by
  have hc := cell_q c hok hθ hφ h0 h0'
  have hh : (0 : ℝ) < c.h := by exact_mod_cast (cellOK_basic c hok).2.2
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
    have hn' : ((c.pp.headD 0 + c.h * qabs c.pp.tail c.h + c.B : ℚ) : ℝ) < ((0 : ℚ) : ℝ) := by
      exact_mod_cast hn
    have hu := upper_q c.pp (h := c.h) (σ := t - c.t0) (by linarith [ht.1]) (by linarith [ht.2])
    have e := abs_le.1 (hc t ht).2
    push_cast at hn' hu
    linarith [e.2]
  · have e := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).1
    rwa [add_sub_cancel_left, ← qeval_cast] at e
  · have e := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).2
    rwa [add_sub_cancel_left, ← qeval_cast] at e

theorem abs_link {x v w B r : ℝ} (h1 : |x - v| ≤ B) (h2 : |v - w| + B ≤ r) : |x - w| ≤ r := by
  have := abs_sub_le x v w
  linarith

/-- A chain from its Boolean check: some last cell `e` meets `term`, the solution is enclosed
at its end, and the sign invariants hold from the first cell's start to there. -/
theorem chain_gen {T : ℚ} {pos neg : Bool} {term : Cell → Bool} :
    ∀ (l : List Cell) (c : Cell), chainTo T pos neg term (c :: l) = true →
    ∀ {θ φ : ℝ → ℝ},
    (∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt θ (φ t) (Icc 0 (T : ℝ)) t) →
    (∀ t ∈ Icc (c.t0 : ℝ) T,
      HasDerivWithinAt φ (-(1 / t * φ t) + θ t - θ t ^ 3) (Icc 0 (T : ℝ)) t) →
    |θ c.t0 - ((c.pt.headD 0 : ℚ) : ℝ)| ≤ c.δ →
    |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ →
    ∃ e : Cell, term e = true ∧ cellOK T e = true ∧ (c.t0 : ℝ) ≤ e.t0 + e.h ∧
    (pos = true → ∀ t ∈ Icc (c.t0 : ℝ) (e.t0 + e.h), 0 < θ t) ∧
    (neg = true → ∀ t ∈ Icc (c.t0 : ℝ) (e.t0 + e.h), φ t < 0) ∧
    |θ (e.t0 + e.h) - ((qeval e.pt e.h : ℚ) : ℝ)| ≤ e.B ∧
    |φ (e.t0 + e.h) - ((qeval e.pp e.h : ℚ) : ℝ)| ≤ e.B := by
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
    obtain ⟨ke, kθ, kφ⟩ := of_decide_eq_true kl
    have he : ((c.t0 + c.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
    push_cast at he
    have hdT : (d.t0 : ℝ) ≤ T := by
      obtain ⟨_, h2, h3⟩ := cellOK_basic d (chainTo_head d l krest)
      exact_mod_cast (by linarith : d.t0 ≤ T)
    have hcd : (c.t0 : ℝ) ≤ d.t0 := by
      have : (0 : ℝ) < c.h := by exact_mod_cast (cellOK_basic c k1).2.2
      linarith
    have hf := cell_facts c k1 kp kn (θ := θ) (φ := φ)
      (fun t ht => hθ t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht => hφ t ⟨ht.1, by linarith [ht.2]⟩) h0 h0'
    rw [he] at hf
    have kθ' : |((qeval c.pt c.h : ℚ) : ℝ) - ((d.pt.headD 0 : ℚ) : ℝ)| + c.B ≤ d.δ := by
      exact_mod_cast kθ
    have kφ' : |((qeval c.pp c.h : ℚ) : ℝ) - ((d.pp.headD 0 : ℚ) : ℝ)| + c.B ≤ d.δ := by
      exact_mod_cast kφ
    obtain ⟨e, het, heok, hce, hpos, hneg, hb1, hb2⟩ := ih d krest (θ := θ) (φ := φ)
      (fun t ht => hθ t ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht => hφ t ⟨by linarith [ht.1], ht.2⟩)
      (abs_link hf.2.2.1 kθ') (abs_link hf.2.2.2 kφ')
    refine ⟨e, het, heok, by linarith, fun hp t ht => ?_, fun hn t ht => ?_, hb1, hb2⟩
    · rcases le_or_gt t d.t0 with h1 | h1
      · exact hf.1 hp t ⟨ht.1, h1⟩
      · exact hpos hp t ⟨h1.le, ht.2⟩
    · rcases le_or_gt t d.t0 with h1 | h1
      · exact hf.2.1 hn t ⟨ht.1, h1⟩
      · exact hneg hn t ⟨h1.le, ht.2⟩

/-- A whole chain of validated cells from its Boolean check: every solution entering the first
cell's box is enclosed at `T` within `r` of (fθ, fφ), with the requested sign invariants. -/
theorem chain_q {T : ℚ} {pos neg : Bool} {fθ fφ r : ℚ} (l : List Cell) (c : Cell)
    (hok : chainOK T pos neg fθ fφ r (c :: l) = true) {θ φ : ℝ → ℝ}
    (hθ : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt θ (φ t) (Icc 0 (T : ℝ)) t)
    (hφ : ∀ t ∈ Icc (c.t0 : ℝ) T,
      HasDerivWithinAt φ (-(1 / t * φ t) + θ t - θ t ^ 3) (Icc 0 (T : ℝ)) t)
    (h0 : |θ c.t0 - ((c.pt.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (pos = true → ∀ t ∈ Icc (c.t0 : ℝ) T, 0 < θ t) ∧
    (neg = true → ∀ t ∈ Icc (c.t0 : ℝ) T, φ t < 0) ∧
    |θ T - fθ| ≤ r ∧ |φ T - fφ| ≤ r := by
  obtain ⟨e, het, -, -, hpos, hneg, hb1, hb2⟩ := chain_gen l c hok hθ hφ h0 h0'
  obtain ⟨kT, kθ, kφ⟩ := of_decide_eq_true het
  have hT : ((e.t0 + e.h : ℚ) : ℝ) = (T : ℝ) := by exact_mod_cast kT
  push_cast at hT
  rw [hT] at hpos hneg hb1 hb2
  have kθ' : |((qeval e.pt e.h : ℚ) : ℝ) - fθ| + e.B ≤ r := by exact_mod_cast kθ
  have kφ' : |((qeval e.pp e.h : ℚ) : ℝ) - fφ| + e.B ≤ r := by exact_mod_cast kφ
  exact ⟨hpos, hneg, abs_link hb1 kθ', abs_link hb2 kφ'⟩

/-- A segment of a chain from its Boolean check: the solution enters the input box of `d` at
`d.t0`, with the sign invariants up to there. -/
theorem seg_q {T : ℚ} {pos neg : Bool} (d : Cell) (l : List Cell) (c : Cell)
    (hok : segOK T pos neg d (c :: l) = true) {θ φ : ℝ → ℝ}
    (hθ : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt θ (φ t) (Icc 0 (T : ℝ)) t)
    (hφ : ∀ t ∈ Icc (c.t0 : ℝ) T,
      HasDerivWithinAt φ (-(1 / t * φ t) + θ t - θ t ^ 3) (Icc 0 (T : ℝ)) t)
    (h0 : |θ c.t0 - ((c.pt.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (c.t0 : ℝ) ≤ d.t0 ∧
    (pos = true → ∀ t ∈ Icc (c.t0 : ℝ) d.t0, 0 < θ t) ∧
    (neg = true → ∀ t ∈ Icc (c.t0 : ℝ) d.t0, φ t < 0) ∧
    |θ d.t0 - ((d.pt.headD 0 : ℚ) : ℝ)| ≤ d.δ ∧ |φ d.t0 - ((d.pp.headD 0 : ℚ) : ℝ)| ≤ d.δ := by
  obtain ⟨e, het, -, hce, hpos, hneg, hb1, hb2⟩ := chain_gen l c hok hθ hφ h0 h0'
  obtain ⟨ke, kθ, kφ⟩ := of_decide_eq_true het
  have he : ((e.t0 + e.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
  push_cast at he
  rw [he] at hce hpos hneg hb1 hb2
  have kθ' : |((qeval e.pt e.h : ℚ) : ℝ) - ((d.pt.headD 0 : ℚ) : ℝ)| + e.B ≤ d.δ := by
    exact_mod_cast kθ
  have kφ' : |((qeval e.pp e.h : ℚ) : ℝ) - ((d.pp.headD 0 : ℚ) : ℝ)| + e.B ≤ d.δ := by
    exact_mod_cast kφ
  exact ⟨hce, hpos, hneg, abs_link hb1 kθ', abs_link hb2 kφ'⟩

end Work.Townes.TCellQ

/-! ## The singular start at the centre, checked by kernel evaluation -/

namespace Work.Townes.TCellQ
open Set Work.Sim Work.Sim.QPoly Work.Townes.TCell

/-- Data of the singular start: truncated series `P` of θ on [0, ξ0], tube radius `η`, residual
bound `R`, Lipschitz constant `L`, bound `Mp` of |P| (as in `Work.Townes.TStart.start`). -/
structure Start where
  ξ0 : ℚ
  η : ℚ
  R : ℚ
  L : ℚ
  Mp : ℚ
  P : List ℚ

/-- Residual (rP')' − r(P − P³) of the series, computed. -/
def startRes (s : Start) : List ℚ :=
  qsub (qderiv (0 :: qderiv s.P)) (qmul [0, 1] (qsub s.P (qmul s.P (qmul s.P s.P))))

/-- The radius constant C = Lη + R. -/
def startC (s : Start) : ℚ := s.L * s.η + s.R

/-- Hypotheses of `TStart.start`, the link to the first cell `c` and the sign invariant. -/
def StartProp (X c0 : ℚ) (pos neg : Bool) (s : Start) (c : Cell) : Prop :=
  0 < s.ξ0 ∧ s.ξ0 ≤ X ∧ s.P.headD 0 = c0 ∧
  (startRes s).headD 0 = 0 ∧ qabs (startRes s).tail s.ξ0 ≤ s.R ∧
  qabs s.P s.ξ0 ≤ s.Mp ∧ 1 + 3 * ((s.Mp + s.η) * (s.Mp + s.η)) ≤ s.L ∧ 0 < s.η ∧ 0 ≤ s.R ∧
  s.ξ0 * s.ξ0 / 4 * startC s < s.η ∧
  c.t0 = s.ξ0 ∧
  |qeval s.P s.ξ0 - c.pt.headD 0| + s.ξ0 * s.ξ0 / 4 * startC s ≤ c.δ ∧
  |qeval (qderiv s.P) s.ξ0 - c.pp.headD 0| + s.ξ0 / 2 * startC s ≤ c.δ ∧
  (pos = true → 0 < s.P.headD 0 - s.ξ0 * qabs s.P.tail s.ξ0 - s.ξ0 * s.ξ0 / 4 * startC s) ∧
  (neg = true → (qderiv s.P).headD 0 = 0 ∧
    (qderiv s.P).tail.headD 0 + s.ξ0 * qabs (qderiv s.P).tail.tail s.ξ0 + startC s / 2 < 0)

instance (X c0 : ℚ) (pos neg : Bool) (s : Start) (c : Cell) :
    Decidable (StartProp X c0 pos neg s c) := by unfold StartProp; infer_instance

/-- Start and chain together, as one Boolean. -/
def shootOK (X c0 : ℚ) (pos neg : Bool) (fθ fφ r : ℚ) (s : Start) (cs : List Cell) : Bool :=
  match cs with
  | [] => false
  | c :: _ => decide (StartProp X c0 pos neg s c) && chainOK X pos neg fθ fφ r cs

theorem evalQ_cons_zero_head (p : List ℚ) (hp : p.headD 0 = 0) (s : ℝ) :
    evalQ p s = s * evalQ p.tail s := by
  cases p with
  | nil => simp [evalQ]
  | cons a q => simp only [List.headD_cons] at hp; subst hp; simp [evalQ]

/-- The singular start from its Boolean check: every solution with θ(0) = c0 enters the input
box of the first cell `c` at c.t0 = ξ0, with the sign invariants on [0, ξ0]. -/
theorem start_q {X c0 : ℚ} {pos neg : Bool} (s : Start) (c : Cell)
    (hs : decide (StartProp X c0 pos neg s c) = true) {θ φ : ℝ → ℝ}
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) X, HasDerivWithinAt θ (φ ξ) (Icc 0 (X : ℝ)) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 (X : ℝ)) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) X,
      HasDerivWithinAt φ (-(1 / ξ * φ ξ) + θ ξ - θ ξ ^ 3) (Icc 0 (X : ℝ)) ξ)
    (h0 : θ 0 = c0) :
    (c.t0 : ℝ) = s.ξ0 ∧ (0 : ℝ) < c.t0 ∧
    (pos = true → ∀ t ∈ Icc (0 : ℝ) c.t0, 0 < θ t) ∧
    (neg = true → ∀ t ∈ Ioc (0 : ℝ) c.t0, φ t < 0) ∧
    |θ c.t0 - ((c.pt.headD 0 : ℚ) : ℝ)| ≤ c.δ ∧ |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, kpos, kneg⟩ :
    StartProp X c0 pos neg s c := of_decide_eq_true hs
  -- the series data as real functions
  have hp : ∀ t, HasDerivAt (evalQ s.P) (evalQ (qderiv s.P) t) t := fun t => by
    rw [← dEvalQ_eq]; exact hasDerivAt_evalQ s.P t
  have hq : ∀ t, HasDerivAt (fun t => t * evalQ (qderiv s.P) t)
      (evalQ (qderiv (0 :: qderiv s.P)) t) t := fun t => by
    have e : (fun t => t * evalQ (qderiv s.P) t) = evalQ (0 :: qderiv s.P) := by
      funext t; rw [evalQ_cons0]
    rw [e, ← dEvalQ_eq]; exact hasDerivAt_evalQ _ t
  have r5 : ((qabs (startRes s).tail s.ξ0 : ℚ) : ℝ) ≤ (s.R : ℝ) := by exact_mod_cast k5
  have hres : ∀ t ∈ Icc (0 : ℝ) s.ξ0, |evalQ (qderiv (0 :: qderiv s.P)) t -
      t * (evalQ s.P t - evalQ s.P t ^ 3)| ≤ t * s.R := by
    intro t ht
    have e : evalQ (qderiv (0 :: qderiv s.P)) t - t * (evalQ s.P t - evalQ s.P t ^ 3) =
        evalQ (startRes s) t := by
      simp only [startRes, evalQ_qsub, evalQ_qmul, evalQ]; push_cast; ring
    rw [e, evalQ_cons_zero_head _ k4, abs_mul, abs_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_left ((abs_le_qabs _ ht.1 ht.2).trans r5) ht.1
  have r6 : ((qabs s.P s.ξ0 : ℚ) : ℝ) ≤ (s.Mp : ℝ) := by exact_mod_cast k6
  have hpM : ∀ t ∈ Icc (0 : ℝ) s.ξ0, |evalQ s.P t| ≤ s.Mp := fun t ht =>
    (abs_le_qabs _ ht.1 ht.2).trans r6
  have r7 : ((1 + 3 * ((s.Mp + s.η) * (s.Mp + s.η)) : ℚ) : ℝ) ≤ (s.L : ℝ) := by exact_mod_cast k7
  have r10 : ((s.ξ0 * s.ξ0 / 4 * startC s : ℚ) : ℝ) < (s.η : ℝ) := by exact_mod_cast k10
  push_cast [startC] at r7 r10
  have hξX : (s.ξ0 : ℝ) ≤ X := by exact_mod_cast k2
  have hst := Work.Townes.TStart.start θ φ (evalQ s.P) (evalQ (qderiv s.P))
    (evalQ (qderiv (0 :: qderiv s.P))) (X := (X : ℝ)) (ξ0 := (s.ξ0 : ℝ)) (η := (s.η : ℝ))
    (R := (s.R : ℝ)) (L := (s.L : ℝ)) (Mp := (s.Mp : ℝ)) (c0 := (c0 : ℝ))
    (by exact_mod_cast k1) hξX hθ hφ0 hφ h0 hp
    (by rw [evalQ_zero_head, k3]) hq hres hpM (by nlinarith [r7]) (by exact_mod_cast k8)
    (by exact_mod_cast k9) (by linarith [r10])
  have hξ0 : (0 : ℝ) < s.ξ0 := by exact_mod_cast k1
  -- link to the first cell
  have hX0 := hst s.ξ0 ⟨hξ0.le, le_rfl⟩
  have r12 : |((qeval s.P s.ξ0 : ℚ) : ℝ) - ((c.pt.headD 0 : ℚ) : ℝ)| +
      ((s.ξ0 * s.ξ0 / 4 * startC s : ℚ) : ℝ) ≤ c.δ := by exact_mod_cast k12
  have r13 : |((qeval (qderiv s.P) s.ξ0 : ℚ) : ℝ) - ((c.pp.headD 0 : ℚ) : ℝ)| +
      ((s.ξ0 / 2 * startC s : ℚ) : ℝ) ≤ c.δ := by exact_mod_cast k13
  rw [qeval_cast] at r12 r13
  push_cast [startC] at r12 r13
  have hct : (c.t0 : ℝ) = s.ξ0 := by exact_mod_cast k11
  have hA : |θ s.ξ0 - evalQ s.P s.ξ0| ≤ s.ξ0 * s.ξ0 / 4 * (s.L * s.η + s.R) := by
    have := hX0.1; rw [sq] at this; exact this
  refine ⟨hct, hct ▸ hξ0, fun hpos t ht => ?_, fun hneg t ht => ?_,
    by rw [hct]; exact abs_link hA r12, by rw [hct]; exact abs_link hX0.2 r13⟩
  · rw [hct] at ht
    have h1 := ht.2
    · have kp := kpos hpos
      have rp : ((0 : ℚ) : ℝ) <
          ((s.P.headD 0 - s.ξ0 * qabs s.P.tail s.ξ0 - s.ξ0 * s.ξ0 / 4 * startC s : ℚ) : ℝ) := by
        exact_mod_cast kp
      have hl := lower_q s.P (h := s.ξ0) ht.1 h1
      have e := abs_le.1 (hst t ⟨ht.1, h1⟩).1
      push_cast [startC] at rp hl
      nlinarith [e.1]
  · rw [hct] at ht
    have h1 := ht.2
    · obtain ⟨kd, kn⟩ := kneg hneg
      have rn : (((qderiv s.P).tail.headD 0 + s.ξ0 * qabs (qderiv s.P).tail.tail s.ξ0 +
          startC s / 2 : ℚ) : ℝ) < ((0 : ℚ) : ℝ) := by exact_mod_cast kn
      have hu := upper_q (qderiv s.P).tail (h := s.ξ0) ht.1.le h1
      have e := abs_le.1 (hst t ⟨ht.1.le, h1⟩).2
      rw [evalQ_cons_zero_head _ kd] at e
      push_cast [startC] at rn hu
      have h3 : evalQ (qderiv s.P).tail t + (s.L * s.η + s.R) / 2 < 0 := by linarith
      have h4 : t * (evalQ (qderiv s.P).tail t + (s.L * s.η + s.R) / 2) < 0 :=
        mul_neg_of_pos_of_neg ht.1 h3
      nlinarith [e.2]

/-- Every solution of the radial Townes problem with θ(0) = c0 on [0, X], from one Boolean
check of a singular start and a chain of validated cells. -/
theorem shoot_q {X c0 : ℚ} {pos neg : Bool} {fθ fφ r : ℚ} (s : Start) (cs : List Cell)
    (hok : shootOK X c0 pos neg fθ fφ r s cs = true) {θ φ : ℝ → ℝ}
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) X, HasDerivWithinAt θ (φ ξ) (Icc 0 (X : ℝ)) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 (X : ℝ)) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) X,
      HasDerivWithinAt φ (-(1 / ξ * φ ξ) + θ ξ - θ ξ ^ 3) (Icc 0 (X : ℝ)) ξ)
    (h0 : θ 0 = c0) :
    (pos = true → ∀ t ∈ Icc (0 : ℝ) X, 0 < θ t) ∧
    (neg = true → ∀ t ∈ Ioc (0 : ℝ) X, φ t < 0) ∧
    |θ X - fθ| ≤ r ∧ |φ X - fφ| ≤ r := by
  cases cs with
  | nil => simp [shootOK] at hok
  | cons c l =>
  simp only [shootOK, Bool.and_eq_true] at hok
  obtain ⟨hs, hch⟩ := hok
  obtain ⟨-, hc0, sp, sn, b1, b2⟩ := start_q s c hs hθ hφ0 hφ h0
  have hc := chain_q l c hch (θ := θ) (φ := φ)
    (fun t ht => hθ t ⟨by linarith [ht.1], ht.2⟩)
    (fun t ht => hφ t ⟨by linarith [ht.1], ht.2⟩) b1 b2
  refine ⟨fun hpos t ht => ?_, fun hneg t ht => ?_, hc.2.2⟩
  · rcases le_or_gt t c.t0 with h1 | h1
    · exact sp hpos t ⟨ht.1, h1⟩
    · exact hc.1 hpos t ⟨h1.le, ht.2⟩
  · rcases le_or_gt t c.t0 with h1 | h1
    · exact sn hneg t ⟨ht.1, h1⟩
    · exact hc.2.1 hneg t ⟨h1.le, ht.2⟩

end Work.Townes.TCellQ

namespace Work.Townes.TCellQ
open Set

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

end Work.Townes.TCellQ
