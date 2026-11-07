import Mathlib
import Checked.Sim.QPoly
import Work.Blasius.BCell

/-!
# Blasius: validated cells checked by kernel evaluation (run 2026-11-07T1228Z)

The cells of `Work.Blasius.BCell.cell` with every numeric side condition and the three defect
bounds as one proposition over ℚ (`CellProp`): the defect polynomials pg′ − pp, pp′ − pq and
pq′ + pg·pq/2 are computed from the cell's Taylor polynomials (`Checked.Sim.QPoly`). A chain of
cells is one Boolean (`chainTo`), decided by the kernel; `chain_gen` turns it into an enclosure
of every solution at the chain's end.
-/

namespace Work.Blasius.BCellQ
open Set Checked.Sim Checked.Sim.QPoly Work.Blasius.BCell

/-- One cell: start `t0`, length `h`, input radius `δ` around the constant terms of `pg`, `pp`,
`pq`, defect bound `ε`, output radius `B`, slab half-widths `GH`, `QH`, Lipschitz constant `K`. -/
structure Cell where
  t0 : ℚ
  h : ℚ
  δ : ℚ
  ε : ℚ
  B : ℚ
  GH : ℚ
  QH : ℚ
  K : ℚ
  pg : List ℚ
  pp : List ℚ
  pq : List ℚ

/-- The third defect pq′ + pg·pq/2. -/
def defect3 (c : Cell) : List ℚ := qadd (qderiv c.pq) (qsmul (1 / 2) (qmul c.pg c.pq))

/-- All hypotheses of `BCell.cell` except the solution's own, as one proposition over ℚ. -/
def CellProp (T : ℚ) (c : Cell) : Prop :=
  0 ≤ c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h ∧ 1 ≤ c.K ∧
  (c.GH + c.QH) / 2 ≤ c.K ∧ c.K * c.h < 1 ∧
  0 ≤ c.δ ∧ 0 ≤ c.ε ∧
  -(c.GH - 1 / 100) ≤ c.pg.headD 0 - c.h * qabs c.pg.tail c.h ∧
  c.pg.headD 0 + c.h * qabs c.pg.tail c.h ≤ c.GH - 1 / 100 ∧
  -(c.QH - 1 / 100) ≤ c.pq.headD 0 - c.h * qabs c.pq.tail c.h ∧
  c.pq.headD 0 + c.h * qabs c.pq.tail c.h ≤ c.QH - 1 / 100 ∧
  qabs (qsub (qderiv c.pg) c.pp) c.h ≤ c.ε ∧
  qabs (qsub (qderiv c.pp) c.pq) c.h ≤ c.ε ∧
  qabs (defect3 c) c.h ≤ c.ε ∧
  c.δ * (1 / (1 - c.K * c.h)) + c.ε / c.K * (1 / (1 - c.K * c.h) - 1) ≤ c.B ∧
  c.B < 1 / 100

instance (T : ℚ) (c : Cell) : Decidable (CellProp T c) := by unfold CellProp; infer_instance

/-- `CellProp` as a Boolean, for evaluation by the kernel. -/
def cellOK (T : ℚ) (c : Cell) : Bool := decide (CellProp T c)

theorem cellOK_basic {T : ℚ} (c : Cell) (hok : cellOK T c = true) :
    0 ≤ c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h := by
  obtain ⟨k1, k2, k3, -⟩ : CellProp T c := of_decide_eq_true hok
  exact ⟨k1, k2, k3⟩

theorem defect3_eval (c : Cell) (σ : ℝ) :
    dEvalQ c.pq σ + evalQ c.pg σ * evalQ c.pq σ / 2 = evalQ (defect3 c) σ := by
  simp only [defect3, evalQ_qadd, evalQ_qsmul, evalQ_qmul, ← dEvalQ_eq]
  push_cast; ring

/-- The solution hypotheses on [a, T]. -/
def Sol (T a : ℝ) (g p q : ℝ → ℝ) : Prop :=
  (∀ t ∈ Icc a T, HasDerivWithinAt g (p t) (Icc 0 T) t) ∧
  (∀ t ∈ Icc a T, HasDerivWithinAt p (q t) (Icc 0 T) t) ∧
  (∀ t ∈ Icc a T, HasDerivWithinAt q (-(g t * q t / 2)) (Icc 0 T) t)

theorem Sol.mono {T a b : ℝ} {g p q : ℝ → ℝ} (h : Sol T a g p q) (hab : a ≤ b) :
    Sol T b g p q :=
  ⟨fun t ht => h.1 t ⟨hab.trans ht.1, ht.2⟩, fun t ht => h.2.1 t ⟨hab.trans ht.1, ht.2⟩,
    fun t ht => h.2.2 t ⟨hab.trans ht.1, ht.2⟩⟩

/-- The input box of a cell. -/
def InBox (c : Cell) (g p q : ℝ → ℝ) : Prop :=
  |g c.t0 - ((c.pg.headD 0 : ℚ) : ℝ)| ≤ c.δ ∧ |p c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ ∧
  |q c.t0 - ((c.pq.headD 0 : ℚ) : ℝ)| ≤ c.δ

/-- The end enclosure of a cell. -/
def AtEnd (c : Cell) (g p q : ℝ → ℝ) : Prop :=
  |g (c.t0 + c.h) - ((qeval c.pg c.h : ℚ) : ℝ)| ≤ c.B ∧
  |p (c.t0 + c.h) - ((qeval c.pp c.h : ℚ) : ℝ)| ≤ c.B ∧
  |q (c.t0 + c.h) - ((qeval c.pq c.h : ℚ) : ℝ)| ≤ c.B

/-- One validated cell from its Boolean check: the enclosure at the cell's end. -/
theorem cell_q {T : ℚ} (c : Cell) (hok : cellOK T c = true) {g p q : ℝ → ℝ}
    (hs : Sol T c.t0 g p q) (h0 : InBox c g p q) : AtEnd c g p q := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17⟩ :
    CellProp T c := of_decide_eq_true hok
  have r17 : ((c.B : ℚ) : ℝ) < ((1 / 100 : ℚ) : ℝ) := by exact_mod_cast k17
  have r5 : (((c.GH + c.QH) / 2 : ℚ) : ℝ) ≤ (c.K : ℝ) := by exact_mod_cast k5
  have r9 : ((-(c.GH - 1 / 100) : ℚ) : ℝ) ≤ ((c.pg.headD 0 - c.h * qabs c.pg.tail c.h : ℚ) : ℝ) := by
    exact_mod_cast k9
  have r10 : ((c.pg.headD 0 + c.h * qabs c.pg.tail c.h : ℚ) : ℝ) ≤ ((c.GH - 1 / 100 : ℚ) : ℝ) := by
    exact_mod_cast k10
  have r11 : ((-(c.QH - 1 / 100) : ℚ) : ℝ) ≤ ((c.pq.headD 0 - c.h * qabs c.pq.tail c.h : ℚ) : ℝ) := by
    exact_mod_cast k11
  have r12 : ((c.pq.headD 0 + c.h * qabs c.pq.tail c.h : ℚ) : ℝ) ≤ ((c.QH - 1 / 100 : ℚ) : ℝ) := by
    exact_mod_cast k12
  have r13 : ((qabs (qsub (qderiv c.pg) c.pp) c.h : ℚ) : ℝ) ≤ (c.ε : ℝ) := by exact_mod_cast k13
  have r14 : ((qabs (qsub (qderiv c.pp) c.pq) c.h : ℚ) : ℝ) ≤ (c.ε : ℝ) := by exact_mod_cast k14
  have r15 : ((qabs (defect3 c) c.h : ℚ) : ℝ) ≤ (c.ε : ℝ) := by exact_mod_cast k15
  have r16 : ((c.δ * (1 / (1 - c.K * c.h)) + c.ε / c.K * (1 / (1 - c.K * c.h) - 1) : ℚ) : ℝ) ≤
      (c.B : ℝ) := by exact_mod_cast k16
  push_cast at r5 r9 r10 r11 r12 r16 r17
  have hT2 : ((c.t0 + c.h : ℚ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast k2
  push_cast at hT2
  have hcT : Icc (c.t0 : ℝ) (c.t0 + c.h) ⊆ Icc (c.t0 : ℝ) T := Icc_subset_Icc le_rfl hT2
  have key := cell c.pg c.pp c.pq (T := (T : ℝ)) (t0 := (c.t0 : ℝ)) (h := (c.h : ℝ))
    (δ := (c.δ : ℝ)) (ε := (c.ε : ℝ)) (B := (c.B : ℝ)) (GH := (c.GH : ℝ)) (QH := (c.QH : ℝ))
    (K := (c.K : ℝ))
    (by exact_mod_cast k1) hT2 (by exact_mod_cast k3) (by exact_mod_cast k4)
    r5 (by exact_mod_cast k6) (by exact_mod_cast k7) (by exact_mod_cast k8)
    (fun t ht => hs.1 t (hcT ht)) (fun t ht => hs.2.1 t (hcT ht)) (fun t ht => hs.2.2 t (hcT ht))
    (fun σ hσ => by
      have := lower_q c.pg (h := c.h) hσ.1 hσ.2
      push_cast at this; linarith)
    (fun σ hσ => by
      have := upper_q c.pg (h := c.h) hσ.1 hσ.2
      push_cast at this; linarith)
    (fun σ hσ => by
      have := lower_q c.pq (h := c.h) hσ.1 hσ.2
      push_cast at this; linarith)
    (fun σ hσ => by
      have := upper_q c.pq (h := c.h) hσ.1 hσ.2
      push_cast at this; linarith)
    (fun σ hσ => by
      rw [dEvalQ_eq, ← evalQ_qsub]
      exact (abs_le_qabs _ hσ.1 hσ.2).trans r13)
    (fun σ hσ => by
      rw [dEvalQ_eq, ← evalQ_qsub]
      exact (abs_le_qabs _ hσ.1 hσ.2).trans r14)
    (fun σ hσ => by
      rw [defect3_eval]
      exact (abs_le_qabs _ hσ.1 hσ.2).trans r15)
    (by rw [evalQ_zero_head]; exact h0.1) (by rw [evalQ_zero_head]; exact h0.2.1)
    (by rw [evalQ_zero_head]; exact h0.2.2) r16 r17
  have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
  have e := key (c.t0 + c.h) ⟨by linarith, le_rfl⟩
  simp only [add_sub_cancel_left, ← qeval_cast] at e
  exact e

/-- Consecutive cells meet, and the end enclosure of `c` lies in the input box of `d`. -/
def linkOK (c d : Cell) : Bool :=
  decide (c.t0 + c.h = d.t0 ∧
    |qeval c.pg c.h - d.pg.headD 0| + c.B ≤ d.δ ∧
    |qeval c.pp c.h - d.pp.headD 0| + c.B ≤ d.δ ∧
    |qeval c.pq c.h - d.pq.headD 0| + c.B ≤ d.δ)

/-- A chain of cells inside [0, T] whose last cell satisfies `term`. -/
def chainTo (T : ℚ) (term : Cell → Bool) : List Cell → Bool
  | [] => false
  | [c] => cellOK T c && term c
  | c :: d :: l => cellOK T c && linkOK c d && chainTo T term (d :: l)

theorem abs_link {x v w B r : ℝ} (h1 : |x - v| ≤ B) (h2 : |v - w| + B ≤ r) : |x - w| ≤ r := by
  have := abs_sub_le x v w
  linarith

theorem link_box {c d : Cell} (hl : linkOK c d = true) {g p q : ℝ → ℝ} (he : AtEnd c g p q) :
    (d.t0 : ℝ) = c.t0 + c.h ∧ InBox d g p q := by
  obtain ⟨ke, k1, k2, k3⟩ := of_decide_eq_true hl
  have he' : ((c.t0 + c.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
  push_cast at he'
  have k1' : |((qeval c.pg c.h : ℚ) : ℝ) - ((d.pg.headD 0 : ℚ) : ℝ)| + c.B ≤ d.δ := by
    exact_mod_cast k1
  have k2' : |((qeval c.pp c.h : ℚ) : ℝ) - ((d.pp.headD 0 : ℚ) : ℝ)| + c.B ≤ d.δ := by
    exact_mod_cast k2
  have k3' : |((qeval c.pq c.h : ℚ) : ℝ) - ((d.pq.headD 0 : ℚ) : ℝ)| + c.B ≤ d.δ := by
    exact_mod_cast k3
  refine ⟨he'.symm, ?_⟩
  unfold InBox; rw [← he']
  exact ⟨abs_link he.1 k1', abs_link he.2.1 k2', abs_link he.2.2 k3'⟩

/-- A chain from its Boolean check: some last cell `e` satisfies `term`, and every solution
entering the first cell's box is enclosed at `e`'s end. -/
theorem chain_gen {T : ℚ} {term : Cell → Bool} :
    ∀ (l : List Cell) (c : Cell), chainTo T term (c :: l) = true →
    ∀ {g p q : ℝ → ℝ}, Sol T c.t0 g p q → InBox c g p q →
    ∃ e : Cell, term e = true ∧ AtEnd e g p q := by
  intro l
  induction l with
  | nil =>
    intro c hok g p q hs h0
    simp only [chainTo, Bool.and_eq_true] at hok
    exact ⟨c, hok.2, cell_q c hok.1 hs h0⟩
  | cons d l ih =>
    intro c hok g p q hs h0
    simp only [chainTo, Bool.and_eq_true] at hok
    obtain ⟨⟨k1, kl⟩, krest⟩ := hok
    have he := cell_q c k1 hs h0
    obtain ⟨hdt, hbox⟩ := link_box kl he
    have hh : (0 : ℝ) < c.h := by exact_mod_cast (cellOK_basic c k1).2.2
    exact ih d krest (hs.mono (by rw [hdt]; linarith)) hbox

/-- A segment ending in the input box of `d`. -/
theorem seg_q {T : ℚ} (d : Cell) (l : List Cell) (c : Cell)
    (hok : chainTo T (fun e => linkOK e d) (c :: l) = true) {g p q : ℝ → ℝ}
    (hs : Sol T c.t0 g p q) (h0 : InBox c g p q) : InBox d g p q := by
  obtain ⟨e, he, hend⟩ := chain_gen l c hok hs h0
  exact (link_box he hend).2

/-- Terminal condition: the last cell ends at `T` within `r` of (fg, fp, fq). -/
def endOK (T fg fp fq r : ℚ) (c : Cell) : Bool :=
  decide (c.t0 + c.h = T ∧ |qeval c.pg c.h - fg| + c.B ≤ r ∧ |qeval c.pp c.h - fp| + c.B ≤ r ∧
    |qeval c.pq c.h - fq| + c.B ≤ r)

/-- A final segment: every solution entering the first cell's box is within `r` of
(fg, fp, fq) at `T`. -/
theorem end_q {T fg fp fq r : ℚ} (l : List Cell) (c : Cell)
    (hok : chainTo T (endOK T fg fp fq r) (c :: l) = true) {g p q : ℝ → ℝ}
    (hs : Sol T c.t0 g p q) (h0 : InBox c g p q) :
    |g T - fg| ≤ r ∧ |p T - fp| ≤ r ∧ |q T - fq| ≤ r := by
  obtain ⟨e, het, hend⟩ := chain_gen l c hok hs h0
  obtain ⟨kT, k1, k2, k3⟩ := of_decide_eq_true het
  have hT : ((e.t0 + e.h : ℚ) : ℝ) = (T : ℝ) := by exact_mod_cast kT
  push_cast at hT
  have k1' : |((qeval e.pg e.h : ℚ) : ℝ) - fg| + e.B ≤ r := by exact_mod_cast k1
  have k2' : |((qeval e.pp e.h : ℚ) : ℝ) - fp| + e.B ≤ r := by exact_mod_cast k2
  have k3' : |((qeval e.pq e.h : ℚ) : ℝ) - fq| + e.B ≤ r := by exact_mod_cast k3
  unfold AtEnd at hend; rw [hT] at hend
  exact ⟨abs_link hend.1 k1', abs_link hend.2.1 k2', abs_link hend.2.2 k3'⟩

theorem chainTo_head {T : ℚ} {term : Cell → Bool} (c : Cell) (l : List Cell)
    (h : chainTo T term (c :: l) = true) : cellOK T c = true := by
  cases l with
  | nil => simp only [chainTo, Bool.and_eq_true] at h; exact h.1
  | cons _ _ => simp only [chainTo, Bool.and_eq_true] at h; exact h.1.1

/-- `seg_q` with the solution hypotheses on the whole of [0, T]. -/
theorem seg_q0 {T : ℚ} (d : Cell) (l : List Cell) (c : Cell)
    (hok : chainTo T (fun e => linkOK e d) (c :: l) = true) {g p q : ℝ → ℝ}
    (hs : Sol T 0 g p q) (h0 : InBox c g p q) : InBox d g p q := by
  have k := (cellOK_basic c (chainTo_head c l hok)).1
  exact seg_q d l c hok (hs.mono (by exact_mod_cast k)) h0

/-- `end_q` with the solution hypotheses on the whole of [0, T]. -/
theorem end_q0 {T fg fp fq r : ℚ} (l : List Cell) (c : Cell)
    (hok : chainTo T (endOK T fg fp fq r) (c :: l) = true) {g p q : ℝ → ℝ}
    (hs : Sol T 0 g p q) (h0 : InBox c g p q) :
    |g T - fg| ≤ r ∧ |p T - fp| ≤ r ∧ |q T - fq| ≤ r := by
  have k := (cellOK_basic c (chainTo_head c l hok)).1
  exact end_q l c hok (hs.mono (by exact_mod_cast k)) h0

end Work.Blasius.BCellQ
