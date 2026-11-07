import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Checked.Sim.ODETools
import Checked.Sim.QPoly
import Checked.Math.TFCell

/-! Thomas–Fermi, `TFCellQ`: the barrier cells of `Checked.Math.TFCell` checked by kernel evaluation. A cell is its start, its length and the two Taylor polynomials of the barrier; the two differential inequalities of `super_cell`/`sub_cell` are bounds of polynomials that are computed over the rationals from the barrier (`Checked.Sim.QPoly`), not supplied and proved by `ring`. A chain of cells is one Boolean, decided by the kernel. -/

namespace Checked.Math.TFCellQ
open Set Checked.Sim Checked.Sim.QPoly Checked.Math.TFCell

/-- One barrier cell: start `t0`, length `h`, Taylor polynomials `qw` (of w) and `qp` (of P) in
σ = t − t0. -/
structure BCell where
  t0 : ℚ
  h : ℚ
  qw : List ℚ
  qp : List ℚ

/-- qw·qw′ − (t0 + σ)·qp, computed. -/
def d1 (c : BCell) : List ℚ := qsub (qmul c.qw (qderiv c.qw)) (qmul [c.t0, 1] c.qp)

/-- qp′ − 2·qw³, computed. -/
def d2 (c : BCell) : List ℚ := qsub (qderiv c.qp) (qsmul 2 (qmul c.qw (qmul c.qw c.qw)))

/-- Lower bound c₀ − h·Σ|cₖ₊₁|hᵏ of a polynomial on [0, h]. -/
def lo (p : List ℚ) (h : ℚ) : ℚ := p.headD 0 - h * qabs p.tail h

/-- Upper bound c₀ + h·Σ|cₖ₊₁|hᵏ of a polynomial on [0, h]. -/
def hi (p : List ℚ) (h : ℚ) : ℚ := p.headD 0 + h * qabs p.tail h

/-- Side conditions of an upper barrier cell inside [0, T]. -/
def SupProp (T : ℚ) (c : BCell) : Prop :=
  0 ≤ c.t0 ∧ 0 < c.h ∧ c.t0 + c.h ≤ T ∧ 0 < lo (d1 c) c.h ∧ 0 < lo (d2 c) c.h

/-- Side conditions of a lower barrier cell inside [0, T]. -/
def SubProp (T : ℚ) (c : BCell) : Prop :=
  0 ≤ c.t0 ∧ 0 < c.h ∧ c.t0 + c.h ≤ T ∧ hi (d1 c) c.h < 0 ∧ hi (d2 c) c.h < 0

instance (T : ℚ) (c : BCell) : Decidable (SupProp T c) := by unfold SupProp; infer_instance
instance (T : ℚ) (c : BCell) : Decidable (SubProp T c) := by unfold SubProp; infer_instance

theorem d1_eval (c : BCell) (σ : ℝ) :
    evalQ c.qw σ * dEvalQ c.qw σ - ((c.t0 : ℝ) + σ) * evalQ c.qp σ = evalQ (d1 c) σ := by
  simp only [d1, evalQ_qsub, evalQ_qmul, ← dEvalQ_eq, evalQ]; push_cast; ring

theorem d2_eval (c : BCell) (σ : ℝ) :
    dEvalQ c.qp σ - 2 * evalQ c.qw σ ^ 3 = evalQ (d2 c) σ := by
  simp only [d2, evalQ_qsub, evalQ_qmul, evalQ_qsmul, ← dEvalQ_eq]; push_cast; ring

theorem lo_le (p : List ℚ) {h : ℚ} {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ h) :
    ((lo p h : ℚ) : ℝ) ≤ evalQ p σ := lower_q p h0 h1

theorem le_hi (p : List ℚ) {h : ℚ} {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ h) :
    evalQ p σ ≤ ((hi p h : ℚ) : ℝ) := upper_q p h0 h1

/-- The hypotheses on the pair (w, P) on [0, T] used by every cell. -/
structure TFSol (T : ℝ) (w P : ℝ → ℝ) : Prop where
  cw : ContinuousOn w (Icc 0 T)
  cP : ContinuousOn P (Icc 0 T)
  dw : ∀ t ∈ Ioc (0 : ℝ) T, HasDerivAt w (t * P t / w t) t
  dP : ∀ t ∈ Ioc (0 : ℝ) T, HasDerivAt P (2 * w t ^ 3) t
  pos : ∀ t ∈ Ioc (0 : ℝ) T, 0 < w t

/-- One upper barrier cell from its Boolean check. -/
theorem sup_q {T : ℚ} (c : BCell) (hok : decide (SupProp T c) = true) {w P : ℝ → ℝ}
    (hs : TFSol T w P) (s1 : w c.t0 < ((c.qw.headD 0 : ℚ) : ℝ))
    (s2 : P c.t0 < ((c.qp.headD 0 : ℚ) : ℝ)) :
    w (c.t0 + c.h) < ((qeval c.qw c.h : ℚ) : ℝ) ∧ P (c.t0 + c.h) < ((qeval c.qp c.h : ℚ) : ℝ) := by
  obtain ⟨k1, k2, k3, k4, k5⟩ : SupProp T c := of_decide_eq_true hok
  have r1 : (0 : ℝ) ≤ c.t0 := by exact_mod_cast k1
  have r2 : (0 : ℝ) < c.h := by exact_mod_cast k2
  have r3 : ((c.t0 + c.h : ℚ) : ℝ) ≤ T := by exact_mod_cast k3
  have r4 : ((0 : ℚ) : ℝ) < ((lo (d1 c) c.h : ℚ) : ℝ) := by exact_mod_cast k4
  have r5 : ((0 : ℚ) : ℝ) < ((lo (d2 c) c.h : ℚ) : ℝ) := by exact_mod_cast k5
  push_cast at r3 r4 r5
  have sub : Icc (c.t0 : ℝ) (c.t0 + c.h) ⊆ Icc 0 (T : ℝ) :=
    Icc_subset_Icc r1 r3
  have sub' : ∀ t ∈ Ioc (c.t0 : ℝ) (c.t0 + c.h), t ∈ Ioc (0 : ℝ) T := fun t ht =>
    ⟨lt_of_le_of_lt r1 ht.1, le_trans ht.2 r3⟩
  have hc := super_cell c.qw c.qp (w := w) (P := P) (t0 := (c.t0 : ℝ)) (h := (c.h : ℝ)) r1 r2
    (hs.cw.mono sub) (hs.cP.mono sub) (fun t ht => hs.dw t (sub' t ht))
    (fun t ht => hs.dP t (sub' t ht)) (fun t ht => hs.pos t (sub' t ht))
    (fun σ hσ => by rw [d1_eval]; exact lt_of_lt_of_le r4 (lo_le _ hσ.1 hσ.2))
    (fun σ hσ => by rw [d2_eval]; exact lt_of_lt_of_le r5 (lo_le _ hσ.1 hσ.2))
    (by rw [evalQ_zero_head]; exact s1) (by rw [evalQ_zero_head]; exact s2)
  have he := hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩
  rw [add_sub_cancel_left, ← qeval_cast, ← qeval_cast] at he
  exact he

/-- One lower barrier cell from its Boolean check. -/
theorem sub_q {T : ℚ} (c : BCell) (hok : decide (SubProp T c) = true) {w P : ℝ → ℝ}
    (hs : TFSol T w P) (s1 : ((c.qw.headD 0 : ℚ) : ℝ) < w c.t0)
    (s2 : ((c.qp.headD 0 : ℚ) : ℝ) < P c.t0) :
    ((qeval c.qw c.h : ℚ) : ℝ) < w (c.t0 + c.h) ∧ ((qeval c.qp c.h : ℚ) : ℝ) < P (c.t0 + c.h) := by
  obtain ⟨k1, k2, k3, k4, k5⟩ : SubProp T c := of_decide_eq_true hok
  have r1 : (0 : ℝ) ≤ c.t0 := by exact_mod_cast k1
  have r2 : (0 : ℝ) < c.h := by exact_mod_cast k2
  have r3 : ((c.t0 + c.h : ℚ) : ℝ) ≤ T := by exact_mod_cast k3
  have r4 : ((hi (d1 c) c.h : ℚ) : ℝ) < ((0 : ℚ) : ℝ) := by exact_mod_cast k4
  have r5 : ((hi (d2 c) c.h : ℚ) : ℝ) < ((0 : ℚ) : ℝ) := by exact_mod_cast k5
  push_cast at r3 r4 r5
  have sub : Icc (c.t0 : ℝ) (c.t0 + c.h) ⊆ Icc 0 (T : ℝ) :=
    Icc_subset_Icc r1 r3
  have sub' : ∀ t ∈ Ioc (c.t0 : ℝ) (c.t0 + c.h), t ∈ Ioc (0 : ℝ) T := fun t ht =>
    ⟨lt_of_le_of_lt r1 ht.1, le_trans ht.2 r3⟩
  have hc := sub_cell c.qw c.qp (w := w) (P := P) (t0 := (c.t0 : ℝ)) (h := (c.h : ℝ)) r1 r2
    (hs.cw.mono sub) (hs.cP.mono sub) (fun t ht => hs.dw t (sub' t ht))
    (fun t ht => hs.dP t (sub' t ht)) (fun t ht => hs.pos t (sub' t ht))
    (fun σ hσ => by rw [d1_eval]; exact lt_of_le_of_lt (le_hi _ hσ.1 hσ.2) r4)
    (fun σ hσ => by rw [d2_eval]; exact lt_of_le_of_lt (le_hi _ hσ.1 hσ.2) r5)
    (by rw [evalQ_zero_head]; exact s1) (by rw [evalQ_zero_head]; exact s2)
  have he := hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩
  rw [add_sub_cancel_left, ← qeval_cast, ← qeval_cast] at he
  exact he

/-- An upper cell's end values lie below the next cell's start values, at its start time. -/
def supLink (c d : BCell) : Bool :=
  decide (c.t0 + c.h = d.t0 ∧ qeval c.qw c.h ≤ d.qw.headD 0 ∧ qeval c.qp c.h ≤ d.qp.headD 0)

/-- A lower cell's end values lie above the next cell's start values, at its start time. -/
def subLink (c d : BCell) : Bool :=
  decide (c.t0 + c.h = d.t0 ∧ d.qw.headD 0 ≤ qeval c.qw c.h ∧ d.qp.headD 0 ≤ qeval c.qp c.h)

/-- A chain of upper cells whose last cell satisfies `term`. -/
def supChain (T : ℚ) (term : BCell → Bool) : List BCell → Bool
  | [] => false
  | [c] => decide (SupProp T c) && term c
  | c :: d :: l => decide (SupProp T c) && supLink c d && supChain T term (d :: l)

/-- A chain of lower cells whose last cell satisfies `term`. -/
def subChain (T : ℚ) (term : BCell → Bool) : List BCell → Bool
  | [] => false
  | [c] => decide (SubProp T c) && term c
  | c :: d :: l => decide (SubProp T c) && subLink c d && subChain T term (d :: l)

/-- Upper chain from its Boolean check: some last cell `e` meets `term`, and the solution lies
below its barrier at the end of `e`. -/
theorem sup_chain_q {T : ℚ} {term : BCell → Bool} {w P : ℝ → ℝ} (hs : TFSol T w P) :
    ∀ (l : List BCell) (c : BCell), supChain T term (c :: l) = true →
    w c.t0 < ((c.qw.headD 0 : ℚ) : ℝ) → P c.t0 < ((c.qp.headD 0 : ℚ) : ℝ) →
    ∃ e : BCell, term e = true ∧
      w (e.t0 + e.h) < ((qeval e.qw e.h : ℚ) : ℝ) ∧ P (e.t0 + e.h) < ((qeval e.qp e.h : ℚ) : ℝ) := by
  intro l
  induction l with
  | nil =>
    intro c hok s1 s2
    simp only [supChain, Bool.and_eq_true] at hok
    exact ⟨c, hok.2, sup_q c hok.1 hs s1 s2⟩
  | cons d l ih =>
    intro c hok s1 s2
    simp only [supChain, Bool.and_eq_true] at hok
    obtain ⟨⟨k1, kl⟩, krest⟩ := hok
    obtain ⟨ke, kw, kp⟩ := of_decide_eq_true kl
    have he : ((c.t0 + c.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
    push_cast at he
    have kw' : ((qeval c.qw c.h : ℚ) : ℝ) ≤ ((d.qw.headD 0 : ℚ) : ℝ) := by exact_mod_cast kw
    have kp' : ((qeval c.qp c.h : ℚ) : ℝ) ≤ ((d.qp.headD 0 : ℚ) : ℝ) := by exact_mod_cast kp
    have hc := sup_q c k1 hs s1 s2
    rw [he] at hc
    exact ih d krest (lt_of_lt_of_le hc.1 kw') (lt_of_lt_of_le hc.2 kp')

/-- Lower chain from its Boolean check. -/
theorem sub_chain_q {T : ℚ} {term : BCell → Bool} {w P : ℝ → ℝ} (hs : TFSol T w P) :
    ∀ (l : List BCell) (c : BCell), subChain T term (c :: l) = true →
    ((c.qw.headD 0 : ℚ) : ℝ) < w c.t0 → ((c.qp.headD 0 : ℚ) : ℝ) < P c.t0 →
    ∃ e : BCell, term e = true ∧
      ((qeval e.qw e.h : ℚ) : ℝ) < w (e.t0 + e.h) ∧ ((qeval e.qp e.h : ℚ) : ℝ) < P (e.t0 + e.h) := by
  intro l
  induction l with
  | nil =>
    intro c hok s1 s2
    simp only [subChain, Bool.and_eq_true] at hok
    exact ⟨c, hok.2, sub_q c hok.1 hs s1 s2⟩
  | cons d l ih =>
    intro c hok s1 s2
    simp only [subChain, Bool.and_eq_true] at hok
    obtain ⟨⟨k1, kl⟩, krest⟩ := hok
    obtain ⟨ke, kw, kp⟩ := of_decide_eq_true kl
    have he : ((c.t0 + c.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
    push_cast at he
    have kw' : ((d.qw.headD 0 : ℚ) : ℝ) ≤ ((qeval c.qw c.h : ℚ) : ℝ) := by exact_mod_cast kw
    have kp' : ((d.qp.headD 0 : ℚ) : ℝ) ≤ ((qeval c.qp c.h : ℚ) : ℝ) := by exact_mod_cast kp
    have hc := sub_q c k1 hs s1 s2
    rw [he] at hc
    exact ih d krest (lt_of_le_of_lt kw' hc.1) (lt_of_le_of_lt kp' hc.2)

/-- A segment of upper cells ending in the start box of the cell `d`. -/
theorem sup_seg_q {T : ℚ} {w P : ℝ → ℝ} (hs : TFSol T w P) (d : BCell) (l : List BCell)
    (c : BCell) (hok : supChain T (fun e => supLink e d) (c :: l) = true)
    (s1 : w c.t0 < ((c.qw.headD 0 : ℚ) : ℝ)) (s2 : P c.t0 < ((c.qp.headD 0 : ℚ) : ℝ)) :
    w d.t0 < ((d.qw.headD 0 : ℚ) : ℝ) ∧ P d.t0 < ((d.qp.headD 0 : ℚ) : ℝ) := by
  obtain ⟨e, he, h1, h2⟩ := sup_chain_q hs l c hok s1 s2
  obtain ⟨ke, kw, kp⟩ := of_decide_eq_true he
  have ht : ((e.t0 + e.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
  push_cast at ht
  have kw' : ((qeval e.qw e.h : ℚ) : ℝ) ≤ ((d.qw.headD 0 : ℚ) : ℝ) := by exact_mod_cast kw
  have kp' : ((qeval e.qp e.h : ℚ) : ℝ) ≤ ((d.qp.headD 0 : ℚ) : ℝ) := by exact_mod_cast kp
  rw [ht] at h1 h2
  exact ⟨lt_of_lt_of_le h1 kw', lt_of_lt_of_le h2 kp'⟩

/-- A segment of lower cells ending in the start box of the cell `d`. -/
theorem sub_seg_q {T : ℚ} {w P : ℝ → ℝ} (hs : TFSol T w P) (d : BCell) (l : List BCell)
    (c : BCell) (hok : subChain T (fun e => subLink e d) (c :: l) = true)
    (s1 : ((c.qw.headD 0 : ℚ) : ℝ) < w c.t0) (s2 : ((c.qp.headD 0 : ℚ) : ℝ) < P c.t0) :
    ((d.qw.headD 0 : ℚ) : ℝ) < w d.t0 ∧ ((d.qp.headD 0 : ℚ) : ℝ) < P d.t0 := by
  obtain ⟨e, he, h1, h2⟩ := sub_chain_q hs l c hok s1 s2
  obtain ⟨ke, kw, kp⟩ := of_decide_eq_true he
  have ht : ((e.t0 + e.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
  push_cast at ht
  have kw' : ((d.qw.headD 0 : ℚ) : ℝ) ≤ ((qeval e.qw e.h : ℚ) : ℝ) := by exact_mod_cast kw
  have kp' : ((d.qp.headD 0 : ℚ) : ℝ) ≤ ((qeval e.qp e.h : ℚ) : ℝ) := by exact_mod_cast kp
  rw [ht] at h1 h2
  exact ⟨lt_of_le_of_lt kw' h1, lt_of_le_of_lt kp' h2⟩

/-- Terminal condition of an upper chain: it ends at `T` below (a, b). -/
def supEnd (T a b : ℚ) (e : BCell) : Bool :=
  decide (e.t0 + e.h = T ∧ qeval e.qw e.h ≤ a ∧ qeval e.qp e.h ≤ b)

/-- Terminal condition of a lower chain: it ends at `T` above (a, b). -/
def subEnd (T a b : ℚ) (e : BCell) : Bool :=
  decide (e.t0 + e.h = T ∧ a ≤ qeval e.qw e.h ∧ b ≤ qeval e.qp e.h)

/-- The last segment of an upper chain: the solution is below (a, b) at `T`. -/
theorem sup_end_q {T a b : ℚ} {w P : ℝ → ℝ} (hs : TFSol T w P) (l : List BCell)
    (c : BCell) (hok : supChain T (supEnd T a b) (c :: l) = true)
    (s1 : w c.t0 < ((c.qw.headD 0 : ℚ) : ℝ)) (s2 : P c.t0 < ((c.qp.headD 0 : ℚ) : ℝ)) :
    w T < a ∧ P T < b := by
  obtain ⟨e, he, h1, h2⟩ := sup_chain_q hs l c hok s1 s2
  obtain ⟨ke, kw, kp⟩ := of_decide_eq_true he
  have ht : ((e.t0 + e.h : ℚ) : ℝ) = (T : ℝ) := by exact_mod_cast ke
  push_cast at ht
  have kw' : ((qeval e.qw e.h : ℚ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast kw
  have kp' : ((qeval e.qp e.h : ℚ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast kp
  rw [ht] at h1 h2
  exact ⟨lt_of_lt_of_le h1 kw', lt_of_lt_of_le h2 kp'⟩

/-- The last segment of a lower chain: the solution is above (a, b) at `T`. -/
theorem sub_end_q {T a b : ℚ} {w P : ℝ → ℝ} (hs : TFSol T w P) (l : List BCell)
    (c : BCell) (hok : subChain T (subEnd T a b) (c :: l) = true)
    (s1 : ((c.qw.headD 0 : ℚ) : ℝ) < w c.t0) (s2 : ((c.qp.headD 0 : ℚ) : ℝ) < P c.t0) :
    (a : ℝ) < w T ∧ (b : ℝ) < P T := by
  obtain ⟨e, he, h1, h2⟩ := sub_chain_q hs l c hok s1 s2
  obtain ⟨ke, kw, kp⟩ := of_decide_eq_true he
  have ht : ((e.t0 + e.h : ℚ) : ℝ) = (T : ℝ) := by exact_mod_cast ke
  push_cast at ht
  have kw' : (a : ℝ) ≤ ((qeval e.qw e.h : ℚ) : ℝ) := by exact_mod_cast kw
  have kp' : (b : ℝ) ≤ ((qeval e.qp e.h : ℚ) : ℝ) := by exact_mod_cast kp
  rw [ht] at h1 h2
  exact ⟨lt_of_le_of_lt kw' h1, lt_of_le_of_lt kp' h2⟩

end Checked.Math.TFCellQ
