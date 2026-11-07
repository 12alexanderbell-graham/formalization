import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Sim.QPoly
import Checked.Sim.OneSided3
import Checked.Hiemenz.HExBase
/-! Hiemenz stagnation-point flow, `HCellWC`: the validated cells of `HCellW` for the clamped Hiemenz field, with the ball of every cell inside the clamps, so that the same certificates apply to the flow of the clamped field. Promoted from `Work/Hiemenz/HCellWC.lean`. -/

namespace Checked.Hiemenz.HCellWC
open Set Checked.Sim Checked.Sim.QPoly Checked.Sim.OneSided3 Checked.Hiemenz.HExBase

/-- One cell: start `t0`, length `h`, input radius `δ`, defect bound `ε`, output radius `B` in the
weighted norm with weights `w1`, `w2`, one-sided bound `μ`, bounds `r1`, `r2` of the first two
error components on the ball, and the Taylor polynomials `pg`, `pp`, `pq`. -/
structure Cell where
  t0 : ℚ
  h : ℚ
  δ : ℚ
  ε : ℚ
  B : ℚ
  μ : ℚ
  w1 : ℚ
  w2 : ℚ
  r1 : ℚ
  r2 : ℚ
  pg : List ℚ
  pp : List ℚ
  pq : List ℚ

/-- The third defect pq′ + pg·pq + 1 − pp². -/
def defect3 (c : Cell) : List ℚ := qsub (qadd (qadd (qderiv c.pq) (qmul c.pg c.pq)) [1]) (qmul c.pp c.pp)

/-- The determinant of the symmetric 3×3 matrix with entries m11 … m33. -/
def det3 (m11 m12 m13 m22 m23 m33 : ℚ) : ℚ :=
  m11 * (m22 * m33 - m23 ^ 2) - m12 * (m12 * m33 - m23 * m13) + m13 * (m12 * m23 - m22 * m13)

/-- Sylvester's criterion for the one-sided bound at one value `P3` of the q-component, one value
`s` of y2 + P2 and a lower bound `m` of the g-component. -/
def psdOK (μ w1 w2 m P3 s : ℚ) : Prop :=
  0 < μ * w1 ∧ 0 < μ * w1 * (μ * w2) - (-(w1 / 2)) ^ 2 ∧
  0 ≤ det3 (μ * w1) (-(w1 / 2)) (P3 / 2) (μ * w2) (-((w2 + s) / 2)) (μ + m)

/-- Lower bound of the g-component on the ball. -/
def mlo (c : Cell) : ℚ := c.pg.headD 0 - c.h * qabs c.pg.tail c.h - c.r1

/-- Lower end of the q-component of the approximation on the cell. -/
def qlo (c : Cell) : ℚ := c.pq.headD 0 - c.h * qabs c.pq.tail c.h

/-- Upper end of the q-component of the approximation on the cell. -/
def qhi (c : Cell) : ℚ := c.pq.headD 0 + c.h * qabs c.pq.tail c.h

/-- Lower end of the p-component of the approximation on the cell. -/
def plo (c : Cell) : ℚ := c.pp.headD 0 - c.h * qabs c.pp.tail c.h

/-- Upper end of the p-component of the approximation on the cell. -/
def phi (c : Cell) : ℚ := c.pp.headD 0 + c.h * qabs c.pp.tail c.h

/-- Lower end of the g-component of the approximation on the cell. -/
def glo (c : Cell) : ℚ := c.pg.headD 0 - c.h * qabs c.pg.tail c.h

/-- Upper end of the g-component of the approximation on the cell. -/
def ghi (c : Cell) : ℚ := c.pg.headD 0 + c.h * qabs c.pg.tail c.h

/-- All hypotheses of the weighted cell step except the solution's own, over ℚ. -/
def CellProp (T : ℚ) (c : Cell) : Prop :=
  0 ≤ c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h ∧ 0 < c.w1 ∧ 0 < c.w2 ∧ 0 ≤ c.μ ∧ c.μ * c.h < 1 ∧
  0 < c.δ ∧ 0 < c.ε ∧
  c.w1 * qabs (qsub (qderiv c.pg) c.pp) c.h ^ 2 + c.w2 * qabs (qsub (qderiv c.pp) c.pq) c.h ^ 2
    + qabs (defect3 c) c.h ^ 2 < c.ε ^ 2 ∧
  0 ≤ c.r1 ∧ c.B ^ 2 ≤ c.w1 * c.r1 ^ 2 ∧ 0 ≤ c.r2 ∧ c.B ^ 2 ≤ c.w2 * c.r2 ^ 2 ∧
  psdOK c.μ c.w1 c.w2 (mlo c) (qlo c) (2 * plo c - c.r2) ∧
  psdOK c.μ c.w1 c.w2 (mlo c) (qlo c) (2 * phi c + c.r2) ∧
  psdOK c.μ c.w1 c.w2 (mlo c) (qhi c) (2 * plo c - c.r2) ∧
  psdOK c.μ c.w1 c.w2 (mlo c) (qhi c) (2 * phi c + c.r2) ∧
  (c.δ + c.ε * c.h) / (1 - c.μ * c.h) ≤ c.B ∧
  -(c.t0 + 2) < glo c - c.r1 ∧ ghi c + c.r1 < c.t0 + 2 ∧ -2 < plo c - c.r2 ∧ phi c + c.r2 < 2 ∧
  -2 < qlo c - c.B ∧ qhi c + c.B < 2

instance (T : ℚ) (c : Cell) : Decidable (CellProp T c) := by
  unfold CellProp psdOK; infer_instance

/-- `CellProp` as a Boolean, for evaluation by the kernel. -/
def cellOK (T : ℚ) (c : Cell) : Bool := decide (CellProp T c)

theorem cellOK_basic {T : ℚ} (c : Cell) (hok : cellOK T c = true) :
    0 ≤ c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h := by
  obtain ⟨k1, k2, k3, -⟩ : CellProp T c := of_decide_eq_true hok
  exact ⟨k1, k2, k3⟩

theorem cell_pos {T : ℚ} (c : Cell) (hok : cellOK T c = true) :
    (0 : ℝ) < c.w1 ∧ (0 : ℝ) < c.w2 ∧ (0 : ℝ) < c.B ∧ (0 : ℝ) ≤ c.r2 ∧
      (c.B : ℝ) ^ 2 ≤ c.w2 * (c.r2 : ℝ) ^ 2 := by
  obtain ⟨-, -, k3, kw1, kw2, -, kμh, kδ, kε, -, -, -, kr2, kBr2, -, -, -, -, kB, -⟩ :
    CellProp T c := of_decide_eq_true hok
  have h1 : (0 : ℚ) < 1 - c.μ * c.h := by linarith
  have h2 : (0 : ℚ) < (c.δ + c.ε * c.h) / (1 - c.μ * c.h) :=
    div_pos (by nlinarith) h1
  refine ⟨by exact_mod_cast kw1, by exact_mod_cast kw2, by exact_mod_cast h2.trans_le kB,
    by exact_mod_cast kr2, by exact_mod_cast kBr2⟩

theorem defect3_eval (c : Cell) (σ : ℝ) :
    dEvalQ c.pq σ + evalQ c.pg σ * evalQ c.pq σ + 1 - evalQ c.pp σ ^ 2 = evalQ (defect3 c) σ := by
  simp only [defect3, evalQ_qsub, evalQ_qadd, evalQ_qmul, ← dEvalQ_eq]
  simp only [evalQ]
  push_cast; ring

/-- The solution hypotheses on [a, T]. -/
def SolC (T a : ℝ) (g p q : ℝ → ℝ) : Prop :=
  (∀ t ∈ Icc a T, HasDerivWithinAt g (cl 2 (p t)) (Icc 0 T) t) ∧
  (∀ t ∈ Icc a T, HasDerivWithinAt p (cl 2 (q t)) (Icc 0 T) t) ∧
  (∀ t ∈ Icc a T, HasDerivWithinAt q (-(cl (max t 0 + 2) (g t) * cl 2 (q t)) - 1 + cl 2 (p t) ^ 2)
    (Icc 0 T) t)

theorem SolC.mono {T a b : ℝ} {g p q : ℝ → ℝ} (h : SolC T a g p q) (hab : a ≤ b) :
    SolC T b g p q :=
  ⟨fun t ht => h.1 t ⟨hab.trans ht.1, ht.2⟩, fun t ht => h.2.1 t ⟨hab.trans ht.1, ht.2⟩,
    fun t ht => h.2.2 t ⟨hab.trans ht.1, ht.2⟩⟩

/-- The weighted norm (squared) of an error vector. -/
def V (w1 w2 e1 e2 e3 : ℝ) : ℝ := w1 * e1 ^ 2 + w2 * e2 ^ 2 + e3 ^ 2

/-- The input ball of a cell. -/
def InBox (c : Cell) (g p q : ℝ → ℝ) : Prop :=
  V c.w1 c.w2 (g c.t0 - ((c.pg.headD 0 : ℚ) : ℝ)) (p c.t0 - ((c.pp.headD 0 : ℚ) : ℝ))
    (q c.t0 - ((c.pq.headD 0 : ℚ) : ℝ)) ≤ (c.δ : ℝ) ^ 2

/-- The end enclosure of a cell. -/
def AtEnd (c : Cell) (g p q : ℝ → ℝ) : Prop :=
  V c.w1 c.w2 (g (c.t0 + c.h) - ((qeval c.pg c.h : ℚ) : ℝ)) (p (c.t0 + c.h) - ((qeval c.pp c.h : ℚ) : ℝ))
    (q (c.t0 + c.h) - ((qeval c.pq c.h : ℚ) : ℝ)) ≤ (c.B : ℝ) ^ 2

/-- e^x ≤ 1/(1 − x) for x < 1. -/
theorem exp_le_inv' {x : ℝ} (hx : x < 1) : Real.exp x ≤ 1 / (1 - x) := by
  have h1 : 0 < 1 - x := by linarith
  rw [le_div_iff₀ h1]
  have := Real.add_one_le_exp (-x)
  have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

/-- From a weighted-norm bound to a component bound. -/
theorem comp_le {w e B r : ℝ} (hw : 0 < w) (hr : 0 ≤ r) (he : w * e ^ 2 ≤ B ^ 2)
    (hB : B ^ 2 ≤ w * r ^ 2) : |e| ≤ r := by
  have h1 : e ^ 2 ≤ r ^ 2 := le_of_mul_le_mul_left (he.trans hB) hw
  by_contra hc
  rw [not_le] at hc
  have : r ^ 2 < |e| ^ 2 := by nlinarith [abs_nonneg e]
  rw [sq_abs] at this
  linarith

/-- The quadratic form eᵀ M e of the one-sided bound, at (P3, s). -/
noncomputable def qf (μ w1 w2 m P s x y z : ℝ) : ℝ :=
  μ * w1 * x ^ 2 + μ * w2 * y ^ 2 + (μ + m) * z ^ 2
    + 2 * (-(w1 / 2)) * x * y + 2 * (P / 2) * x * z + 2 * (-((w2 + s) / 2)) * y * z

/-- The one-sided bound of the Hiemenz field on the ball, from the four corner checks. -/
theorem os_hiemenz {μ w1 w2 m ql qh sl sh P1 P2 P3 y1 y2 y3 : ℝ}
    (H1 : ∀ x y z : ℝ, 0 ≤ qf μ w1 w2 m ql sl x y z)
    (H2 : ∀ x y z : ℝ, 0 ≤ qf μ w1 w2 m ql sh x y z)
    (H3 : ∀ x y z : ℝ, 0 ≤ qf μ w1 w2 m qh sl x y z)
    (H4 : ∀ x y z : ℝ, 0 ≤ qf μ w1 w2 m qh sh x y z)
    (hm : m ≤ y1) (hq1 : ql ≤ P3) (hq2 : P3 ≤ qh) (hs1 : sl ≤ y2 + P2) (hs2 : y2 + P2 ≤ sh) :
    w1 * (y2 - P2) * (y1 - P1) + w2 * (y3 - P3) * (y2 - P2)
      + ((-(y1 * y3) - 1 + y2 ^ 2) - (-(P1 * P3) - 1 + P2 ^ 2)) * (y3 - P3)
      ≤ μ * (w1 * (y1 - P1) ^ 2 + w2 * (y2 - P2) ^ 2 + (y3 - P3) ^ 2) := by
  set e1 := y1 - P1 with he1
  set e2 := y2 - P2 with he2
  set e3 := y3 - P3 with he3
  set s := y2 + P2 with hs
  have key : μ * (w1 * e1 ^ 2 + w2 * e2 ^ 2 + e3 ^ 2)
      - (w1 * e2 * e1 + w2 * e3 * e2 + ((-(y1 * y3) - 1 + y2 ^ 2) - (-(P1 * P3) - 1 + P2 ^ 2)) * e3)
      = qf μ w1 w2 m P3 s e1 e2 e3 + (y1 - m) * e3 ^ 2 := by
    simp only [qf, he1, he2, he3, hs]; ring
  have hy : 0 ≤ (y1 - m) * e3 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  -- affine in P: reduce to a corner in P
  have dP : ∀ P P' t, qf μ w1 w2 m P t e1 e2 e3 - qf μ w1 w2 m P' t e1 e2 e3 = (P - P') * (e1 * e3) := by
    intro P P' t; simp only [qf]; ring
  have dS : ∀ P t t', qf μ w1 w2 m P t e1 e2 e3 - qf μ w1 w2 m P t' e1 e2 e3 = -((t - t') * (e2 * e3)) := by
    intro P t t'; simp only [qf]; ring
  -- in s first, at each P-corner
  have hS : ∀ P, (∀ x y z : ℝ, 0 ≤ qf μ w1 w2 m P sl x y z) → (∀ x y z : ℝ, 0 ≤ qf μ w1 w2 m P sh x y z) →
      0 ≤ qf μ w1 w2 m P s e1 e2 e3 := by
    intro P A B
    rcases le_total (e2 * e3) 0 with h | h
    · have := dS P s sl
      have : 0 ≤ (s - sl) * (-(e2 * e3)) := mul_nonneg (by linarith) (by linarith)
      linarith [A e1 e2 e3]
    · have := dS P s sh
      have : 0 ≤ (sh - s) * (e2 * e3) := mul_nonneg (by linarith) h
      linarith [B e1 e2 e3]
  have hQ : 0 ≤ qf μ w1 w2 m P3 s e1 e2 e3 := by
    rcases le_total 0 (e1 * e3) with h | h
    · have := dP P3 ql s
      have : 0 ≤ (P3 - ql) * (e1 * e3) := mul_nonneg (by linarith) h
      linarith [hS ql H1 H2]
    · have := dP P3 qh s
      have : 0 ≤ (qh - P3) * (-(e1 * e3)) := mul_nonneg (by linarith) (by linarith)
      linarith [hS qh H3 H4]
  have : w1 * e2 * e1 = w1 * (y2 - P2) * (y1 - P1) := by rw [he1, he2]
  linarith

theorem quad_of_psd {μ w1 w2 m P3 s : ℚ} (h : psdOK μ w1 w2 m P3 s) (x y z : ℝ) :
    0 ≤ qf (μ : ℝ) w1 w2 m P3 s x y z := by
  obtain ⟨h1, h2, h3⟩ := h
  have r1 : (0 : ℝ) < ((μ * w1 : ℚ) : ℝ) := by exact_mod_cast h1
  have r2 : (0 : ℝ) < ((μ * w1 * (μ * w2) - (-(w1 / 2)) ^ 2 : ℚ) : ℝ) := by exact_mod_cast h2
  have r3 : (0 : ℝ) ≤ ((det3 (μ * w1) (-(w1 / 2)) (P3 / 2) (μ * w2) (-((w2 + s) / 2)) (μ + m) : ℚ) : ℝ) := by
    exact_mod_cast h3
  unfold det3 at r3
  push_cast at r1 r2 r3
  have := quad3_nonneg r1 r2 r3 x y z
  unfold qf; linarith

/-- R(t) = (δ + ε(t − t₀))·e^{μ(t − t₀)} stays below B on the cell. -/
theorem R_le {t0 h δ ε μ B t : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hμ : 0 ≤ μ) (hμh : μ * h < 1)
    (hB : (δ + ε * h) / (1 - μ * h) ≤ B) (ht : t ∈ Icc t0 (t0 + h)) :
    (δ + ε * (t - t0)) * Real.exp (μ * (t - t0)) ≤ B := by
  have h1 : (0 : ℝ) < 1 - μ * h := by linarith
  have hx : μ * (t - t0) ≤ μ * h := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hμ
  have he1 : Real.exp (μ * (t - t0)) ≤ Real.exp (μ * h) := Real.exp_le_exp.2 hx
  have he2 := exp_le_inv' hμh
  have hpos : (0 : ℝ) ≤ δ + ε * (t - t0) := by nlinarith [ht.1]
  calc (δ + ε * (t - t0)) * Real.exp (μ * (t - t0))
      ≤ (δ + ε * h) * Real.exp (μ * h) :=
        mul_le_mul (by nlinarith [ht.2]) he1 (Real.exp_pos _).le (by nlinarith [ht.1, ht.2])
    _ ≤ (δ + ε * h) * (1 / (1 - μ * h)) :=
        mul_le_mul_of_nonneg_left he2 (by nlinarith [ht.1, ht.2])
    _ = (δ + ε * h) / (1 - μ * h) := by ring
    _ ≤ B := hB

/-- Time-dependent copy of `Checked.Sim.OneSided3.onesided3_cell` (the field may depend on t); generic 3-D cell step in the weighted norm `w1·e₁² + w2·e₂² + e₃²` with a one-sided bound `μ`
on the ball of radius `B` around the approximation. -/
theorem onesided3_cell_t {F1 F2 F3 : ℝ → ℝ → ℝ → ℝ → ℝ} {f1 f2 f3 g1 g2 g3 G1 G2 G3 : ℝ → ℝ}
    {a b w1 w2 μ ε δ B : ℝ}
    (hab : a ≤ b) (hw1 : 0 < w1) (hw2 : 0 < w2) (hμ : 0 ≤ μ) (hε : 0 < ε) (hδ : 0 < δ)
    (hf1 : ContinuousOn f1 (Set.Icc a b)) (hf2 : ContinuousOn f2 (Set.Icc a b)) (hf3 : ContinuousOn f3 (Set.Icc a b))
    (hg1 : ContinuousOn g1 (Set.Icc a b)) (hg2 : ContinuousOn g2 (Set.Icc a b)) (hg3 : ContinuousOn g3 (Set.Icc a b))
    (hf1' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt f1 (F1 t (f1 t) (f2 t) (f3 t)) (Set.Ici t) t)
    (hf2' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt f2 (F2 t (f1 t) (f2 t) (f3 t)) (Set.Ici t) t)
    (hf3' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt f3 (F3 t (f1 t) (f2 t) (f3 t)) (Set.Ici t) t)
    (hg1' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt g1 (G1 t) (Set.Ici t) t)
    (hg2' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt g2 (G2 t) (Set.Ici t) t)
    (hg3' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt g3 (G3 t) (Set.Ici t) t)
    (hdef : ∀ t ∈ Set.Ico a b,
      w1 * (G1 t - F1 t (g1 t) (g2 t) (g3 t)) ^ 2 + w2 * (G2 t - F2 t (g1 t) (g2 t) (g3 t)) ^ 2
        + (G3 t - F3 t (g1 t) (g2 t) (g3 t)) ^ 2 < ε ^ 2)
    (hos : ∀ t ∈ Set.Ico a b, ∀ y1 y2 y3 : ℝ,
      w1 * (y1 - g1 t) ^ 2 + w2 * (y2 - g2 t) ^ 2 + (y3 - g3 t) ^ 2 ≤ B ^ 2 →
      w1 * (F1 t y1 y2 y3 - F1 t (g1 t) (g2 t) (g3 t)) * (y1 - g1 t)
        + w2 * (F2 t y1 y2 y3 - F2 t (g1 t) (g2 t) (g3 t)) * (y2 - g2 t)
        + (F3 t y1 y2 y3 - F3 t (g1 t) (g2 t) (g3 t)) * (y3 - g3 t)
        ≤ μ * (w1 * (y1 - g1 t) ^ 2 + w2 * (y2 - g2 t) ^ 2 + (y3 - g3 t) ^ 2))
    (h0 : w1 * (f1 a - g1 a) ^ 2 + w2 * (f2 a - g2 a) ^ 2 + (f3 a - g3 a) ^ 2 ≤ δ ^ 2)
    (hB : (δ + ε * (b - a)) * Real.exp (μ * (b - a)) ≤ B) :
    ∀ t ∈ Set.Icc a b, w1 * (f1 t - g1 t) ^ 2 + w2 * (f2 t - g2 t) ^ 2 + (f3 t - g3 t) ^ 2
      ≤ ((δ + ε * (t - a)) * Real.exp (μ * (t - a))) ^ 2 := by
  set R : ℝ → ℝ := fun t => (δ + ε * (t - a)) * Real.exp (μ * (t - a)) with hRdef
  set φ : ℝ → ℝ := fun t => w1 * (f1 t - g1 t) ^ 2 + w2 * (f2 t - g2 t) ^ 2 + (f3 t - g3 t) ^ 2
    with hφdef
  have hRd : ∀ t, HasDerivAt R (ε * Real.exp (μ * (t - a)) + μ * R t) t := by
    intro t
    have h1 : HasDerivAt (fun t => δ + ε * (t - a)) ε t := by
      have := (((hasDerivAt_id t).sub_const a).const_mul ε).const_add δ
      simpa using this
    have h2 : HasDerivAt (fun t => Real.exp (μ * (t - a))) (Real.exp (μ * (t - a)) * μ) t := by
      have := (((hasDerivAt_id t).sub_const a).const_mul μ).exp
      simpa using this
    have := h1.mul h2
    convert this using 1
    simp only [hRdef]
    ring
  have hR2d : ∀ t, HasDerivAt (fun t => R t ^ 2)
      (2 * R t * (ε * Real.exp (μ * (t - a)) + μ * R t)) t := by
    intro t
    have := (hRd t).pow 2
    convert this using 1
    norm_num
  have hRcont : Continuous R := by
    simp only [hRdef]; fun_prop
  have hRge : ∀ t, a ≤ t → δ ≤ R t := by
    intro t ht
    simp only [hRdef]
    have he : 1 ≤ Real.exp (μ * (t - a)) := Real.one_le_exp (mul_nonneg hμ (by linarith))
    have hd : δ ≤ δ + ε * (t - a) := by nlinarith
    nlinarith
  have hRle : ∀ t, t ≤ b → a ≤ t → R t ≤ B := by
    intro t htb hta
    refine le_trans ?_ hB
    simp only [hRdef]
    apply mul_le_mul
    · nlinarith
    · exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hμ)
    · exact (Real.exp_pos _).le
    · nlinarith
  have key := image_le_of_deriv_right_lt_deriv_boundary' (f := φ)
    (f' := fun t => w1 * (2 * (f1 t - g1 t) * (F1 t (f1 t) (f2 t) (f3 t) - G1 t))
      + w2 * (2 * (f2 t - g2 t) * (F2 t (f1 t) (f2 t) (f3 t) - G2 t))
      + 2 * (f3 t - g3 t) * (F3 t (f1 t) (f2 t) (f3 t) - G3 t))
    (B := fun t => R t ^ 2)
    (B' := fun t => 2 * R t * (ε * Real.exp (μ * (t - a)) + μ * R t))
    (by simp only [hφdef]; fun_prop)
    (by
      intro t ht
      have e1 := ((hf1' t ht).sub (hg1' t ht)).pow 2
      have e2 := ((hf2' t ht).sub (hg2' t ht)).pow 2
      have e3 := ((hf3' t ht).sub (hg3' t ht)).pow 2
      have := ((e1.const_mul w1).add (e2.const_mul w2)).add e3
      convert this using 1
      norm_num [Pi.sub_apply])
    (by
      simp only [hφdef, hRdef, sub_self, mul_zero, add_zero, Real.exp_zero, mul_one]
      exact h0)
    (hRcont.pow 2).continuousOn
    (fun t _ => (hR2d t).hasDerivWithinAt)
    (by
      intro t ht heq
      simp only [hφdef] at heq
      set e1 := f1 t - g1 t
      set e2 := f2 t - g2 t
      set e3 := f3 t - g3 t
      set D1 := G1 t - F1 t (g1 t) (g2 t) (g3 t)
      set D2 := G2 t - F2 t (g1 t) (g2 t) (g3 t)
      set D3 := G3 t - F3 t (g1 t) (g2 t) (g3 t)
      have hRt : δ ≤ R t := hRge t ht.1
      have hRpos : 0 < R t := lt_of_lt_of_le hδ hRt
      have hRB : R t ≤ B := hRle t ht.2.le ht.1
      have hball : w1 * (f1 t - g1 t) ^ 2 + w2 * (f2 t - g2 t) ^ 2 + (f3 t - g3 t) ^ 2 ≤ B ^ 2 := by
        rw [heq]
        exact pow_le_pow_left₀ hRpos.le hRB 2
      have hos' := hos t ht (f1 t) (f2 t) (f3 t) hball
      have hD := hdef t ht
      have hcs : (w1 * e1 * D1 + w2 * e2 * D2 + e3 * D3) ^ 2 < (R t * ε) ^ 2 := by
        have hX : w1 * e1 ^ 2 + w2 * e2 ^ 2 + e3 ^ 2 = R t ^ 2 := heq
        have hid : (w1 * e1 ^ 2 + w2 * e2 ^ 2 + e3 ^ 2) * (w1 * D1 ^ 2 + w2 * D2 ^ 2 + D3 ^ 2)
            - (w1 * e1 * D1 + w2 * e2 * D2 + e3 * D3) ^ 2
            = w1 * w2 * (e1 * D2 - e2 * D1) ^ 2 + w1 * (e1 * D3 - e3 * D1) ^ 2
              + w2 * (e2 * D3 - e3 * D2) ^ 2 := by ring
        have hnn : 0 ≤ w1 * w2 * (e1 * D2 - e2 * D1) ^ 2 + w1 * (e1 * D3 - e3 * D1) ^ 2
              + w2 * (e2 * D3 - e3 * D2) ^ 2 := by positivity
        have hR2 : 0 < R t ^ 2 := by positivity
        have : R t ^ 2 * (w1 * D1 ^ 2 + w2 * D2 ^ 2 + D3 ^ 2) < R t ^ 2 * ε ^ 2 :=
          mul_lt_mul_of_pos_left hD hR2
        rw [hX] at hid
        rw [mul_pow]
        linarith
      have hab' := abs_lt_of_sq_lt_sq hcs (by positivity)
      have hexp : 1 ≤ Real.exp (μ * (t - a)) :=
        Real.one_le_exp (mul_nonneg hμ (by linarith [ht.1]))
      have hsplit : w1 * (2 * e1 * (F1 t (f1 t) (f2 t) (f3 t) - G1 t))
          + w2 * (2 * e2 * (F2 t (f1 t) (f2 t) (f3 t) - G2 t))
          + 2 * e3 * (F3 t (f1 t) (f2 t) (f3 t) - G3 t)
          = 2 * (w1 * (F1 t (f1 t) (f2 t) (f3 t) - F1 t (g1 t) (g2 t) (g3 t)) * e1
              + w2 * (F2 t (f1 t) (f2 t) (f3 t) - F2 t (g1 t) (g2 t) (g3 t)) * e2
              + (F3 t (f1 t) (f2 t) (f3 t) - F3 t (g1 t) (g2 t) (g3 t)) * e3)
            - 2 * (w1 * e1 * D1 + w2 * e2 * D2 + e3 * D3) := by
        simp only [D1, D2, D3]; ring
      rw [hsplit]
      have hε' : R t * ε ≤ R t * (ε * Real.exp (μ * (t - a))) := by
        apply mul_le_mul_of_nonneg_left _ hRpos.le
        exact le_mul_of_one_le_right hε.le hexp
      have hμR : μ * (w1 * e1 ^ 2 + w2 * e2 ^ 2 + e3 ^ 2) = μ * R t ^ 2 := by rw [heq]
      have habs := (abs_lt.1 hab').1
      linarith)
  intro t ht
  exact key ht


set_option maxHeartbeats 1600000 in
/-- One validated weighted cell from its Boolean check: the enclosure on the whole cell. -/
theorem cell_all {T : ℚ} (c : Cell) (hok : cellOK T c = true) {g p q : ℝ → ℝ}
    (hs : SolC T c.t0 g p q) (h0 : InBox c g p q) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      V c.w1 c.w2 (g t - evalQ c.pg (t - c.t0)) (p t - evalQ c.pp (t - c.t0))
        (q t - evalQ c.pq (t - c.t0)) ≤ (c.B : ℝ) ^ 2 := by
  obtain ⟨k1, k2, k3, kw1, kw2, kμ, kμh, kδ, kε, kdef, kr1, kBr, kr2, kBr2, kc1, kc2, kc3, kc4, kB, kx1, kx2, kx3, kx4, kx5, kx6⟩ :
    CellProp T c := of_decide_eq_true hok
  have hT2 : ((c.t0 + c.h : ℚ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast k2
  push_cast at hT2
  have ht0 : (0 : ℝ) ≤ c.t0 := by exact_mod_cast k1
  have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
  have hw1 : (0 : ℝ) < c.w1 := by exact_mod_cast kw1
  have hw2 : (0 : ℝ) < c.w2 := by exact_mod_cast kw2
  have hμ : (0 : ℝ) ≤ c.μ := by exact_mod_cast kμ
  have hμh : (c.μ : ℝ) * c.h < 1 := by exact_mod_cast kμh
  have hδ : (0 : ℝ) < c.δ := by exact_mod_cast kδ
  have hε : (0 : ℝ) < c.ε := by exact_mod_cast kε
  have hr1 : (0 : ℝ) ≤ c.r1 := by exact_mod_cast kr1
  have hBr : (c.B : ℝ) ^ 2 ≤ c.w1 * (c.r1 : ℝ) ^ 2 := by exact_mod_cast kBr
  have hr2 : (0 : ℝ) ≤ c.r2 := by exact_mod_cast kr2
  have hBr2 : (c.B : ℝ) ^ 2 ≤ c.w2 * (c.r2 : ℝ) ^ 2 := by exact_mod_cast kBr2
  have hdef : (c.w1 : ℝ) * ((qabs (qsub (qderiv c.pg) c.pp) c.h : ℚ) : ℝ) ^ 2
      + c.w2 * ((qabs (qsub (qderiv c.pp) c.pq) c.h : ℚ) : ℝ) ^ 2
      + ((qabs (defect3 c) c.h : ℚ) : ℝ) ^ 2 < (c.ε : ℝ) ^ 2 := by exact_mod_cast kdef
  have hBq : (((c.δ + c.ε * c.h) / (1 - c.μ * c.h) : ℚ) : ℝ) ≤ (c.B : ℝ) := by exact_mod_cast kB
  push_cast at hBq
  have hsub : Icc (c.t0 : ℝ) (c.t0 + c.h) ⊆ Icc 0 (T : ℝ) :=
    Icc_subset_Icc ht0 hT2
  have hsub' : Icc (c.t0 : ℝ) (c.t0 + c.h) ⊆ Icc (c.t0 : ℝ) T := Icc_subset_Icc le_rfl hT2
  have hnh : ∀ t ∈ Ico (c.t0 : ℝ) (c.t0 + c.h), Icc (0 : ℝ) T ∈ nhdsWithin t (Ici t) := fun t ht =>
    Icc_mem_nhdsGE_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hlo : ∀ σ ∈ Icc (0 : ℝ) c.h, ((c.pg.headD 0 - c.h * qabs c.pg.tail c.h : ℚ) : ℝ) ≤ evalQ c.pg σ :=
    fun σ hσ => lower_q c.pg (h := c.h) hσ.1 hσ.2
  have hql : ∀ σ ∈ Icc (0 : ℝ) c.h, ((qlo c : ℚ) : ℝ) ≤ evalQ c.pq σ :=
    fun σ hσ => lower_q c.pq (h := c.h) hσ.1 hσ.2
  have hqh : ∀ σ ∈ Icc (0 : ℝ) c.h, evalQ c.pq σ ≤ ((qhi c : ℚ) : ℝ) :=
    fun σ hσ => upper_q c.pq (h := c.h) hσ.1 hσ.2
  have hpl : ∀ σ ∈ Icc (0 : ℝ) c.h, ((plo c : ℚ) : ℝ) ≤ evalQ c.pp σ :=
    fun σ hσ => lower_q c.pp (h := c.h) hσ.1 hσ.2
  have hph : ∀ σ ∈ Icc (0 : ℝ) c.h, evalQ c.pp σ ≤ ((phi c : ℚ) : ℝ) :=
    fun σ hσ => upper_q c.pp (h := c.h) hσ.1 hσ.2
  have hB0 : (0 : ℝ) ≤ c.B := (cell_pos c hok).2.2.1.le
  have x1 : (-(c.t0 + 2) : ℝ) < ((glo c - c.r1 : ℚ) : ℝ) := by exact_mod_cast kx1
  have x2 : ((ghi c + c.r1 : ℚ) : ℝ) < (c.t0 + 2 : ℝ) := by exact_mod_cast kx2
  have x3 : (-2 : ℝ) < ((plo c - c.r2 : ℚ) : ℝ) := by exact_mod_cast kx3
  have x4 : ((phi c + c.r2 : ℚ) : ℝ) < 2 := by exact_mod_cast kx4
  have x5 : (-2 : ℝ) < ((qlo c - c.B : ℚ) : ℝ) := by exact_mod_cast kx5
  have x6 : ((qhi c + c.B : ℚ) : ℝ) < 2 := by exact_mod_cast kx6
  push_cast at x1 x2 x3 x4 x5 x6
  have hgl : ∀ σ ∈ Icc (0 : ℝ) c.h, ((glo c : ℚ) : ℝ) ≤ evalQ c.pg σ :=
    fun σ hσ => lower_q c.pg (h := c.h) hσ.1 hσ.2
  have hgh : ∀ σ ∈ Icc (0 : ℝ) c.h, evalQ c.pg σ ≤ ((ghi c : ℚ) : ℝ) :=
    fun σ hσ => upper_q c.pg (h := c.h) hσ.1 hσ.2
  -- inside the ball the clamps are inactive
  have cl1 : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), ∀ y : ℝ, |y - evalQ c.pg (t - c.t0)| ≤ c.r1 →
      cl (max t 0 + 2) y = y := by
    intro t ht y hy
    have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have a1 := hgl _ hσ; have a2 := hgh _ hσ
    have hm : (c.t0 : ℝ) ≤ max t 0 := le_trans ht.1 (le_max_left _ _)
    apply cl_of_abs_le; rw [abs_le]
    constructor <;> linarith [(abs_le.1 hy).1, (abs_le.1 hy).2]
  have cl2 : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), ∀ y : ℝ, |y - evalQ c.pp (t - c.t0)| ≤ c.r2 →
      cl 2 y = y := by
    intro t ht y hy
    have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have a1 := hpl _ hσ; have a2 := hph _ hσ
    apply cl_of_abs_le; rw [abs_le]
    constructor <;> linarith [(abs_le.1 hy).1, (abs_le.1 hy).2]
  have cl3 : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), ∀ y : ℝ, |y - evalQ c.pq (t - c.t0)| ≤ c.B →
      cl 2 y = y := by
    intro t ht y hy
    have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have a1 := hql _ hσ; have a2 := hqh _ hσ
    apply cl_of_abs_le; rw [abs_le]
    constructor <;> linarith [(abs_le.1 hy).1, (abs_le.1 hy).2]
  have key := onesided3_cell_t (F1 := fun _ _ y2 _ => cl 2 y2) (F2 := fun _ _ _ y3 => cl 2 y3)
    (F3 := fun t y1 y2 y3 => -(cl (max t 0 + 2) y1 * cl 2 y3) - 1 + cl 2 y2 ^ 2) (f1 := g) (f2 := p) (f3 := q)
    (g1 := fun t => evalQ c.pg (t - c.t0)) (g2 := fun t => evalQ c.pp (t - c.t0))
    (g3 := fun t => evalQ c.pq (t - c.t0))
    (G1 := fun t => dEvalQ c.pg (t - c.t0)) (G2 := fun t => dEvalQ c.pp (t - c.t0))
    (G3 := fun t => dEvalQ c.pq (t - c.t0))
    (a := c.t0) (b := c.t0 + c.h) (w1 := c.w1) (w2 := c.w2) (μ := c.μ) (ε := c.ε) (δ := c.δ)
    (B := c.B)
    (by linarith) hw1 hw2 hμ hε hδ
    (fun t ht => ((hs.1 t (hsub' ht)).continuousWithinAt).mono hsub)
    (fun t ht => ((hs.2.1 t (hsub' ht)).continuousWithinAt).mono hsub)
    (fun t ht => ((hs.2.2 t (hsub' ht)).continuousWithinAt).mono hsub)
    ((continuous_evalQ c.pg).comp (continuous_sub_right _)).continuousOn
    ((continuous_evalQ c.pp).comp (continuous_sub_right _)).continuousOn
    ((continuous_evalQ c.pq).comp (continuous_sub_right _)).continuousOn
    (fun t ht => (hs.1 t (hsub' (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin (hnh t ht))
    (fun t ht => (hs.2.1 t (hsub' (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin (hnh t ht))
    (fun t ht => (hs.2.2 t (hsub' (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin (hnh t ht))
    (fun t _ => ((hasDerivAt_evalQ c.pg _).comp_sub_const t _).hasDerivWithinAt)
    (fun t _ => ((hasDerivAt_evalQ c.pp _).comp_sub_const t _).hasDerivWithinAt)
    (fun t _ => ((hasDerivAt_evalQ c.pq _).comp_sub_const t _).hasDerivWithinAt)
    (fun t ht => by
      have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have ht' : t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h) := Ico_subset_Icc_self ht
      rw [cl1 t ht' _ (by simpa using hr1), cl2 t ht' _ (by simpa using hr2),
        cl3 t ht' _ (by simpa using hB0)]
      have d1 := abs_le_qabs (qsub (qderiv c.pg) c.pp) hσ.1 hσ.2
      have d2 := abs_le_qabs (qsub (qderiv c.pp) c.pq) hσ.1 hσ.2
      have d3 := abs_le_qabs (defect3 c) hσ.1 hσ.2
      rw [evalQ_qsub, ← dEvalQ_eq] at d1 d2
      rw [← defect3_eval] at d3
      have s1 := sq_le_sq' (abs_le.1 d1).1 (abs_le.1 d1).2
      have s2 := sq_le_sq' (abs_le.1 d2).1 (abs_le.1 d2).2
      have s3 := sq_le_sq' (abs_le.1 d3).1 (abs_le.1 d3).2
      have e3 : dEvalQ c.pq (t - c.t0) - (-(evalQ c.pg (t - c.t0) * evalQ c.pq (t - c.t0)) - 1
            + evalQ c.pp (t - c.t0) ^ 2)
          = dEvalQ c.pq (t - c.t0) + evalQ c.pg (t - c.t0) * evalQ c.pq (t - c.t0) + 1
            - evalQ c.pp (t - c.t0) ^ 2 := by ring
      simp only [e3]
      nlinarith [mul_le_mul_of_nonneg_left s1 hw1.le, mul_le_mul_of_nonneg_left s2 hw2.le])
    (fun t ht y1 y2 y3 hy => by
      have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have n1 := mul_nonneg hw1.le (sq_nonneg (y1 - evalQ c.pg (t - c.t0)))
      have n2 := mul_nonneg hw2.le (sq_nonneg (y2 - evalQ c.pp (t - c.t0)))
      have n3 := sq_nonneg (y3 - evalQ c.pq (t - c.t0))
      have he1 : |y1 - evalQ c.pg (t - c.t0)| ≤ c.r1 := comp_le hw1 hr1 (by linarith) hBr
      have he2 : |y2 - evalQ c.pp (t - c.t0)| ≤ c.r2 := comp_le hw2 hr2 (by linarith) hBr2
      have he3 : |y3 - evalQ c.pq (t - c.t0)| ≤ c.B :=
        comp_le (w := 1) (B := (c.B : ℝ)) one_pos hB0 (by linarith) (by linarith)
      have ht' : t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h) := Ico_subset_Icc_self ht
      rw [cl1 t ht' _ he1, cl2 t ht' _ he2, cl3 t ht' _ he3,
        cl1 t ht' _ (by simpa using hr1), cl2 t ht' _ (by simpa using hr2),
        cl3 t ht' _ (by simpa using hB0)]
      have hm : ((mlo c : ℚ) : ℝ) ≤ y1 := by
        have := hlo _ hσ
        unfold mlo; push_cast at this ⊢
        linarith [(abs_le.1 he1).1]
      have hs1 : ((2 * plo c - c.r2 : ℚ) : ℝ) ≤ y2 + evalQ c.pp (t - c.t0) := by
        have := hpl _ hσ
        push_cast
        linarith [(abs_le.1 he2).1]
      have hs2 : y2 + evalQ c.pp (t - c.t0) ≤ ((2 * phi c + c.r2 : ℚ) : ℝ) := by
        have := hph _ hσ
        push_cast
        linarith [(abs_le.1 he2).2]
      have := os_hiemenz (μ := c.μ) (w1 := c.w1) (w2 := c.w2) (m := ((mlo c : ℚ) : ℝ))
        (ql := ((qlo c : ℚ) : ℝ)) (qh := ((qhi c : ℚ) : ℝ))
        (sl := ((2 * plo c - c.r2 : ℚ) : ℝ)) (sh := ((2 * phi c + c.r2 : ℚ) : ℝ))
        (P1 := evalQ c.pg (t - c.t0)) (P2 := evalQ c.pp (t - c.t0))
        (P3 := evalQ c.pq (t - c.t0)) (y1 := y1) (y2 := y2) (y3 := y3)
        (quad_of_psd kc1) (quad_of_psd kc2) (quad_of_psd kc3) (quad_of_psd kc4)
        hm (hql _ hσ) (hqh _ hσ) hs1 hs2
      simpa using this)
    (by
      simp only [sub_self, evalQ_zero_head]
      exact h0)
    (R_le hδ hε hμ hμh hBq ⟨by linarith, le_rfl⟩)
  intro t ht
  have e := key t ht
  have hpos : (0 : ℝ) ≤ (c.δ + c.ε * (t - c.t0)) * Real.exp (c.μ * (t - c.t0)) :=
    mul_nonneg (by nlinarith [ht.1]) (Real.exp_pos _).le
  have hsq := pow_le_pow_left₀ hpos (R_le hδ hε hμ hμh hBq ht) 2
  unfold V
  exact e.trans hsq

/-- One validated weighted cell from its Boolean check: the enclosure at the cell's end. -/
theorem cell_w {T : ℚ} (c : Cell) (hok : cellOK T c = true) {g p q : ℝ → ℝ}
    (hs : SolC T c.t0 g p q) (h0 : InBox c g p q) : AtEnd c g p q := by
  have hh : (0 : ℝ) < c.h := by exact_mod_cast (cellOK_basic c hok).2.2
  have e := cell_all c hok hs h0 (c.t0 + c.h) ⟨by linarith, le_rfl⟩
  unfold AtEnd
  simp only [add_sub_cancel_left] at e
  simpa only [qeval_cast] using e

/-- The undershoot side condition: the p-component stays below 1 on the cell. -/
def sideU (c : Cell) : Bool := decide (phi c + c.r2 < 1)

/-- The overshoot side condition: the q-component stays positive on the cell. -/
def sideO (c : Cell) : Bool := decide (0 < qlo c - c.B)

theorem sideU_spec {T : ℚ} (c : Cell) (hok : cellOK T c = true) (hside : sideU c = true)
    {g p q : ℝ → ℝ} (hs : SolC T c.t0 g p q) (h0 : InBox c g p q) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), p t < 1 := by
  obtain ⟨-, -, -, kw1, kw2, -, -, -, -, -, -, -, kr2, kBr2, -⟩ : CellProp T c := of_decide_eq_true hok
  have hw1 : (0 : ℝ) < c.w1 := by exact_mod_cast kw1
  have hw2 : (0 : ℝ) < c.w2 := by exact_mod_cast kw2
  have hr2 : (0 : ℝ) ≤ c.r2 := by exact_mod_cast kr2
  have hBr2 : (c.B : ℝ) ^ 2 ≤ c.w2 * (c.r2 : ℝ) ^ 2 := by exact_mod_cast kBr2
  have hU : ((phi c + c.r2 : ℚ) : ℝ) < 1 := by exact_mod_cast (of_decide_eq_true hside)
  push_cast at hU
  intro t ht
  have e := cell_all c hok hs h0 t ht
  unfold V at e
  have n1 := mul_nonneg hw1.le (sq_nonneg (g t - evalQ c.pg (t - c.t0)))
  have n3 := sq_nonneg (q t - evalQ c.pq (t - c.t0))
  have he2 : |p t - evalQ c.pp (t - c.t0)| ≤ c.r2 := comp_le hw2 hr2 (by linarith) hBr2
  have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hp := upper_q c.pp (h := c.h) hσ.1 hσ.2
  have hphi : ((phi c : ℚ) : ℝ) = ((c.pp.headD 0 + c.h * qabs c.pp.tail c.h : ℚ) : ℝ) := rfl
  rw [← hphi] at hp
  linarith [(abs_le.1 he2).2]

theorem sideO_spec {T : ℚ} (c : Cell) (hok : cellOK T c = true) (hside : sideO c = true)
    {g p q : ℝ → ℝ} (hs : SolC T c.t0 g p q) (h0 : InBox c g p q) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), 0 < q t := by
  obtain ⟨-, -, -, kw1, kw2, -⟩ : CellProp T c := of_decide_eq_true hok
  have hw1 : (0 : ℝ) < c.w1 := by exact_mod_cast kw1
  have hw2 : (0 : ℝ) < c.w2 := by exact_mod_cast kw2
  have hO : (0 : ℝ) < ((qlo c - c.B : ℚ) : ℝ) := by exact_mod_cast (of_decide_eq_true hside)
  push_cast at hO
  intro t ht
  have e := cell_all c hok hs h0 t ht
  unfold V at e
  have n1 := mul_nonneg hw1.le (sq_nonneg (g t - evalQ c.pg (t - c.t0)))
  have n2 := mul_nonneg hw2.le (sq_nonneg (p t - evalQ c.pp (t - c.t0)))
  have hB0 : (0 : ℝ) ≤ c.B := (cell_pos c hok).2.2.1.le
  have he3 : |q t - evalQ c.pq (t - c.t0)| ≤ c.B :=
    comp_le (w := 1) (B := (c.B : ℝ)) one_pos hB0 (by linarith) (by linarith)
  have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hq := lower_q c.pq (h := c.h) hσ.1 hσ.2
  have hqlo : ((qlo c : ℚ) : ℝ) = ((c.pq.headD 0 - c.h * qabs c.pq.tail c.h : ℚ) : ℝ) := rfl
  rw [← hqlo] at hq
  linarith [(abs_le.1 he3).1]

/-- The squared weighted norm of a rational vector, over ℚ. -/
def Vq (w1 w2 a b c : ℚ) : ℚ := w1 * a ^ 2 + w2 * b ^ 2 + c ^ 2

/-- Consecutive cells meet with the same weights, and the end ball of `c` lies in the input
ball of `d` (Minkowski with s = d.δ − c.B). -/
def linkOK (c d : Cell) : Bool :=
  decide (c.t0 + c.h = d.t0 ∧ c.w1 = d.w1 ∧ c.w2 = d.w2 ∧ 0 < c.w1 ∧ 0 < c.w2 ∧ 0 ≤ c.B ∧
    0 ≤ d.δ - c.B ∧
    Vq c.w1 c.w2 (qeval c.pg c.h - d.pg.headD 0) (qeval c.pp c.h - d.pp.headD 0)
      (qeval c.pq c.h - d.pq.headD 0) ≤ (d.δ - c.B) ^ 2)

/-- A chain of cells inside [0, T], each satisfying `side`, whose last cell satisfies `term`. -/
def chainS (T : ℚ) (side term : Cell → Bool) : List Cell → Bool
  | [] => false
  | [c] => cellOK T c && side c && term c
  | c :: d :: l => cellOK T c && side c && linkOK c d && chainS T side term (d :: l)

theorem link_box {c d : Cell} (hl : linkOK c d = true) {g p q : ℝ → ℝ} (he : AtEnd c g p q) :
    (d.t0 : ℝ) = c.t0 + c.h ∧ InBox d g p q := by
  obtain ⟨ke, kw1, kw2, kp1, kp2, kB, ks, kV⟩ := of_decide_eq_true hl
  have he' : ((c.t0 + c.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
  push_cast at he'
  have hB : (0 : ℝ) ≤ c.B := by exact_mod_cast kB
  have hs : (0 : ℝ) ≤ ((d.δ - c.B : ℚ) : ℝ) := by exact_mod_cast ks
  have hV : ((Vq c.w1 c.w2 (qeval c.pg c.h - d.pg.headD 0) (qeval c.pp c.h - d.pp.headD 0)
      (qeval c.pq c.h - d.pq.headD 0) : ℚ) : ℝ) ≤ (((d.δ - c.B : ℚ) : ℝ)) ^ 2 := by exact_mod_cast kV
  have hw1 : (0 : ℝ) < c.w1 := by exact_mod_cast kp1
  have hw2 : (0 : ℝ) < c.w2 := by exact_mod_cast kp2
  unfold Vq at hV
  push_cast at hV hs
  refine ⟨he'.symm, ?_⟩
  unfold InBox V; unfold AtEnd V at he
  rw [← he', ← kw1, ← kw2]
  have k := wnorm_add hw1 hw2 hB hs he hV
  have e : (c.B : ℝ) + (d.δ - c.B) = d.δ := by ring
  rw [e] at k
  convert k using 2 <;> ring

/-- A chain from its Boolean check: some last cell `e` satisfies `term`, every solution entering
the first cell's ball is enclosed at `e`'s end, and `Φ` holds from the first cell's start to
`e`'s end. -/
theorem chainS_gen {T : ℚ} {side term : Cell → Bool}
    {Φ : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → Prop}
    (hside : ∀ c, cellOK T c = true → side c = true → ∀ {g p q : ℝ → ℝ}, SolC T c.t0 g p q →
      InBox c g p q → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), Φ g p q t) :
    ∀ (l : List Cell) (c : Cell), chainS T side term (c :: l) = true →
    ∀ {g p q : ℝ → ℝ}, SolC T c.t0 g p q → InBox c g p q →
    ∃ e : Cell, cellOK T e = true ∧ term e = true ∧ AtEnd e g p q ∧
      ∀ t ∈ Icc (c.t0 : ℝ) (e.t0 + e.h), Φ g p q t := by
  intro l
  induction l with
  | nil =>
    intro c hok g p q hs h0
    simp only [chainS, Bool.and_eq_true] at hok
    exact ⟨c, hok.1.1, hok.2, cell_w c hok.1.1 hs h0, hside c hok.1.1 hok.1.2 hs h0⟩
  | cons d l ih =>
    intro c hok g p q hs h0
    simp only [chainS, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨k1, ks⟩, kl⟩, krest⟩ := hok
    have he := cell_w c k1 hs h0
    obtain ⟨hdt, hbox⟩ := link_box kl he
    have hh : (0 : ℝ) < c.h := by exact_mod_cast (cellOK_basic c k1).2.2
    have hc := hside c k1 ks hs h0
    obtain ⟨e, hke, hte, hend, hΦ⟩ := ih d krest (hs.mono (by rw [hdt]; linarith)) hbox
    refine ⟨e, hke, hte, hend, fun t ht => ?_⟩
    rcases le_total t (c.t0 + c.h) with h1 | h1
    · exact hc t ⟨ht.1, h1⟩
    · exact hΦ t ⟨by rw [hdt]; exact h1, ht.2⟩

theorem chainS_head {T : ℚ} {side term : Cell → Bool} (c : Cell) (l : List Cell)
    (h : chainS T side term (c :: l) = true) : cellOK T c = true := by
  cases l with
  | nil => simp only [chainS, Bool.and_eq_true] at h; exact h.1.1
  | cons _ _ => simp only [chainS, Bool.and_eq_true] at h; exact h.1.1.1

/-- A segment ending in the input ball of `d`, with `Φ` on [c.t0, d.t0]; solution hypotheses on
the whole of [0, T]. -/
theorem segS_q0 {T : ℚ} {side : Cell → Bool} {Φ : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → Prop}
    (hside : ∀ c, cellOK T c = true → side c = true → ∀ {g p q : ℝ → ℝ}, SolC T c.t0 g p q →
      InBox c g p q → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), Φ g p q t)
    (d : Cell) (l : List Cell) (c : Cell)
    (hok : chainS T side (fun e => linkOK e d) (c :: l) = true) {g p q : ℝ → ℝ}
    (hs : SolC T 0 g p q) (h0 : InBox c g p q) :
    InBox d g p q ∧ ∀ t ∈ Icc (c.t0 : ℝ) d.t0, Φ g p q t := by
  have k := (cellOK_basic c (chainS_head c l hok)).1
  obtain ⟨e, -, he, hend, hΦ⟩ := chainS_gen hside l c hok (hs.mono (by exact_mod_cast k)) h0
  obtain ⟨hdt, hbox⟩ := link_box he hend
  exact ⟨hbox, by rw [hdt]; exact hΦ⟩

/-- Terminal condition of the undershoot chain: the last cell ends at `T` with q below 0. -/
def endU (T : ℚ) (c : Cell) : Bool := decide (c.t0 + c.h = T ∧ qeval c.pq c.h + c.B < 0)

/-- Terminal condition of the overshoot chain: the last cell ends at `T` with p above 1. -/
def endO (T : ℚ) (c : Cell) : Bool := decide (c.t0 + c.h = T ∧ 1 < qeval c.pp c.h - c.r2)

/-- A final undershoot segment: q(T) < 0 and `Φ` on [c.t0, T]. -/
theorem endS_q0 {T : ℚ} {side : Cell → Bool} {Φ : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → Prop}
    (hside : ∀ c, cellOK T c = true → side c = true → ∀ {g p q : ℝ → ℝ}, SolC T c.t0 g p q →
      InBox c g p q → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), Φ g p q t)
    (l : List Cell) (c : Cell) (hok : chainS T side (endU T) (c :: l) = true) {g p q : ℝ → ℝ}
    (hs : SolC T 0 g p q) (h0 : InBox c g p q) :
    q T < 0 ∧ ∀ t ∈ Icc (c.t0 : ℝ) T, Φ g p q t := by
  have k := (cellOK_basic c (chainS_head c l hok)).1
  obtain ⟨e, hke, he, hend, hΦ⟩ := chainS_gen hside l c hok (hs.mono (by exact_mod_cast k)) h0
  obtain ⟨kT, kq⟩ := of_decide_eq_true he
  obtain ⟨hw1, hw2, hB, -, -⟩ := cell_pos e hke
  have hT : ((e.t0 + e.h : ℚ) : ℝ) = (T : ℝ) := by exact_mod_cast kT
  push_cast at hT
  have kq' : ((qeval e.pq e.h + e.B : ℚ) : ℝ) < 0 := by exact_mod_cast kq
  push_cast at kq'
  unfold AtEnd V at hend
  rw [hT] at hend hΦ
  refine ⟨?_, hΦ⟩
  have n1 := mul_nonneg hw1.le (sq_nonneg (g T - ((qeval e.pg e.h : ℚ) : ℝ)))
  have n2 := mul_nonneg hw2.le (sq_nonneg (p T - ((qeval e.pp e.h : ℚ) : ℝ)))
  have b3 : |q T - ((qeval e.pq e.h : ℚ) : ℝ)| ≤ e.B :=
    comp_le (w := 1) (B := (e.B : ℝ)) one_pos hB.le (by linarith) (by linarith)
  linarith [(abs_le.1 b3).2]

/-- A final overshoot segment: p(T) > 1 and `Φ` on [c.t0, T]. -/
theorem endSO_q0 {T : ℚ} {side : Cell → Bool} {Φ : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → Prop}
    (hside : ∀ c, cellOK T c = true → side c = true → ∀ {g p q : ℝ → ℝ}, SolC T c.t0 g p q →
      InBox c g p q → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), Φ g p q t)
    (l : List Cell) (c : Cell) (hok : chainS T side (endO T) (c :: l) = true) {g p q : ℝ → ℝ}
    (hs : SolC T 0 g p q) (h0 : InBox c g p q) :
    1 < p T ∧ ∀ t ∈ Icc (c.t0 : ℝ) T, Φ g p q t := by
  have k := (cellOK_basic c (chainS_head c l hok)).1
  obtain ⟨e, hke, he, hend, hΦ⟩ := chainS_gen hside l c hok (hs.mono (by exact_mod_cast k)) h0
  obtain ⟨kT, kp⟩ := of_decide_eq_true he
  obtain ⟨hw1, hw2, hB, hr2, hBr2⟩ := cell_pos e hke
  have hT : ((e.t0 + e.h : ℚ) : ℝ) = (T : ℝ) := by exact_mod_cast kT
  push_cast at hT
  have kp' : (1 : ℝ) < ((qeval e.pp e.h - e.r2 : ℚ) : ℝ) := by exact_mod_cast kp
  push_cast at kp'
  unfold AtEnd V at hend
  rw [hT] at hend hΦ
  refine ⟨?_, hΦ⟩
  have n1 := mul_nonneg hw1.le (sq_nonneg (g T - ((qeval e.pg e.h : ℚ) : ℝ)))
  have n3 := sq_nonneg (q T - ((qeval e.pq e.h : ℚ) : ℝ))
  have b2 : |p T - ((qeval e.pp e.h : ℚ) : ℝ)| ≤ e.r2 := comp_le hw2 hr2 (by linarith) hBr2
  linarith [(abs_le.1 b2).1]

end Checked.Hiemenz.HCellWC
