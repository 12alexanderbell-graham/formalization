import Mathlib
import Checked.Sim.QPoly
import Work.Sim.OneSided3

/-!
# Blasius: weighted one-sided cells checked by kernel evaluation (run 2026-11-07T1628Z)

The cells of `Work.Blasius.BCellQ` bound the error in the sup norm with the full Lipschitz constant
of the field, so the damping term −g·q/2 counts as growth and errors were amplified ≈ 10¹⁷ over
[0, 9] (forcing 10⁻³² coefficients). Here the error is measured in the weighted norm
V(e) = w1·e1² + w2·e2² + e3² and grows only with a one-sided (logarithmic-norm) bound μ of the
field on the ball of radius B around the approximation (`Work.Sim.OneSided3.onesided3_cell`); the
bound μ is certified per cell by a 3×3 positive-semidefiniteness check at the two ends of the
range of the approximation's q-component (`psdOK`, Sylvester's criterion). Every numeric
condition of a cell is one proposition over ℚ (`CellProp`), decided by kernel evaluation, and a
chain of cells is one Boolean (`chainTo`).
-/

namespace Work.Blasius.BCellW
open Set Checked.Sim Checked.Sim.QPoly Work.Sim.OneSided3

/-- One cell: start `t0`, length `h`, input radius `δ`, defect bound `ε` and output radius `B`
in the weighted norm with weights `w1`, `w2`, one-sided bound `μ`, a bound `r1` of the first
error component on the ball, and the Taylor polynomials `pg`, `pp`, `pq`. -/
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
  pg : List ℚ
  pp : List ℚ
  pq : List ℚ

/-- The third defect pq′ + pg·pq/2. -/
def defect3 (c : Cell) : List ℚ := qadd (qderiv c.pq) (qsmul (1 / 2) (qmul c.pg c.pq))

/-- The determinant of the symmetric 3×3 matrix with entries m11 … m33. -/
def det3 (m11 m12 m13 m22 m23 m33 : ℚ) : ℚ :=
  m11 * (m22 * m33 - m23 ^ 2) - m12 * (m12 * m33 - m23 * m13) + m13 * (m12 * m23 - m22 * m13)

/-- Sylvester's criterion for the one-sided bound at one value `P3` of the q-component and a
lower bound `m` of the g-component. -/
def psdOK (μ w1 w2 m P3 : ℚ) : Prop :=
  0 < μ * w1 ∧ 0 < μ * w1 * (μ * w2) - (-(w1 / 2)) ^ 2 ∧
  0 ≤ det3 (μ * w1) (-(w1 / 2)) (P3 / 4) (μ * w2) (-(w2 / 2)) (μ + m / 2)

/-- Lower bound of the g-component on the ball: the polynomial's lower bound minus `r1`. -/
def mlo (c : Cell) : ℚ := c.pg.headD 0 - c.h * qabs c.pg.tail c.h - c.r1

/-- Lower end of the q-component of the approximation on the cell. -/
def qlo (c : Cell) : ℚ := c.pq.headD 0 - c.h * qabs c.pq.tail c.h

/-- Upper end of the q-component of the approximation on the cell. -/
def qhi (c : Cell) : ℚ := c.pq.headD 0 + c.h * qabs c.pq.tail c.h

/-- All hypotheses of the weighted cell step except the solution's own, over ℚ. -/
def CellProp (T : ℚ) (c : Cell) : Prop :=
  0 ≤ c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h ∧ 0 < c.w1 ∧ 0 < c.w2 ∧ 0 ≤ c.μ ∧ c.μ * c.h < 1 ∧
  0 < c.δ ∧ 0 < c.ε ∧
  c.w1 * qabs (qsub (qderiv c.pg) c.pp) c.h ^ 2 + c.w2 * qabs (qsub (qderiv c.pp) c.pq) c.h ^ 2
    + qabs (defect3 c) c.h ^ 2 < c.ε ^ 2 ∧
  0 ≤ c.r1 ∧ c.B ^ 2 ≤ c.w1 * c.r1 ^ 2 ∧
  psdOK c.μ c.w1 c.w2 (mlo c) (qlo c) ∧ psdOK c.μ c.w1 c.w2 (mlo c) (qhi c) ∧
  (c.δ + c.ε * c.h) / (1 - c.μ * c.h) ≤ c.B

instance (T : ℚ) (c : Cell) : Decidable (CellProp T c) := by
  unfold CellProp psdOK; infer_instance

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

/-- The one-sided bound of the Blasius field on the ball, from the two Sylvester checks. -/
theorem os_blasius {μ w1 w2 m ql qh P1 P3 y1 y2 y3 P2 : ℝ}
    (Hl : ∀ x y z : ℝ, 0 ≤ μ * w1 * x ^ 2 + μ * w2 * y ^ 2 + (μ + m / 2) * z ^ 2
        + 2 * (-(w1 / 2)) * x * y + 2 * (ql / 4) * x * z + 2 * (-(w2 / 2)) * y * z)
    (Hh : ∀ x y z : ℝ, 0 ≤ μ * w1 * x ^ 2 + μ * w2 * y ^ 2 + (μ + m / 2) * z ^ 2
        + 2 * (-(w1 / 2)) * x * y + 2 * (qh / 4) * x * z + 2 * (-(w2 / 2)) * y * z)
    (hm : m ≤ y1) (hq1 : ql ≤ P3) (hq2 : P3 ≤ qh) :
    w1 * (y2 - P2) * (y1 - P1) + w2 * (y3 - P3) * (y2 - P2)
      + (-(y1 * y3 / 2) - -(P1 * P3 / 2)) * (y3 - P3)
      ≤ μ * (w1 * (y1 - P1) ^ 2 + w2 * (y2 - P2) ^ 2 + (y3 - P3) ^ 2) := by
  set e1 := y1 - P1 with he1
  set e2 := y2 - P2 with he2
  set e3 := y3 - P3 with he3
  have hy1 : y1 = P1 + e1 := by rw [he1]; ring
  have hy3 : y3 = P3 + e3 := by rw [he3]; ring
  have key : μ * (w1 * e1 ^ 2 + w2 * e2 ^ 2 + e3 ^ 2)
      - (w1 * e2 * e1 + w2 * e3 * e2 + (-(y1 * y3 / 2) - -(P1 * P3 / 2)) * e3)
      = (μ * w1 * e1 ^ 2 + μ * w2 * e2 ^ 2 + (μ + m / 2) * e3 ^ 2
        + 2 * (-(w1 / 2)) * e1 * e2 + 2 * (P3 / 4) * e1 * e3 + 2 * (-(w2 / 2)) * e2 * e3)
        + (y1 - m) / 2 * e3 ^ 2 := by
    rw [hy1, hy3]; ring
  have hy : 0 ≤ (y1 - m) / 2 * e3 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  rcases le_total 0 (e1 * e3) with h13 | h13
  · have h := Hl e1 e2 e3
    have : 0 ≤ (P3 - ql) / 2 * (e1 * e3) := mul_nonneg (by linarith) h13
    nlinarith
  · have h := Hh e1 e2 e3
    have : 0 ≤ (qh - P3) / 2 * (-(e1 * e3)) := mul_nonneg (by linarith) (by linarith)
    nlinarith

theorem quad_of_psd {μ w1 w2 m P3 : ℚ} (h : psdOK μ w1 w2 m P3) (x y z : ℝ) :
    0 ≤ (μ : ℝ) * w1 * x ^ 2 + μ * w2 * y ^ 2 + (μ + m / 2) * z ^ 2
        + 2 * (-((w1 : ℝ) / 2)) * x * y + 2 * ((P3 : ℝ) / 4) * x * z + 2 * (-((w2 : ℝ) / 2)) * y * z := by
  obtain ⟨h1, h2, h3⟩ := h
  have r1 : (0 : ℝ) < ((μ * w1 : ℚ) : ℝ) := by exact_mod_cast h1
  have r2 : (0 : ℝ) < ((μ * w1 * (μ * w2) - (-(w1 / 2)) ^ 2 : ℚ) : ℝ) := by exact_mod_cast h2
  have r3 : (0 : ℝ) ≤ ((det3 (μ * w1) (-(w1 / 2)) (P3 / 4) (μ * w2) (-(w2 / 2)) (μ + m / 2) : ℚ) : ℝ) := by
    exact_mod_cast h3
  unfold det3 at r3
  push_cast at r1 r2 r3
  exact quad3_nonneg r1 r2 r3 x y z

/-- One validated weighted cell from its Boolean check: the enclosure at the cell's end. -/
theorem cell_w {T : ℚ} (c : Cell) (hok : cellOK T c = true) {g p q : ℝ → ℝ}
    (hs : Sol T c.t0 g p q) (h0 : InBox c g p q) : AtEnd c g p q := by
  obtain ⟨k1, k2, k3, kw1, kw2, kμ, kμh, kδ, kε, kdef, kr1, kBr, kpl, kph, kB⟩ :
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
  -- the bounds of the approximation on the cell
  have hlo : ∀ σ ∈ Icc (0 : ℝ) c.h, ((c.pg.headD 0 - c.h * qabs c.pg.tail c.h : ℚ) : ℝ) ≤ evalQ c.pg σ :=
    fun σ hσ => lower_q c.pg (h := c.h) hσ.1 hσ.2
  have hql : ∀ σ ∈ Icc (0 : ℝ) c.h, ((qlo c : ℚ) : ℝ) ≤ evalQ c.pq σ :=
    fun σ hσ => lower_q c.pq (h := c.h) hσ.1 hσ.2
  have hqh : ∀ σ ∈ Icc (0 : ℝ) c.h, evalQ c.pq σ ≤ ((qhi c : ℚ) : ℝ) :=
    fun σ hσ => upper_q c.pq (h := c.h) hσ.1 hσ.2
  have key := onesided3_cell (F1 := fun _ y2 _ => y2) (F2 := fun _ _ y3 => y3)
    (F3 := fun y1 _ y3 => -(y1 * y3 / 2)) (f1 := g) (f2 := p) (f3 := q)
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
      have d1 := abs_le_qabs (qsub (qderiv c.pg) c.pp) hσ.1 hσ.2
      have d2 := abs_le_qabs (qsub (qderiv c.pp) c.pq) hσ.1 hσ.2
      have d3 := abs_le_qabs (defect3 c) hσ.1 hσ.2
      rw [evalQ_qsub, ← dEvalQ_eq] at d1 d2
      rw [← defect3_eval] at d3
      have s1 := sq_le_sq' (abs_le.1 d1).1 (abs_le.1 d1).2
      have s2 := sq_le_sq' (abs_le.1 d2).1 (abs_le.1 d2).2
      have s3 := sq_le_sq' (abs_le.1 d3).1 (abs_le.1 d3).2
      have e3 : dEvalQ c.pq (t - c.t0) - -(evalQ c.pg (t - c.t0) * evalQ c.pq (t - c.t0) / 2)
          = dEvalQ c.pq (t - c.t0) + evalQ c.pg (t - c.t0) * evalQ c.pq (t - c.t0) / 2 := by ring
      simp only [e3]
      nlinarith [mul_le_mul_of_nonneg_left s1 hw1.le, mul_le_mul_of_nonneg_left s2 hw2.le])
    (fun t ht y1 y2 y3 hy => by
      have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have he1 : |y1 - evalQ c.pg (t - c.t0)| ≤ c.r1 := by
        refine comp_le hw1 hr1 ?_ hBr
        have := sq_nonneg (y2 - evalQ c.pp (t - c.t0))
        have := sq_nonneg (y3 - evalQ c.pq (t - c.t0))
        nlinarith [mul_nonneg hw2.le (sq_nonneg (y2 - evalQ c.pp (t - c.t0)))]
      have hm : ((mlo c : ℚ) : ℝ) ≤ y1 := by
        have := hlo _ hσ
        unfold mlo; push_cast at this ⊢
        linarith [(abs_le.1 he1).1]
      have := os_blasius (μ := c.μ) (w1 := c.w1) (w2 := c.w2) (m := ((mlo c : ℚ) : ℝ))
        (ql := ((qlo c : ℚ) : ℝ)) (qh := ((qhi c : ℚ) : ℝ)) (P1 := evalQ c.pg (t - c.t0))
        (P3 := evalQ c.pq (t - c.t0)) (P2 := evalQ c.pp (t - c.t0)) (y1 := y1) (y2 := y2) (y3 := y3)
        (quad_of_psd kpl) (quad_of_psd kph) hm (hql _ hσ) (hqh _ hσ)
      simpa using this)
    (by
      simp only [sub_self, evalQ_zero_head]
      exact h0)
    (by
      have hx : (c.μ : ℝ) * (c.t0 + c.h - c.t0) < 1 := by simpa using hμh
      have he := exp_le_inv' hx
      have hpos : (0 : ℝ) ≤ c.δ + c.ε * (c.t0 + c.h - c.t0) := by nlinarith
      have h1 : (0 : ℝ) < 1 - c.μ * c.h := by linarith
      calc (c.δ + c.ε * (c.t0 + c.h - c.t0)) * Real.exp (c.μ * (c.t0 + c.h - c.t0))
          ≤ (c.δ + c.ε * (c.t0 + c.h - c.t0)) * (1 / (1 - c.μ * (c.t0 + c.h - c.t0))) :=
            mul_le_mul_of_nonneg_left he hpos
        _ = (c.δ + c.ε * c.h) / (1 - c.μ * c.h) := by ring_nf
        _ ≤ c.B := hBq)
  have e := key (c.t0 + c.h) ⟨by linarith, le_rfl⟩
  have hx : (c.μ : ℝ) * (c.t0 + c.h - c.t0) < 1 := by simpa using hμh
  have hpos : (0 : ℝ) ≤ (c.δ + c.ε * (c.t0 + c.h - c.t0)) * Real.exp (c.μ * (c.t0 + c.h - c.t0)) :=
    mul_nonneg (by nlinarith) (Real.exp_pos _).le
  have hle : (c.δ + c.ε * (c.t0 + c.h - c.t0)) * Real.exp (c.μ * (c.t0 + c.h - c.t0)) ≤ c.B := by
    have he := exp_le_inv' hx
    have h1 : (0 : ℝ) < 1 - c.μ * c.h := by linarith
    calc (c.δ + c.ε * (c.t0 + c.h - c.t0)) * Real.exp (c.μ * (c.t0 + c.h - c.t0))
        ≤ (c.δ + c.ε * (c.t0 + c.h - c.t0)) * (1 / (1 - c.μ * (c.t0 + c.h - c.t0))) :=
          mul_le_mul_of_nonneg_left he (by nlinarith)
      _ = (c.δ + c.ε * c.h) / (1 - c.μ * c.h) := by ring_nf
      _ ≤ c.B := hBq
  have hsq := pow_le_pow_left₀ hpos hle 2
  unfold AtEnd V
  simp only [add_sub_cancel_left, ← qeval_cast] at e hsq
  exact e.trans hsq

/-- The squared weighted norm of a rational vector, over ℚ. -/
def Vq (w1 w2 a b c : ℚ) : ℚ := w1 * a ^ 2 + w2 * b ^ 2 + c ^ 2

/-- Consecutive cells meet with the same weights, and the end ball of `c` lies in the input
ball of `d` (Minkowski with s = d.δ − c.B). -/
def linkOK (c d : Cell) : Bool :=
  decide (c.t0 + c.h = d.t0 ∧ c.w1 = d.w1 ∧ c.w2 = d.w2 ∧ 0 < c.w1 ∧ 0 < c.w2 ∧ 0 ≤ c.B ∧
    0 ≤ d.δ - c.B ∧
    Vq c.w1 c.w2 (qeval c.pg c.h - d.pg.headD 0) (qeval c.pp c.h - d.pp.headD 0)
      (qeval c.pq c.h - d.pq.headD 0) ≤ (d.δ - c.B) ^ 2)

/-- A chain of cells inside [0, T] whose last cell satisfies `term`. -/
def chainTo (T : ℚ) (term : Cell → Bool) : List Cell → Bool
  | [] => false
  | [c] => cellOK T c && term c
  | c :: d :: l => cellOK T c && linkOK c d && chainTo T term (d :: l)

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

/-- A chain from its Boolean check: some last cell `e` satisfies `term`, and every solution
entering the first cell's ball is enclosed at `e`'s end. -/
theorem chain_gen {T : ℚ} {term : Cell → Bool} :
    ∀ (l : List Cell) (c : Cell), chainTo T term (c :: l) = true →
    ∀ {g p q : ℝ → ℝ}, Sol T c.t0 g p q → InBox c g p q →
    ∃ e : Cell, term e = true ∧ AtEnd e g p q := by
  intro l
  induction l with
  | nil =>
    intro c hok g p q hs h0
    simp only [chainTo, Bool.and_eq_true] at hok
    exact ⟨c, hok.2, cell_w c hok.1 hs h0⟩
  | cons d l ih =>
    intro c hok g p q hs h0
    simp only [chainTo, Bool.and_eq_true] at hok
    obtain ⟨⟨k1, kl⟩, krest⟩ := hok
    have he := cell_w c k1 hs h0
    obtain ⟨hdt, hbox⟩ := link_box kl he
    have hh : (0 : ℝ) < c.h := by exact_mod_cast (cellOK_basic c k1).2.2
    exact ih d krest (hs.mono (by rw [hdt]; linarith)) hbox

/-- A segment ending in the input ball of `d`. -/
theorem seg_q {T : ℚ} (d : Cell) (l : List Cell) (c : Cell)
    (hok : chainTo T (fun e => linkOK e d) (c :: l) = true) {g p q : ℝ → ℝ}
    (hs : Sol T c.t0 g p q) (h0 : InBox c g p q) : InBox d g p q := by
  obtain ⟨e, he, hend⟩ := chain_gen l c hok hs h0
  exact (link_box he hend).2

/-- Terminal condition: the last cell ends at `T`, and its end ball lies in the box of radius
`r` around (fg, fp, fq) (component bounds `r1` and `r2` of the ball). -/
def endOK (T fg fp fq r r2 : ℚ) (c : Cell) : Bool :=
  decide (c.t0 + c.h = T ∧ 0 < c.w1 ∧ 0 < c.w2 ∧ 0 ≤ c.B ∧ 0 ≤ r2 ∧ c.B ^ 2 ≤ c.w2 * r2 ^ 2 ∧
    0 ≤ c.r1 ∧ c.B ^ 2 ≤ c.w1 * c.r1 ^ 2 ∧
    |qeval c.pg c.h - fg| + c.r1 ≤ r ∧ |qeval c.pp c.h - fp| + r2 ≤ r ∧ |qeval c.pq c.h - fq| + c.B ≤ r)

theorem abs_link {x v w B r : ℝ} (h1 : |x - v| ≤ B) (h2 : |v - w| + B ≤ r) : |x - w| ≤ r := by
  have := abs_sub_le x v w
  linarith

/-- A final segment: every solution entering the first cell's ball is within `r` of
(fg, fp, fq) at `T`. -/
theorem end_q {T fg fp fq r r2 : ℚ} (l : List Cell) (c : Cell)
    (hok : chainTo T (endOK T fg fp fq r r2) (c :: l) = true) {g p q : ℝ → ℝ}
    (hs : Sol T c.t0 g p q) (h0 : InBox c g p q) :
    |g T - fg| ≤ r ∧ |p T - fp| ≤ r ∧ |q T - fq| ≤ r := by
  obtain ⟨e, het, hend⟩ := chain_gen l c hok hs h0
  obtain ⟨kT, kw1, kw2, kB, kr2, kBr2, kr1, kBr1, k1, k2, k3⟩ := of_decide_eq_true het
  have hT : ((e.t0 + e.h : ℚ) : ℝ) = (T : ℝ) := by exact_mod_cast kT
  push_cast at hT
  have hw1 : (0 : ℝ) < e.w1 := by exact_mod_cast kw1
  have hw2 : (0 : ℝ) < e.w2 := by exact_mod_cast kw2
  have hB : (0 : ℝ) ≤ e.B := by exact_mod_cast kB
  have hr1 : (0 : ℝ) ≤ e.r1 := by exact_mod_cast kr1
  have hr2 : (0 : ℝ) ≤ r2 := by exact_mod_cast kr2
  have hBr1 : (e.B : ℝ) ^ 2 ≤ e.w1 * (e.r1 : ℝ) ^ 2 := by exact_mod_cast kBr1
  have hBr2 : (e.B : ℝ) ^ 2 ≤ e.w2 * (r2 : ℝ) ^ 2 := by exact_mod_cast kBr2
  have k1' : |((qeval e.pg e.h : ℚ) : ℝ) - fg| + e.r1 ≤ r := by exact_mod_cast k1
  have k2' : |((qeval e.pp e.h : ℚ) : ℝ) - fp| + r2 ≤ r := by exact_mod_cast k2
  have k3' : |((qeval e.pq e.h : ℚ) : ℝ) - fq| + e.B ≤ r := by exact_mod_cast k3
  unfold AtEnd V at hend; rw [hT] at hend
  set a1 := g (T : ℝ) - ((qeval e.pg e.h : ℚ) : ℝ)
  set a2 := p (T : ℝ) - ((qeval e.pp e.h : ℚ) : ℝ)
  set a3 := q (T : ℝ) - ((qeval e.pq e.h : ℚ) : ℝ)
  have s1 := mul_nonneg hw1.le (sq_nonneg a1)
  have s2 := mul_nonneg hw2.le (sq_nonneg a2)
  have s3 := sq_nonneg a3
  have b1 : |a1| ≤ e.r1 := comp_le hw1 hr1 (by linarith) hBr1
  have b2 : |a2| ≤ r2 := comp_le hw2 hr2 (by linarith) hBr2
  have b3 : |a3| ≤ e.B := comp_le (w := 1) (B := (e.B : ℝ)) one_pos hB (by linarith) (by linarith)
  exact ⟨abs_link b1 k1', abs_link b2 k2', abs_link b3 k3'⟩

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
theorem end_q0 {T fg fp fq r r2 : ℚ} (l : List Cell) (c : Cell)
    (hok : chainTo T (endOK T fg fp fq r r2) (c :: l) = true) {g p q : ℝ → ℝ}
    (hs : Sol T 0 g p q) (h0 : InBox c g p q) :
    |g T - fg| ≤ r ∧ |p T - fp| ≤ r ∧ |q T - fq| ≤ r := by
  have k := (cellOK_basic c (chainTo_head c l hok)).1
  exact end_q l c hok (hs.mono (by exact_mod_cast k)) h0

end Work.Blasius.BCellW
