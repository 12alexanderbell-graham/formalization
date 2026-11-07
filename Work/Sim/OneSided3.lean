import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Bound

/-!
# Logarithmic-norm (one-sided Lipschitz) cell step, three components

The three-component version of `Checked.Sim.OneSided.onesided_cell`: the error between a true
solution `(f1, f2, f3)` and an approximation `(g1, g2, g3)` is measured in the weighted norm
`w1·e₁² + w2·e₂² + e₃²` and grows only with a one-sided bound `μ` of the field on the ball of
radius `B` around the approximation, plus the defect `ε`. Also: a Sylvester (LDL) criterion for a
symmetric 3×3 quadratic form, and the triangle inequality for the weighted norm.
-/

namespace Work.Sim.OneSided3
open Set

/-- Generic 3-D cell step in the weighted norm `w1·e₁² + w2·e₂² + e₃²` with a one-sided bound `μ`
on the ball of radius `B` around the approximation. -/
theorem onesided3_cell {F1 F2 F3 : ℝ → ℝ → ℝ → ℝ} {f1 f2 f3 g1 g2 g3 G1 G2 G3 : ℝ → ℝ}
    {a b w1 w2 μ ε δ B : ℝ}
    (hab : a ≤ b) (hw1 : 0 < w1) (hw2 : 0 < w2) (hμ : 0 ≤ μ) (hε : 0 < ε) (hδ : 0 < δ)
    (hf1 : ContinuousOn f1 (Set.Icc a b)) (hf2 : ContinuousOn f2 (Set.Icc a b)) (hf3 : ContinuousOn f3 (Set.Icc a b))
    (hg1 : ContinuousOn g1 (Set.Icc a b)) (hg2 : ContinuousOn g2 (Set.Icc a b)) (hg3 : ContinuousOn g3 (Set.Icc a b))
    (hf1' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt f1 (F1 (f1 t) (f2 t) (f3 t)) (Set.Ici t) t)
    (hf2' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt f2 (F2 (f1 t) (f2 t) (f3 t)) (Set.Ici t) t)
    (hf3' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt f3 (F3 (f1 t) (f2 t) (f3 t)) (Set.Ici t) t)
    (hg1' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt g1 (G1 t) (Set.Ici t) t)
    (hg2' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt g2 (G2 t) (Set.Ici t) t)
    (hg3' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt g3 (G3 t) (Set.Ici t) t)
    (hdef : ∀ t ∈ Set.Ico a b,
      w1 * (G1 t - F1 (g1 t) (g2 t) (g3 t)) ^ 2 + w2 * (G2 t - F2 (g1 t) (g2 t) (g3 t)) ^ 2
        + (G3 t - F3 (g1 t) (g2 t) (g3 t)) ^ 2 < ε ^ 2)
    (hos : ∀ t ∈ Set.Ico a b, ∀ y1 y2 y3 : ℝ,
      w1 * (y1 - g1 t) ^ 2 + w2 * (y2 - g2 t) ^ 2 + (y3 - g3 t) ^ 2 ≤ B ^ 2 →
      w1 * (F1 y1 y2 y3 - F1 (g1 t) (g2 t) (g3 t)) * (y1 - g1 t)
        + w2 * (F2 y1 y2 y3 - F2 (g1 t) (g2 t) (g3 t)) * (y2 - g2 t)
        + (F3 y1 y2 y3 - F3 (g1 t) (g2 t) (g3 t)) * (y3 - g3 t)
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
    (f' := fun t => w1 * (2 * (f1 t - g1 t) * (F1 (f1 t) (f2 t) (f3 t) - G1 t))
      + w2 * (2 * (f2 t - g2 t) * (F2 (f1 t) (f2 t) (f3 t) - G2 t))
      + 2 * (f3 t - g3 t) * (F3 (f1 t) (f2 t) (f3 t) - G3 t))
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
      set D1 := G1 t - F1 (g1 t) (g2 t) (g3 t)
      set D2 := G2 t - F2 (g1 t) (g2 t) (g3 t)
      set D3 := G3 t - F3 (g1 t) (g2 t) (g3 t)
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
      have hsplit : w1 * (2 * e1 * (F1 (f1 t) (f2 t) (f3 t) - G1 t))
          + w2 * (2 * e2 * (F2 (f1 t) (f2 t) (f3 t) - G2 t))
          + 2 * e3 * (F3 (f1 t) (f2 t) (f3 t) - G3 t)
          = 2 * (w1 * (F1 (f1 t) (f2 t) (f3 t) - F1 (g1 t) (g2 t) (g3 t)) * e1
              + w2 * (F2 (f1 t) (f2 t) (f3 t) - F2 (g1 t) (g2 t) (g3 t)) * e2
              + (F3 (f1 t) (f2 t) (f3 t) - F3 (g1 t) (g2 t) (g3 t)) * e3)
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

/-- Sylvester (LDL) criterion: a symmetric 3×3 form with positive leading minors of order 1, 2 and
nonnegative determinant is nonnegative. -/
theorem quad3_nonneg {m11 m12 m13 m22 m23 m33 : ℝ} (h1 : 0 < m11) (h2 : 0 < m11 * m22 - m12 ^ 2)
    (h3 : 0 ≤ m11 * (m22 * m33 - m23 ^ 2) - m12 * (m12 * m33 - m23 * m13) + m13 * (m12 * m23 - m22 * m13))
    (x y z : ℝ) :
    0 ≤ m11 * x ^ 2 + m22 * y ^ 2 + m33 * z ^ 2 + 2 * m12 * x * y + 2 * m13 * x * z + 2 * m23 * y * z := by
  set d2 := m11 * m22 - m12 ^ 2 with hd2
  set d3 := m11 * (m22 * m33 - m23 ^ 2) - m12 * (m12 * m33 - m23 * m13)
    + m13 * (m12 * m23 - m22 * m13) with hd3
  set Q := m11 * x ^ 2 + m22 * y ^ 2 + m33 * z ^ 2 + 2 * m12 * x * y + 2 * m13 * x * z
    + 2 * m23 * y * z with hQ
  have hid : m11 * d2 * Q = d2 * (m11 * x + m12 * y + m13 * z) ^ 2
      + (d2 * y + (m11 * m23 - m12 * m13) * z) ^ 2 + m11 * d3 * z ^ 2 := by
    simp only [hd2, hd3, hQ]; ring
  have hpos : 0 < m11 * d2 := mul_pos h1 h2
  have hrhs : 0 ≤ d2 * (m11 * x + m12 * y + m13 * z) ^ 2
      + (d2 * y + (m11 * m23 - m12 * m13) * z) ^ 2 + m11 * d3 * z ^ 2 := by
    have := mul_nonneg h1.le h3
    positivity
  rw [← hid] at hrhs
  exact (mul_nonneg_iff_of_pos_left hpos).1 hrhs

/-- Triangle inequality for the weighted norm `w1·e₁² + w2·e₂² + e₃²`. -/
theorem wnorm_add {w1 w2 B s e1 e2 e3 r1 r2 r3 : ℝ} (hw1 : 0 < w1) (hw2 : 0 < w2) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (he : w1 * e1 ^ 2 + w2 * e2 ^ 2 + e3 ^ 2 ≤ B ^ 2) (hr : w1 * r1 ^ 2 + w2 * r2 ^ 2 + r3 ^ 2 ≤ s ^ 2) :
    w1 * (e1 + r1) ^ 2 + w2 * (e2 + r2) ^ 2 + (e3 + r3) ^ 2 ≤ (B + s) ^ 2 := by
  set X := w1 * e1 ^ 2 + w2 * e2 ^ 2 + e3 ^ 2
  set Y := w1 * r1 ^ 2 + w2 * r2 ^ 2 + r3 ^ 2
  set C := w1 * e1 * r1 + w2 * e2 * r2 + e3 * r3
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hcs : C ^ 2 ≤ X * Y := by
    have hid : X * Y - C ^ 2 = w1 * w2 * (e1 * r2 - e2 * r1) ^ 2 + w1 * (e1 * r3 - e3 * r1) ^ 2
        + w2 * (e2 * r3 - e3 * r2) ^ 2 := by ring
    have : 0 ≤ w1 * w2 * (e1 * r2 - e2 * r1) ^ 2 + w1 * (e1 * r3 - e3 * r1) ^ 2
        + w2 * (e2 * r3 - e3 * r2) ^ 2 := by positivity
    linarith
  have hXY : X * Y ≤ (B * s) ^ 2 := by
    rw [mul_pow]; exact mul_le_mul he hr hY0 (sq_nonneg _)
  have hC : C ≤ B * s := by
    have := abs_le_of_sq_le_sq' (hcs.trans hXY) (mul_nonneg hB hs)
    exact this.2
  have hexp : w1 * (e1 + r1) ^ 2 + w2 * (e2 + r2) ^ 2 + (e3 + r3) ^ 2 = X + Y + 2 * C := by ring
  rw [hexp]
  nlinarith

end Work.Sim.OneSided3
