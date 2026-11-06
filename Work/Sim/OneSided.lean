import Mathlib

/-!
# Logarithmic-norm (one-sided Lipschitz) cell step for stiff systems

THE RESULT part 1 ("rigorous simulators"). The Grönwall cell step of `Work/Sim/Validated.lean`
lets the enclosure grow with the full Lipschitz constant of the field, which is useless for stiff
systems. Here the error between a true solution `(f2, f3)` and an approximation `(g2, g3)` is
measured in the weighted norm `w·e₂² + e₃²`, and it grows only with a one-sided bound `μ` of the
field (the logarithmic norm in that weighted norm) on the ball of radius `B` around the
approximation, plus the defect `ε` of the approximation. Confinement to that ball comes from the
bound itself (the bound stays below `B` on the whole cell).

`rob_onesided` gives that one-sided bound for the reduced Robertson network (the first two rate
expressions after eliminating the first species by conservation), in terms of a lower bound for
the stiff diagonal rate and an upper bound for the coupling coefficient at the centre point.
-/

namespace Work.Sim.OneSided
open Set

/-- Generic 2-D cell step in the weighted norm `w·e₂² + e₃²` with a one-sided (logarithmic-norm)
bound `μ` on the ball of radius `B` around the approximation. -/
theorem onesided_cell {P Q : ℝ → ℝ → ℝ} {f2 f3 g2 g3 G2 G3 : ℝ → ℝ} {a b w μ ε δ B : ℝ}
    (hab : a ≤ b) (hw : 0 < w) (hμ : 0 ≤ μ) (hε : 0 < ε) (hδ : 0 < δ)
    (hf2 : ContinuousOn f2 (Set.Icc a b)) (hf3 : ContinuousOn f3 (Set.Icc a b))
    (hg2 : ContinuousOn g2 (Set.Icc a b)) (hg3 : ContinuousOn g3 (Set.Icc a b))
    (hf2' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt f2 (P (f2 t) (f3 t)) (Set.Ici t) t)
    (hf3' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt f3 (Q (f2 t) (f3 t)) (Set.Ici t) t)
    (hg2' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt g2 (G2 t) (Set.Ici t) t)
    (hg3' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt g3 (G3 t) (Set.Ici t) t)
    (hdef : ∀ t ∈ Set.Ico a b,
      w * (G2 t - P (g2 t) (g3 t)) ^ 2 + (G3 t - Q (g2 t) (g3 t)) ^ 2 < ε ^ 2)
    (hos : ∀ t ∈ Set.Ico a b, ∀ y2 y3 : ℝ, w * (y2 - g2 t) ^ 2 + (y3 - g3 t) ^ 2 ≤ B ^ 2 →
      w * (P y2 y3 - P (g2 t) (g3 t)) * (y2 - g2 t) + (Q y2 y3 - Q (g2 t) (g3 t)) * (y3 - g3 t)
        ≤ μ * (w * (y2 - g2 t) ^ 2 + (y3 - g3 t) ^ 2))
    (h0 : w * (f2 a - g2 a) ^ 2 + (f3 a - g3 a) ^ 2 ≤ δ ^ 2)
    (hB : (δ + ε * (b - a)) * Real.exp (μ * (b - a)) ≤ B) :
    ∀ t ∈ Set.Icc a b, w * (f2 t - g2 t) ^ 2 + (f3 t - g3 t) ^ 2
      ≤ ((δ + ε * (t - a)) * Real.exp (μ * (t - a))) ^ 2 := by
  set R : ℝ → ℝ := fun t => (δ + ε * (t - a)) * Real.exp (μ * (t - a)) with hRdef
  set φ : ℝ → ℝ := fun t => w * (f2 t - g2 t) ^ 2 + (f3 t - g3 t) ^ 2 with hφdef
  -- derivative of R
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
  -- bounds on R
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
    (f' := fun t => w * (2 * (f2 t - g2 t) * (P (f2 t) (f3 t) - G2 t))
      + 2 * (f3 t - g3 t) * (Q (f2 t) (f3 t) - G3 t))
    (B := fun t => R t ^ 2)
    (B' := fun t => 2 * R t * (ε * Real.exp (μ * (t - a)) + μ * R t))
    (by simp only [hφdef]; fun_prop)
    (by
      intro t ht
      have e2 := ((hf2' t ht).sub (hg2' t ht)).pow 2
      have e3 := ((hf3' t ht).sub (hg3' t ht)).pow 2
      have := (e2.const_mul w).add e3
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
      set e2 := f2 t - g2 t
      set e3 := f3 t - g3 t
      set D2 := G2 t - P (g2 t) (g3 t)
      set D3 := G3 t - Q (g2 t) (g3 t)
      have hRt : δ ≤ R t := hRge t ht.1
      have hRpos : 0 < R t := lt_of_lt_of_le hδ hRt
      have hRB : R t ≤ B := hRle t ht.2.le ht.1
      have hball : w * (f2 t - g2 t) ^ 2 + (f3 t - g3 t) ^ 2 ≤ B ^ 2 := by
        rw [heq]
        exact pow_le_pow_left₀ hRpos.le hRB 2
      have hos' := hos t ht (f2 t) (f3 t) hball
      have hD := hdef t ht
      -- Cauchy–Schwarz in the weighted norm
      have hcs : (w * e2 * D2 + e3 * D3) ^ 2 < (R t * ε) ^ 2 := by
        have hX : w * e2 ^ 2 + e3 ^ 2 = R t ^ 2 := heq
        have hid : (w * e2 ^ 2 + e3 ^ 2) * (w * D2 ^ 2 + D3 ^ 2) - (w * e2 * D2 + e3 * D3) ^ 2
            = w * (e2 * D3 - e3 * D2) ^ 2 := by ring
        have hnn : 0 ≤ w * (e2 * D3 - e3 * D2) ^ 2 := mul_nonneg hw.le (sq_nonneg _)
        have hR2 : 0 < R t ^ 2 := by positivity
        have : R t ^ 2 * (w * D2 ^ 2 + D3 ^ 2) < R t ^ 2 * ε ^ 2 :=
          mul_lt_mul_of_pos_left hD hR2
        rw [hX] at hid
        rw [mul_pow]
        linarith
      have hab' := abs_lt_of_sq_lt_sq hcs (by positivity)
      have hc := neg_abs_le (w * e2 * D2 + e3 * D3)
      have hexp : 1 ≤ Real.exp (μ * (t - a)) := Real.one_le_exp (mul_nonneg hμ (by linarith [ht.1]))
      have hsplit : w * (2 * e2 * (P (f2 t) (f3 t) - G2 t)) + 2 * e3 * (Q (f2 t) (f3 t) - G3 t)
          = 2 * (w * (P (f2 t) (f3 t) - P (g2 t) (g3 t)) * e2
              + (Q (f2 t) (f3 t) - Q (g2 t) (g3 t)) * e3) - 2 * (w * e2 * D2 + e3 * D3) := by
        simp only [D2, D3]; ring
      rw [hsplit]
      have hε' : R t * ε ≤ R t * (ε * Real.exp (μ * (t - a))) := by
        apply mul_le_mul_of_nonneg_left _ hRpos.le
        exact le_mul_of_one_le_right hε.le hexp
      have hμR : μ * (w * e2 ^ 2 + e3 ^ 2) = μ * R t ^ 2 := by rw [heq]
      have habs := (abs_lt.1 hab').1
      linarith)
  intro t ht
  exact key ht

/-- `|h₂| ≤ s B` and `|h₃| ≤ B` on the weighted ball. -/
lemma ball_bounds {w s B h2 h3 : ℝ} (hw : 0 < w) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hsw : 1 ≤ s ^ 2 * w) (hh : w * h2 ^ 2 + h3 ^ 2 ≤ B ^ 2) :
    |h2| ≤ s * B ∧ |h3| ≤ B := by
  constructor
  · apply abs_le_of_sq_le_sq _ (mul_nonneg hs hB)
    have h1 : 0 ≤ h2 ^ 2 * (s ^ 2 * w - 1) := mul_nonneg (sq_nonneg _) (by linarith)
    have h2' : 0 ≤ s ^ 2 * (B ^ 2 - w * h2 ^ 2) :=
      mul_nonneg (sq_nonneg _) (by nlinarith [sq_nonneg h3])
    nlinarith
  · apply abs_le_of_sq_le_sq _ hB
    nlinarith [mul_nonneg hw.le (sq_nonneg h2)]

/-- Algebraic core of the Robertson one-sided bound, over atoms. -/
lemma rob_core {w μ A A' C Cm K0 h2 h3 cub : ℝ} (hw : 0 < w) (hμ : 0 < μ)
    (hA : A ≤ A') (hcub : cub ≤ K0) (hC : |C| ≤ Cm)
    (hcond : Cm ^ 2 ≤ 4 * μ * (w * A - K0 + w * μ)) :
    -(w * A') * h2 ^ 2 + C * (h2 * h3) + h2 ^ 2 * cub ≤ μ * (w * h2 ^ 2 + h3 ^ 2) := by
  have hcubm : h2 ^ 2 * cub ≤ h2 ^ 2 * K0 := mul_le_mul_of_nonneg_left hcub (sq_nonneg _)
  have hdiag : w * A * h2 ^ 2 ≤ w * A' * h2 ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hw.le) (sq_nonneg _)
  have e1 : C * (h2 * h3) ≤ Cm * (|h2| * |h3|) := by
    calc C * (h2 * h3) ≤ |C * (h2 * h3)| := le_abs_self _
      _ = |C| * (|h2| * |h3|) := by rw [abs_mul, abs_mul]
      _ ≤ Cm * (|h2| * |h3|) :=
        mul_le_mul_of_nonneg_right hC (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have e2 : 0 ≤ (Cm * |h2| - 2 * μ * |h3|) ^ 2 := sq_nonneg _
  have e3 : |h2| ^ 2 = h2 ^ 2 := sq_abs h2
  have e4 : |h3| ^ 2 = h3 ^ 2 := sq_abs h3
  have hcross : 4 * μ * (C * (h2 * h3)) ≤ Cm ^ 2 * h2 ^ 2 + 4 * μ ^ 2 * h3 ^ 2 := by
    have h4 : 4 * μ * (C * (h2 * h3)) ≤ 4 * μ * (Cm * (|h2| * |h3|)) :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    have : (Cm * |h2| - 2 * μ * |h3|) ^ 2
        = Cm ^ 2 * |h2| ^ 2 + 4 * μ ^ 2 * |h3| ^ 2 - 4 * μ * (Cm * (|h2| * |h3|)) := by ring
    rw [e3, e4] at this
    linarith
  have hc2 : Cm ^ 2 * h2 ^ 2 ≤ 4 * μ * (w * A - K0 + w * μ) * h2 ^ 2 :=
    mul_le_mul_of_nonneg_right hcond (sq_nonneg _)
  have h4 : 0 < 4 * μ := by positivity
  have m1 : 4 * μ * (h2 ^ 2 * cub) ≤ 4 * μ * (h2 ^ 2 * K0) := mul_le_mul_of_nonneg_left hcubm h4.le
  have m2 : 4 * μ * (w * A * h2 ^ 2) ≤ 4 * μ * (w * A' * h2 ^ 2) :=
    mul_le_mul_of_nonneg_left hdiag h4.le
  have : 4 * μ * (-(w * A') * h2 ^ 2 + C * (h2 * h3) + h2 ^ 2 * cub)
      ≤ 4 * μ * (μ * (w * h2 ^ 2 + h3 ^ 2)) := by
    linarith
  exact le_of_mul_le_mul_left this h4

/-- One-sided bound for the reduced Robertson field in the weighted norm `w·h₂² + h₃²`. -/
theorem rob_onesided {w s μ B A Cm x2 x3 h2 h3 : ℝ} (hw : 0 < w) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hsw : 1 ≤ s ^ 2 * w) (hμ : 0 < μ)
    (hA : A ≤ 1 / 25 + 10000 * x3 + 2 * 30000000 * x2)
    (hC : |-(w * (1 / 25)) - w * 10000 * x2 + 2 * 30000000 * x2| ≤ Cm)
    (hcond : Cm ^ 2 ≤ 4 * μ * (w * A - ((w * 10000 + 30000000) + w * 30000000 * s) * B + w * μ))
    (hh : w * h2 ^ 2 + h3 ^ 2 ≤ B ^ 2) :
    w * (((1/25) * (1 - (x2 + h2) - (x3 + h3)) - 10000 * (x2 + h2) * (x3 + h3) - 30000000 * (x2 + h2) ^ 2)
          - ((1/25) * (1 - x2 - x3) - 10000 * x2 * x3 - 30000000 * x2 ^ 2)) * h2
      + (30000000 * (x2 + h2) ^ 2 - 30000000 * x2 ^ 2) * h3
      ≤ μ * (w * h2 ^ 2 + h3 ^ 2) := by
  obtain ⟨hb2, hb3⟩ := ball_bounds hw hB hs hsw hh
  have hexp : w * (((1/25) * (1 - (x2 + h2) - (x3 + h3)) - 10000 * (x2 + h2) * (x3 + h3)
        - 30000000 * (x2 + h2) ^ 2)
          - ((1/25) * (1 - x2 - x3) - 10000 * x2 * x3 - 30000000 * x2 ^ 2)) * h2
      + (30000000 * (x2 + h2) ^ 2 - 30000000 * x2 ^ 2) * h3
      = -(w * (1 / 25 + 10000 * x3 + 2 * 30000000 * x2)) * h2 ^ 2
        + (-(w * (1 / 25)) - w * 10000 * x2 + 2 * 30000000 * x2) * (h2 * h3)
        + h2 ^ 2 * (-(w * 10000) * h3 - w * 30000000 * h2 + 30000000 * h3) := by
    ring
  rw [hexp]
  have hcub : -(w * 10000) * h3 - w * 30000000 * h2 + 30000000 * h3
      ≤ ((w * 10000 + 30000000) + w * 30000000 * s) * B := by
    have a1 : -h3 ≤ B := by linarith [neg_abs_le h3]
    have a2 : h3 ≤ B := le_trans (le_abs_self h3) hb3
    have a3 : -h2 ≤ s * B := by linarith [neg_abs_le h2]
    have t1 : w * 10000 * (-h3) ≤ w * 10000 * B :=
      mul_le_mul_of_nonneg_left a1 (by positivity)
    have t2 : w * 30000000 * (-h2) ≤ w * 30000000 * (s * B) :=
      mul_le_mul_of_nonneg_left a3 (by positivity)
    linarith
  exact rob_core hw hμ hA hcub hC hcond

end Work.Sim.OneSided
