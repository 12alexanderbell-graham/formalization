import Mathlib

/-!
# One-sided cell step with a contracting bound (μ ≤ 0)

`Work.Sim.OneSided.onesided_cell` assumes μ ≥ 0 and bounds the error by (δ + ε s)·e^{μ s}. On a
stiff system's slow manifold, a sheared weight gives μ < 0 (Robertson: μ ≈ −2/t,
`runs/2026-11-06T0628Z/scripts/rob_feas_matrix.py`); then the bound δ·e^{μ s} + ε·s holds
(R′ = μδe^{μs} + ε ≥ μR + ε because ε s ≥ 0 and μ ≤ 0), so the initial error contracts.
-/

namespace Work.Sim.OneSidedNeg

theorem onesided_cell_neg {P Q : ℝ → ℝ → ℝ} {f2 f3 g2 g3 G2 G3 : ℝ → ℝ} {a b w μ ε δ B : ℝ}
    (hab : a ≤ b) (hw : 0 < w) (hμ : μ ≤ 0) (hε : 0 < ε) (hδ : 0 < δ)
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
    (hB : δ + ε * (b - a) ≤ B) :
    ∀ t ∈ Set.Icc a b, w * (f2 t - g2 t) ^ 2 + (f3 t - g3 t) ^ 2
      ≤ (δ * Real.exp (μ * (t - a)) + ε * (t - a)) ^ 2 := by
  set R : ℝ → ℝ := fun t => δ * Real.exp (μ * (t - a)) + ε * (t - a) with hRdef
  set φ : ℝ → ℝ := fun t => w * (f2 t - g2 t) ^ 2 + (f3 t - g3 t) ^ 2 with hφdef
  -- derivative of R
  have hRd : ∀ t, HasDerivAt R (μ * (δ * Real.exp (μ * (t - a))) + ε) t := by
    intro t
    have h2 : HasDerivAt (fun t => Real.exp (μ * (t - a))) (Real.exp (μ * (t - a)) * μ) t := by
      have := (((hasDerivAt_id t).sub_const a).const_mul μ).exp
      simpa using this
    have h1 : HasDerivAt (fun t => ε * (t - a)) ε t := by
      have := ((hasDerivAt_id t).sub_const a).const_mul ε
      simpa using this
    have := (h2.const_mul δ).add h1
    convert this using 1
    ring
  have hR2d : ∀ t, HasDerivAt (fun t => R t ^ 2)
      (2 * R t * (μ * (δ * Real.exp (μ * (t - a))) + ε)) t := by
    intro t
    have := (hRd t).pow 2
    convert this using 1
    norm_num
  have hRcont : Continuous R := by
    simp only [hRdef]; fun_prop
  -- bounds on R
  have hRge : ∀ t, a ≤ t → δ * Real.exp (μ * (t - a)) ≤ R t := by
    intro t ht
    simp only [hRdef]
    nlinarith
  have hRpos : ∀ t, a ≤ t → 0 < R t := fun t ht =>
    lt_of_lt_of_le (mul_pos hδ (Real.exp_pos _)) (hRge t ht)
  have hRle : ∀ t, t ≤ b → a ≤ t → R t ≤ B := by
    intro t htb hta
    refine le_trans ?_ hB
    simp only [hRdef]
    have he : Real.exp (μ * (t - a)) ≤ 1 := Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hμ (by linarith))
    have h1 : δ * Real.exp (μ * (t - a)) ≤ δ := by nlinarith
    have h2 : ε * (t - a) ≤ ε * (b - a) := by nlinarith
    linarith
  have key := image_le_of_deriv_right_lt_deriv_boundary' (f := φ)
    (f' := fun t => w * (2 * (f2 t - g2 t) * (P (f2 t) (f3 t) - G2 t))
      + 2 * (f3 t - g3 t) * (Q (f2 t) (f3 t) - G3 t))
    (B := fun t => R t ^ 2)
    (B' := fun t => 2 * R t * (μ * (δ * Real.exp (μ * (t - a))) + ε))
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
      have hRt := hRge t ht.1
      have hRpos : 0 < R t := hRpos t ht.1
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
      have hsplit : w * (2 * e2 * (P (f2 t) (f3 t) - G2 t)) + 2 * e3 * (Q (f2 t) (f3 t) - G3 t)
          = 2 * (w * (P (f2 t) (f3 t) - P (g2 t) (g3 t)) * e2
              + (Q (f2 t) (f3 t) - Q (g2 t) (g3 t)) * e3) - 2 * (w * e2 * D2 + e3 * D3) := by
        simp only [D2, D3]; ring
      rw [hsplit]
      have hμle : μ * R t ≤ μ * (δ * Real.exp (μ * (t - a))) :=
        mul_le_mul_of_nonpos_left hRt hμ
      have hμR2 : μ * R t ^ 2 ≤ R t * (μ * (δ * Real.exp (μ * (t - a)))) := by
        have := mul_le_mul_of_nonneg_left hμle hRpos.le
        nlinarith
      have hμR : μ * (w * e2 ^ 2 + e3 ^ 2) = μ * R t ^ 2 := by rw [heq]
      have habs := (abs_lt.1 hab').1
      linarith)
  intro t ht
  exact key ht

#print axioms Work.Sim.OneSidedNeg.onesided_cell_neg

end Work.Sim.OneSidedNeg
