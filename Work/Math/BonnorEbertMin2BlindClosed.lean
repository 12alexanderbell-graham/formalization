import Mathlib
import Work.Math.BonnorEbertMin2
import Work.Math.BonnorEbertMin2Blind

/-! Bonnor–Ebert sphere: the blind restatement `Work.Math.BonnorEbertMin2Blind.blind_bonnor_ebert_second_min`
(ψ of class C² on [0, ∞), ψ(0) = 0, ψ'(0) = 0 within [0, ∞), equation in the form (ξ² ψ')' = ξ² e^{−ψ} with ψ'
the two-sided `deriv`, mass (√(4π))⁻¹ e^{−ψ/2} ξ² ψ', contrast e^{ψ}, strict extrema over every radius
ξ ≥ 0, ≥ ξ₁, ≥ ξ₂, ≥ ξ₃) closed from the frozen headline `Work.Math.BonnorEbertMin2.bonnor_ebert_second_min`
with w = −ψ, φ = −ψ'. At ξ = 0 the two-sided `deriv ψ 0` is 0 whether or not ψ is differentiable there
(ψ'(0) = 0 within [0, ∞), or Lean's junk value), so φ agrees on [0, ∞) with minus the derivative within
[0, ∞), which is continuous. The headline is applied once with S = 20000 and once with S = max ξ 20000; the
extremisers agree because each is a strict extremiser on a set containing the other. Written by run
2026-11-14T1428Z, adapted from `Work/Math/BonnorEbertMax2BlindClosed.lean`. -/

namespace Work.Math.BonnorEbertMin2BlindClosed
open Set Filter Topology Work.Math.BonnorEbertMin2Blind

theorem blind_closed (ψ : ℝ → ℝ) (hψ : IsRegularIsothermalSolution ψ) :
    ∃ ξ₁ ξ₂ ξ₃ ξ₄ : ℝ,
      6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      733.5 ≤ ξ₃ ∧ ξ₃ ≤ 734 ∧
      7849.5 ≤ ξ₄ ∧ ξ₄ ≤ 7849.75 ∧
      (∀ ξ : ℝ, 0 ≤ ξ → ξ ≠ ξ₁ → beMass ψ ξ < beMass ψ ξ₁) ∧
      (∀ ξ : ℝ, ξ₁ ≤ ξ → ξ ≠ ξ₂ → beMass ψ ξ₂ < beMass ψ ξ) ∧
      (∀ ξ : ℝ, ξ₂ ≤ ξ → ξ ≠ ξ₃ → beMass ψ ξ < beMass ψ ξ₃) ∧
      (∀ ξ : ℝ, ξ₃ ≤ ξ → ξ ≠ ξ₄ → beMass ψ ξ₄ < beMass ψ ξ) ∧
      0.787992 ≤ beMass ψ ξ₄ ∧ beMass ψ ξ₄ ≤ 0.787995 ∧
      31193900 ≤ Real.exp (ψ ξ₄) ∧ Real.exp (ψ ξ₄) ≤ 31196100 := by
  obtain ⟨hsmooth, h0, h0', hode⟩ := hψ
  set dW : ℝ → ℝ := derivWithin ψ (Ici 0) with hdW
  have hU : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have hD : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt ψ (dW s) (Ici 0) s := fun s hs =>
    ((hsmooth.differentiableOn (by norm_num)) s hs).hasDerivWithinAt
  have hcont : ContinuousOn dW (Ici 0) := hsmooth.continuousOn_derivWithin hU (by norm_num)
  have hC1 : ContDiffOn ℝ 1 dW (Ici 0) := hsmooth.derivWithin hU (by norm_num)
  -- deriv ψ agrees with dW on [0, ∞)
  have hdW0 : dW 0 = 0 := (hU 0 (Set.mem_Ici.mpr le_rfl)).eq_deriv _ (hD 0 (Set.mem_Ici.mpr le_rfl)) h0'
  have hpos : ∀ s : ℝ, 0 < s → deriv ψ s = dW s := fun s hs =>
    (derivWithin_of_mem_nhds (Ici_mem_nhds hs)).symm
  have hzero : deriv ψ 0 = 0 := by
    by_cases hd : DifferentiableAt ℝ ψ 0
    · have h1 : HasDerivWithinAt ψ (deriv ψ 0) (Ici 0) 0 := hd.hasDerivAt.hasDerivWithinAt
      exact (hU 0 (Set.mem_Ici.mpr le_rfl)).eq_deriv _ h1 h0'
    · exact deriv_zero_of_not_differentiableAt hd
  have heq : ∀ s : ℝ, 0 ≤ s → deriv ψ s = dW s := by
    intro s hs
    rcases hs.lt_or_eq with h | h
    · exact hpos s h
    · subst h; rw [hzero, hdW0]
  have h2 : ∀ x : ℝ, 0 < x → HasDerivAt (deriv ψ) (Real.exp (-(ψ x)) - 2 / x * deriv ψ x) x := by
    intro x hx
    have hdiff : DifferentiableAt ℝ dW x :=
      ((hC1.differentiableOn (by norm_num)) x (le_of_lt hx)).differentiableAt (Ici_mem_nhds hx)
    have hev : deriv ψ =ᶠ[𝓝 x] dW := by
      filter_upwards [Ioi_mem_nhds hx] with y hy using hpos y hy
    have hdd : HasDerivAt (deriv ψ) (deriv dW x) x := hdiff.hasDerivAt.congr_of_eventuallyEq hev
    have hprod : HasDerivAt (fun y => y ^ 2 * deriv ψ y)
        (((2 : ℕ) : ℝ) * x ^ (2 - 1) * deriv ψ x + x ^ 2 * deriv dW x) x := (hasDerivAt_pow 2 x).mul hdd
    have e := (hode x hx).unique hprod
    have hx0 : x ≠ 0 := hx.ne'
    have key : deriv dW x = Real.exp (-(ψ x)) - 2 / x * deriv ψ x := by
      have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
      field_simp
      push_cast at e
      nlinarith [e]
    rw [← key]; exact hdd
  have hyp : ∀ S : ℝ, 20000 ≤ S →
      (∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt (fun x => -ψ x) (-deriv ψ s) (Icc 0 S) s) ∧
      ContinuousWithinAt (fun x => -deriv ψ x) (Icc 0 S) 0 ∧
      (∀ s ∈ Ioc (0 : ℝ) S, HasDerivWithinAt (fun x => -deriv ψ x)
        (-(2 / s * (fun x => -deriv ψ x) s) - Real.exp ((fun x => -ψ x) s)) (Icc 0 S) s) := by
    intro S _
    refine ⟨fun s hs => ?_, ?_, fun s hs => ?_⟩
    · rw [heq s hs.1]; exact ((hD s hs.1).mono Icc_subset_Ici_self).neg
    · have hc : ContinuousWithinAt (fun x => -dW x) (Icc 0 S) 0 :=
        ((hcont 0 (Set.mem_Ici.mpr le_rfl)).neg).mono Icc_subset_Ici_self
      refine hc.congr (fun y hy => by simp only [heq y hy.1]) (by simp only [heq 0 le_rfl])
    · exact ((h2 s hs.1).neg.congr_deriv (by ring)).hasDerivWithinAt
  have hz : (fun x => -ψ x) 0 = 0 := by simp [h0]
  have hm : ∀ s : ℝ, s ^ 2 * (-(fun x => -deriv ψ x) s) * Real.exp ((fun x => -ψ x) s / 2) /
      Real.sqrt (4 * Real.pi) = beMass ψ s := by
    intro s
    simp only [beMass, neg_neg, neg_div]
    field_simp
  obtain ⟨A1, A2, A3⟩ := hyp 20000 le_rfl
  obtain ⟨ξ₁, ξ₂, ξ₃, ξ₄, a1, a2, a3, a4, a3', a4', a3'', a4'', a5, a6, a7, a7', a8, a9, a10, a11⟩ :=
    Work.Math.BonnorEbertMin2.bonnor_ebert_second_min 20000 le_rfl _ _ A1 A2 A3 hz
  have hξ0 : (0 : ℝ) ≤ ξ₁ := by linarith
  rw [hm ξ₄] at a8 a9
  simp only [neg_neg] at a10 a11
  have agree : ∀ ξ : ℝ, ∃ η₁ η₂ η₃ η₄ : ℝ, η₁ = ξ₁ ∧ η₂ = ξ₂ ∧ η₃ = ξ₃ ∧ η₄ = ξ₄ ∧
      (∀ s ∈ Icc (0 : ℝ) (max ξ 20000), s ≠ η₁ → beMass ψ s < beMass ψ η₁) ∧
      (∀ s ∈ Icc η₁ (max ξ 20000), s ≠ η₂ → beMass ψ η₂ < beMass ψ s) ∧
      (∀ s ∈ Icc η₂ (max ξ 20000), s ≠ η₃ → beMass ψ s < beMass ψ η₃) ∧
      (∀ s ∈ Icc η₃ (max ξ 20000), s ≠ η₄ → beMass ψ η₄ < beMass ψ s) := by
    intro ξ
    obtain ⟨B1, B2, B3⟩ := hyp (max ξ 20000) (le_max_right _ _)
    obtain ⟨η₁, η₂, η₃, η₄, b1, b2, b3, b4, b3', b4', b3'', b4'', b5, b6, b7, b7', -, -, -, -⟩ :=
      Work.Math.BonnorEbertMin2.bonnor_ebert_second_min (max ξ 20000) (le_max_right _ _) _ _ B1 B2 B3 hz
    have hM : (20000 : ℝ) ≤ max ξ 20000 := le_max_right _ _
    have e1 : η₁ = ξ₁ := by
      by_contra hne'
      have l1 := a5 η₁ ⟨by linarith, by linarith⟩ hne'
      have l2 := b5 ξ₁ ⟨hξ0, by linarith⟩ (Ne.symm hne')
      linarith
    subst e1
    have e2 : η₂ = ξ₂ := by
      by_contra hne'
      have l1 := a6 η₂ ⟨by linarith, by linarith⟩ hne'
      have l2 := b6 ξ₂ ⟨by linarith, by linarith⟩ (Ne.symm hne')
      linarith
    subst e2
    have e3 : η₃ = ξ₃ := by
      by_contra hne'
      have l1 := a7 η₃ ⟨by linarith, by linarith⟩ hne'
      have l2 := b7 ξ₃ ⟨by linarith, by linarith⟩ (Ne.symm hne')
      linarith
    subst e3
    have e4 : η₄ = ξ₄ := by
      by_contra hne'
      have l1 := a7' η₄ ⟨by linarith, by linarith⟩ hne'
      have l2 := b7' ξ₄ ⟨by linarith, by linarith⟩ (Ne.symm hne')
      linarith
    subst e4
    refine ⟨η₁, η₂, η₃, η₄, rfl, rfl, rfl, rfl, fun s hs hne => ?_, fun s hs hne => ?_,
      fun s hs hne => ?_, fun s hs hne => ?_⟩
    · have := b5 s hs hne; rwa [hm s, hm η₁] at this
    · have := b6 s hs hne; rwa [hm s, hm η₂] at this
    · have := b7 s hs hne; rwa [hm s, hm η₃] at this
    · have := b7' s hs hne; rwa [hm s, hm η₄] at this
  refine ⟨ξ₁, ξ₂, ξ₃, ξ₄, a1, a2, a3, a4, a3', a4', a3'', a4'', ?_, ?_, ?_, ?_, a8, a9, a10, a11⟩
  · intro ξ hξ hne
    obtain ⟨η₁, η₂, η₃, η₄, rfl, rfl, rfl, rfl, c1, c2, c3, c4⟩ := agree ξ
    exact c1 ξ ⟨hξ, le_max_left _ _⟩ hne
  · intro ξ hξ hne
    obtain ⟨η₁, η₂, η₃, η₄, rfl, rfl, rfl, rfl, c1, c2, c3, c4⟩ := agree ξ
    exact c2 ξ ⟨hξ, le_max_left _ _⟩ hne
  · intro ξ hξ hne
    obtain ⟨η₁, η₂, η₃, η₄, rfl, rfl, rfl, rfl, c1, c2, c3, c4⟩ := agree ξ
    exact c3 ξ ⟨hξ, le_max_left _ _⟩ hne
  · intro ξ hξ hne
    obtain ⟨η₁, η₂, η₃, η₄, rfl, rfl, rfl, rfl, c1, c2, c3, c4⟩ := agree ξ
    exact c4 ξ ⟨hξ, le_max_left _ _⟩ hne

end Work.Math.BonnorEbertMin2BlindClosed

#print axioms Work.Math.BonnorEbertMin2BlindClosed.blind_closed
