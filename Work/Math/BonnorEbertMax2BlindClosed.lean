import Mathlib
import Work.Math.BonnorEbertMax2
import Work.Math.BonnorEbertMax2Blind

/-! Bonnor–Ebert sphere: the blind restatement `Work.Math.BonnorEbertMax2Blind.blind_bonnor_ebert_second_max`
(ψ of class C² on [0, ∞), ψ(0) = 0, ψ'(0) = 0 within [0, ∞), equation in the form (ξ² ψ')' = ξ² e^{−ψ} with ψ'
the derivative within [0, ∞), mass with the rpow (4π)^(−1/2), contrast e^{ψ}, strict maximum over every radius
ξ ≥ 0, strict minimum over every radius ξ ≥ ξ₁, strict maximum over every radius ξ ≥ ξ₂) closed from the frozen
headline `Work.Math.BonnorEbertMax2.bonnor_ebert_second_max` with w = −ψ, φ = −(derivative of ψ within
[0, ∞)). The headline is applied once with S = 2000 and once with S = max ξ 2000; the extremisers agree
because each is a strict extremiser on a set containing the other. Written by run 2026-11-14T1028Z, adapted
from `Work/Math/BonnorEbertMinBlindClosed.lean`. -/

namespace Work.Math.BonnorEbertMax2BlindClosed
open Set Filter Topology Work.Math.BonnorEbertMax2Blind

theorem blind_closed (ψ : ℝ → ℝ)
    (hsmooth : ContDiffOn ℝ 2 ψ (Ici 0))
    (h0 : ψ 0 = 0)
    (h0' : HasDerivWithinAt ψ 0 (Ici 0) 0)
    (hode : ∀ ξ : ℝ, 0 < ξ →
      deriv (fun x => x ^ 2 * derivWithin ψ (Ici 0) x) ξ = ξ ^ 2 * Real.exp (-(ψ ξ))) :
    ∃ ξ₁ ξ₂ ξ₃ : ℝ,
      6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      733.5 ≤ ξ₃ ∧ ξ₃ ≤ 734 ∧
      (∀ ξ : ℝ, 0 ≤ ξ → ξ ≠ ξ₁ → beMass ψ ξ < beMass ψ ξ₁) ∧
      (∀ ξ : ℝ, ξ₁ ≤ ξ → ξ ≠ ξ₂ → beMass ψ ξ₂ < beMass ψ ξ) ∧
      (∀ ξ : ℝ, ξ₂ ≤ ξ → ξ ≠ ξ₃ → beMass ψ ξ < beMass ψ ξ₃) ∧
      0.8306 ≤ beMass ψ ξ₃ ∧ beMass ψ ξ₃ ≤ 0.8308 ∧
      258300 ≤ Real.exp (ψ ξ₃) ∧ Real.exp (ψ ξ₃) ≤ 258800 := by
  set dψ : ℝ → ℝ := derivWithin ψ (Ici 0) with hdψ
  have hU : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have hD : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt ψ (dψ s) (Ici 0) s := fun s hs =>
    ((hsmooth.differentiableOn (by norm_num)) s hs).hasDerivWithinAt
  have hcont : ContinuousOn dψ (Ici 0) := hsmooth.continuousOn_derivWithin hU (by norm_num)
  have hC1 : ContDiffOn ℝ 1 dψ (Ici 0) := hsmooth.derivWithin hU (by norm_num)
  have h2 : ∀ x : ℝ, 0 < x → HasDerivAt dψ (Real.exp (-(ψ x)) - 2 / x * dψ x) x := by
    intro x hx
    have hdiff : DifferentiableAt ℝ dψ x :=
      ((hC1.differentiableOn (by norm_num)) x (le_of_lt hx)).differentiableAt (Ici_mem_nhds hx)
    have hprod : HasDerivAt (fun y => y ^ 2 * dψ y) _ x := (hasDerivAt_pow 2 x).mul hdiff.hasDerivAt
    have e := hode x hx
    rw [hprod.deriv] at e
    have hx0 : x ≠ 0 := hx.ne'
    have key : deriv dψ x = Real.exp (-(ψ x)) - 2 / x * dψ x := by
      have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
      field_simp
      push_cast at e
      nlinarith [e]
    rw [← key]; exact hdiff.hasDerivAt
  have hyp : ∀ S : ℝ, 2000 ≤ S →
      (∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt (fun x => -ψ x) (-dψ s) (Icc 0 S) s) ∧
      ContinuousWithinAt (fun x => -dψ x) (Icc 0 S) 0 ∧
      (∀ s ∈ Ioc (0 : ℝ) S, HasDerivWithinAt (fun x => -dψ x)
        (-(2 / s * (fun x => -dψ x) s) - Real.exp ((fun x => -ψ x) s)) (Icc 0 S) s) := by
    intro S _
    refine ⟨fun s hs => ((hD s hs.1).mono Icc_subset_Ici_self).neg,
      ((hcont 0 (Set.mem_Ici.mpr le_rfl)).neg).mono Icc_subset_Ici_self, fun s hs => ?_⟩
    exact ((h2 s hs.1).neg.congr_deriv (by ring)).hasDerivWithinAt
  have hz : (fun x => -ψ x) 0 = 0 := by simp [h0]
  have hm : ∀ s : ℝ, s ^ 2 * (-(fun x => -dψ x) s) * Real.exp ((fun x => -ψ x) s / 2) /
      Real.sqrt (4 * Real.pi) = beMass ψ s := by
    intro s
    simp only [beMass, neg_neg, neg_div]
    have hp : (0 : ℝ) ≤ 4 * Real.pi := by positivity
    rw [Real.rpow_neg hp, ← Real.sqrt_eq_rpow, hdψ]
    field_simp
  obtain ⟨A1, A2, A3⟩ := hyp 2000 le_rfl
  obtain ⟨ξ₁, ξ₂, ξ₃, a1, a2, a3, a4, a3', a4', a5, a6, a7, a8, a9, a10, a11⟩ :=
    Work.Math.BonnorEbertMax2.bonnor_ebert_second_max 2000 le_rfl _ _ A1 A2 A3 hz
  have hξ0 : (0 : ℝ) ≤ ξ₁ := by linarith
  have hξ20 : (0 : ℝ) ≤ ξ₂ := by linarith
  rw [hm ξ₃] at a8 a9
  simp only [neg_neg] at a10 a11
  -- the extremisers of the run with S = max ξ 2000 are those of the run with S = 2000
  have agree : ∀ ξ : ℝ, ∃ η₁ η₂ η₃ : ℝ, η₁ = ξ₁ ∧ η₂ = ξ₂ ∧ η₃ = ξ₃ ∧
      (∀ s ∈ Icc (0 : ℝ) (max ξ 2000), s ≠ η₁ → beMass ψ s < beMass ψ η₁) ∧
      (∀ s ∈ Icc η₁ (max ξ 2000), s ≠ η₂ → beMass ψ η₂ < beMass ψ s) ∧
      (∀ s ∈ Icc η₂ (max ξ 2000), s ≠ η₃ → beMass ψ s < beMass ψ η₃) := by
    intro ξ
    obtain ⟨B1, B2, B3⟩ := hyp (max ξ 2000) (le_max_right _ _)
    obtain ⟨η₁, η₂, η₃, b1, b2, b3, b4, b3', b4', b5, b6, b7, -, -, -, -⟩ :=
      Work.Math.BonnorEbertMax2.bonnor_ebert_second_max (max ξ 2000) (le_max_right _ _) _ _ B1 B2 B3 hz
    have hM : (2000 : ℝ) ≤ max ξ 2000 := le_max_right _ _
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
    refine ⟨η₁, η₂, η₃, rfl, rfl, rfl, fun s hs hne => ?_, fun s hs hne => ?_, fun s hs hne => ?_⟩
    · have := b5 s hs hne; rwa [hm s, hm η₁] at this
    · have := b6 s hs hne; rwa [hm s, hm η₂] at this
    · have := b7 s hs hne; rwa [hm s, hm η₃] at this
  refine ⟨ξ₁, ξ₂, ξ₃, a1, a2, a3, a4, a3', a4', ?_, ?_, ?_, a8, a9, a10, a11⟩
  · intro ξ hξ hne
    obtain ⟨η₁, η₂, η₃, rfl, rfl, rfl, c1, c2, c3⟩ := agree ξ
    exact c1 ξ ⟨hξ, le_max_left _ _⟩ hne
  · intro ξ hξ hne
    obtain ⟨η₁, η₂, η₃, rfl, rfl, rfl, c1, c2, c3⟩ := agree ξ
    exact c2 ξ ⟨hξ, le_max_left _ _⟩ hne
  · intro ξ hξ hne
    obtain ⟨η₁, η₂, η₃, rfl, rfl, rfl, c1, c2, c3⟩ := agree ξ
    exact c3 ξ ⟨hξ, le_max_left _ _⟩ hne

end Work.Math.BonnorEbertMax2BlindClosed

#print axioms Work.Math.BonnorEbertMax2BlindClosed.blind_closed
