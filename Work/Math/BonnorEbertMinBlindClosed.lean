import Mathlib
import Work.Math.BonnorEbertMin
import Work.Math.BonnorEbertMinBlind

/-! Bonnor–Ebert sphere: the blind restatement `Work.Math.BonnorEbertMinBlind.blind_bonnor_ebert_min`
(ψ of class C² on [0, ∞) via the predicate `IsRegularEmden`, equation in the form (ξ² ψ')' = ξ² e^{−ψ} with
Mathlib's `deriv`, mass with the rpow (4π)^(−1/2), contrast e^{ψ}, strict maximum over every radius ξ ≥ 0 and
strict minimum over every radius ξ ≥ ξ₁) closed from the frozen headline
`Work.Math.BonnorEbertMin.bonnor_ebert_min` with w = −ψ, φ = −(one-sided derivative of ψ on [0, ∞)).
The headline is applied once with S = 150 and once with S = max ξ 150; the maximisers agree because each is
a strict maximiser on a set containing the other, and then so do the minimisers. Written by run
2026-11-14T0428Z, adapted from `Work/Math/BonnorEbertGlobalBlindClosed.lean`. -/

namespace Work.Math.BonnorEbertMinBlindClosed
open Set Filter Topology Work.Math.BonnorEbertMinBlind

theorem blind_closed (ψ : ℝ → ℝ) (hψ : IsRegularEmden ψ) :
    ∃ ξ₁ ξ₂ : ℝ,
      6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      (∀ ξ : ℝ, 0 ≤ ξ → ξ ≠ ξ₁ → beMass ψ ξ < beMass ψ ξ₁) ∧
      (∀ ξ : ℝ, ξ₁ ≤ ξ → ξ ≠ ξ₂ → beMass ψ ξ₂ < beMass ψ ξ) ∧
      0.694366 ≤ beMass ψ ξ₂ ∧ beMass ψ ξ₂ ≤ 0.694367 ∧
      2579.69 ≤ Real.exp (ψ ξ₂) ∧ Real.exp (ψ ξ₂) ≤ 2579.71 := by
  obtain ⟨hC, h0, h0', hode⟩ := hψ
  set dψ : ℝ → ℝ := derivWithin ψ (Ici 0) with hdψ
  have hU : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  -- first derivative
  have hD : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt ψ (dψ s) (Ici 0) s := fun s hs =>
    ((hC.differentiableOn (by norm_num)) s hs).hasDerivWithinAt
  have hdeq : ∀ x : ℝ, 0 < x → dψ x = deriv ψ x := fun x hx =>
    derivWithin_of_mem_nhds (Ici_mem_nhds hx)
  have hd00 : dψ 0 = 0 := h0'.derivWithin (hU 0 (Set.mem_Ici.mpr le_rfl))
  have hcont : ContinuousOn dψ (Ici 0) := hC.continuousOn_derivWithin hU (by norm_num)
  have hC1 : ContDiffOn ℝ 1 dψ (Ici 0) := hC.derivWithin hU (by norm_num)
  -- second derivative from the equation
  have h2 : ∀ x : ℝ, 0 < x → HasDerivAt dψ (Real.exp (-(ψ x)) - 2 / x * dψ x) x := by
    intro x hx
    have hdiff : DifferentiableAt ℝ dψ x :=
      ((hC1.differentiableOn (by norm_num)) x (le_of_lt hx)).differentiableAt (Ici_mem_nhds hx)
    have hev : (fun y => y ^ 2 * deriv ψ y) =ᶠ[𝓝 x] (fun y => y ^ 2 * dψ y) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [hdeq y hy]
    have hprod : HasDerivAt (fun y => y ^ 2 * dψ y) _ x := (hasDerivAt_pow 2 x).mul hdiff.hasDerivAt
    have e := hode x hx
    rw [hev.deriv_eq, hprod.deriv] at e
    have hx0 : x ≠ 0 := hx.ne'
    have key : deriv dψ x = Real.exp (-(ψ x)) - 2 / x * dψ x := by
      have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
      field_simp
      push_cast at e
      nlinarith [e]
    rw [← key]; exact hdiff.hasDerivAt
  -- the headline's hypotheses for any S ≥ 7
  have hyp : ∀ S : ℝ, 150 ≤ S →
      (∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt (fun x => -ψ x) (-dψ s) (Icc 0 S) s) ∧
      ContinuousWithinAt (fun x => -dψ x) (Icc 0 S) 0 ∧
      (∀ s ∈ Ioc (0 : ℝ) S, HasDerivWithinAt (fun x => -dψ x)
        (-(2 / s * (fun x => -dψ x) s) - Real.exp ((fun x => -ψ x) s)) (Icc 0 S) s) := by
    intro S _
    refine ⟨fun s hs => ((hD s hs.1).mono Icc_subset_Ici_self).neg,
      ((hcont 0 (Set.mem_Ici.mpr le_rfl)).neg).mono Icc_subset_Ici_self, fun s hs => ?_⟩
    exact ((h2 s hs.1).neg.congr_deriv (by ring)).hasDerivWithinAt
  have hz : (fun x => -ψ x) 0 = 0 := by simp [h0]
  -- the mass agrees on [0, ∞)
  have hm : ∀ s : ℝ, 0 ≤ s → s ^ 2 * (-(fun x => -dψ x) s) * Real.exp ((fun x => -ψ x) s / 2) /
      Real.sqrt (4 * Real.pi) = beMass ψ s := by
    intro s hs
    simp only [beMass, neg_neg, neg_div]
    have hp : (0 : ℝ) ≤ 4 * Real.pi := by positivity
    rw [Real.rpow_neg hp, ← Real.sqrt_eq_rpow]
    rcases eq_or_lt_of_le hs with h | h
    · rw [← h]; simp
    · rw [hdeq s h]; field_simp
  obtain ⟨A1, A2, A3⟩ := hyp 150 le_rfl
  obtain ⟨ξ₁, ξ₂, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ :=
    Work.Math.BonnorEbertMin.bonnor_ebert_min 150 le_rfl _ _ A1 A2 A3 hz
  have hξ0 : (0 : ℝ) ≤ ξ₁ := by linarith
  have hξ20 : (0 : ℝ) ≤ ξ₂ := by linarith
  rw [hm ξ₂ hξ20] at a7 a8
  simp only [neg_neg] at a9 a10
  refine ⟨ξ₁, ξ₂, a1, a2, a3, a4, ?_, ?_, a7, a8, a9, a10⟩
  · intro ξ hξ hne
    obtain ⟨B1, B2, B3⟩ := hyp (max ξ 150) (le_max_right _ _)
    obtain ⟨η, -, b1, b2, -, -, b3, -⟩ :=
      Work.Math.BonnorEbertMin.bonnor_ebert_min (max ξ 150) (le_max_right _ _) _ _ B1 B2 B3 hz
    have hη0 : (0 : ℝ) ≤ η := by linarith
    have hηξ : η = ξ₁ := by
      by_contra hne'
      have l1 := a5 η ⟨hη0, by linarith⟩ hne'
      have l2 := b3 ξ₁ ⟨hξ0, le_trans (by linarith) (le_max_right ξ 150)⟩ (Ne.symm hne')
      linarith
    subst hηξ
    have := b3 ξ ⟨hξ, le_max_left _ _⟩ hne
    rwa [hm ξ hξ, hm η hη0] at this
  · intro ξ hξ hne
    have hξ' : (0 : ℝ) ≤ ξ := le_trans hξ0 hξ
    obtain ⟨B1, B2, B3⟩ := hyp (max ξ 150) (le_max_right _ _)
    obtain ⟨η, η₂, b1, b2, b3, b4, b5, b6, -, -, -, -⟩ :=
      Work.Math.BonnorEbertMin.bonnor_ebert_min (max ξ 150) (le_max_right _ _) _ _ B1 B2 B3 hz
    have hη0 : (0 : ℝ) ≤ η := by linarith
    have hηξ : η = ξ₁ := by
      by_contra hne'
      have l1 := a5 η ⟨hη0, by linarith⟩ hne'
      have l2 := b5 ξ₁ ⟨hξ0, le_trans (by linarith) (le_max_right ξ 150)⟩ (Ne.symm hne')
      linarith
    subst hηξ
    have hη2 : η₂ = ξ₂ := by
      by_contra hne'
      have l1 := a6 η₂ ⟨by linarith, by linarith⟩ hne'
      have l2 := b6 ξ₂ ⟨by linarith, le_trans (by linarith) (le_max_right ξ 150)⟩ (Ne.symm hne')
      linarith
    subst hη2
    have := b6 ξ ⟨hξ, le_max_left _ _⟩ hne
    rwa [hm ξ hξ', hm η₂ hξ20] at this

end Work.Math.BonnorEbertMinBlindClosed

#print axioms Work.Math.BonnorEbertMinBlindClosed.blind_closed
