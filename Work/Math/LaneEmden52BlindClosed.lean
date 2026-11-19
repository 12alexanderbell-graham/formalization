import Mathlib
import Work.Math.LaneEmden52

/-!
# Lane–Emden index five halves: the blind restatement closed

The blind restatement (`runs/2026-11-19T1628Z/blind/LaneEmden52Blind.lean`, statement copied
verbatim by `runs/2026-11-19T1628Z/scripts/mk_blind_closed52.py`) asks for θ twice continuously
differentiable on [0, 6], θ'(0) = 0 within [0, 6] and the equation on the open interval in `deriv`
form, and concludes with `deriv θ` at the zero. It follows from the program's helper
`Work.Math.LaneEmden52.core` on [0, 134/25] with φ = derivWithin θ (Icc 0 6): on the open interval
`derivWithin` agrees with `deriv`, and the derivative of φ there is `deriv (deriv θ)`. The blind
hypothesis θ'(0) = 0 is not used (it is implied).
-/

namespace Work.Math.LaneEmden52BlindClosed
open Set Filter Topology

theorem blind_laneEmden52 (θ : ℝ → ℝ)
    (hC : ContDiffOn ℝ 2 θ (Set.Icc (0 : ℝ) 6))
    (h0 : θ 0 = 1)
    (h0' : derivWithin θ (Set.Icc (0 : ℝ) 6) 0 = 0)
    (hode : ∀ ξ ∈ Set.Ioo (0 : ℝ) 6,
      deriv (deriv θ) ξ + 2 / ξ * deriv θ ξ + (θ ξ) ^ ((5 : ℝ) / 2) = 0) :
    ∃ ξ₁ : ℝ, ξ₁ ∈ Set.Ioo (0 : ℝ) 6 ∧ θ ξ₁ = 0 ∧
      (∀ ξ ∈ Set.Ico (0 : ℝ) ξ₁, 0 < θ ξ) ∧
      (5.35527545 ≤ ξ₁ ∧ ξ₁ ≤ 5.35527546) ∧
      (2.18719956 ≤ -ξ₁ ^ 2 * deriv θ ξ₁ ∧ -ξ₁ ^ 2 * deriv θ ξ₁ ≤ 2.18719957) ∧
      (23.40646222 ≤ ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * deriv θ ξ₁)) ∧
        ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * deriv θ ξ₁)) ≤ 23.40646231) := by
  set φ : ℝ → ℝ := derivWithin θ (Icc (0 : ℝ) 6) with hφdef
  have hU : UniqueDiffOn ℝ (Icc (0 : ℝ) 6) := uniqueDiffOn_Icc (by norm_num)
  have hd1 : DifferentiableOn ℝ θ (Icc (0 : ℝ) 6) := hC.differentiableOn (by norm_num)
  have hC1 : ContDiffOn ℝ 1 φ (Icc (0 : ℝ) 6) := hC.derivWithin hU (by norm_num)
  have hd2 : DifferentiableOn ℝ φ (Icc (0 : ℝ) 6) := hC1.differentiableOn (by norm_num)
  have hsub : Icc (0 : ℝ) (134 / 25) ⊆ Icc 0 6 := Icc_subset_Icc le_rfl (by norm_num)
  -- on the open interval, φ = deriv θ near ξ
  have hloc : ∀ ξ ∈ Ioo (0 : ℝ) 6, φ =ᶠ[𝓝 ξ] deriv θ := by
    intro ξ hξ
    filter_upwards [Ioo_mem_nhds hξ.1 hξ.2] with y hy
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)
  have hθ' : ∀ ξ ∈ Icc (0 : ℝ) (134 / 25),
      HasDerivWithinAt θ (φ ξ) (Icc 0 (134 / 25)) ξ := fun ξ hξ =>
    ((hd1 ξ (hsub hξ)).hasDerivWithinAt).mono hsub
  have hφ0 : ContinuousWithinAt φ (Icc 0 (134 / 25)) 0 :=
    (hC1.continuousOn 0 ⟨le_rfl, by norm_num⟩).mono hsub
  have hφ' : ∀ ξ ∈ Ioc (0 : ℝ) (134 / 25),
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ ((5 : ℝ) / 2)) (Icc 0 (134 / 25)) ξ := by
    intro ξ hξ
    have hξo : ξ ∈ Ioo (0 : ℝ) 6 := ⟨hξ.1, by linarith [hξ.2]⟩
    have hda : HasDerivAt φ (deriv φ ξ) ξ :=
      ((hd2 ξ (Ioo_subset_Icc_self hξo)).differentiableAt (Icc_mem_nhds hξo.1 hξo.2)).hasDerivAt
    have e1 : deriv φ ξ = deriv (deriv θ) ξ := (hloc ξ hξo).deriv_eq
    have e2 : φ ξ = deriv θ ξ := (hloc ξ hξo).eq_of_nhds
    have h := hode ξ hξo
    have hv : deriv φ ξ = -(2 / ξ * φ ξ) - θ ξ ^ ((5 : ℝ) / 2) := by
      rw [e1, e2]; linarith
    rw [← hv]
    exact hda.hasDerivWithinAt
  obtain ⟨ξ₁, ha, hb, hz, hpos, hω1, hω2, hc1, hc2⟩ :=
    Work.Math.LaneEmden52.core θ φ hθ' hφ0 hφ' h0
  have hξo : ξ₁ ∈ Ioo (0 : ℝ) 6 := ⟨by linarith, by linarith⟩
  have e2 : φ ξ₁ = deriv θ ξ₁ := (hloc ξ₁ hξo).eq_of_nhds
  have en : -ξ₁ ^ 2 * deriv θ ξ₁ = -(ξ₁ ^ 2 * φ ξ₁) := by rw [e2]; ring
  refine ⟨ξ₁, hξo, hz, hpos, ⟨ha, hb⟩, ?_, ?_⟩
  · rw [en]; exact ⟨hω1, hω2⟩
  · rw [en]; exact ⟨hc1, hc2⟩

end Work.Math.LaneEmden52BlindClosed
