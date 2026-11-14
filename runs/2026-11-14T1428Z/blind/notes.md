# Interpretive choices
- ψ : ℝ → ℝ, only its values on [0, ∞) matter; the structure `IsRegularIsothermalSolution` is the hypothesis.
- Regularity at 0: ψ is C² on Ici 0 (`ContDiffOn ℝ 2 ψ (Set.Ici 0)`), ψ 0 = 0, and `HasDerivWithinAt ψ 0 (Set.Ici 0) 0` (ψ'(0)=0). This pins down the unique regular solution.
- ODE: the equation (1/ξ²)(ξ²ψ')' = e^{-ψ} is stated for ξ > 0 in the multiplied-out form
  `HasDerivAt (fun x => x^2 * deriv ψ x) (ξ^2 * exp (-ψ ξ)) ξ` (avoids division by ξ²; equivalent for ξ>0).
- ψ' is written `deriv ψ`; for ξ > 0 it is the genuine derivative (ψ differentiable near ξ). At ξ = 0, m(0) = 0 regardless since ξ² = 0.
- m(ξ) = (√(4π))⁻¹ · exp(-ψ ξ / 2) · ξ² · deriv ψ ξ, defined for all reals (only ξ ≥ 0 used).
- Claim is existential in ξ₁..ξ₄ with the given numeric bounds (decimal literals in ℝ); strict inequalities with "ξ ≠ ξᵢ" for uniqueness of extremum; domains: ξ ≥ 0, ≥ ξ₁, ≥ ξ₂, ≥ ξ₃ respectively.
- Contrast e^{ψ(ξ₄)} is stated as `Real.exp (ψ ξ₄)`.
- Nothing assumed beyond the ODE data; global existence of ψ on [0,∞) is implicit in the hypothesis (ψ is given on all of Ici 0). Ordering ξ₁<ξ₂<ξ₃<ξ₄ follows from the numeric bounds and is not separately stated.
