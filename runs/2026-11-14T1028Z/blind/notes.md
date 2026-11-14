# Interpretive choices
- ψ : ℝ → ℝ, only its values on [0, ∞) matter. Domain: the solution is assumed to exist on all of [0, ∞) (global solution), as a hypothesis, not proved.
- Regularity at 0: `ContDiffOn ℝ 2 ψ (Ici 0)` (C² up to the boundary), `ψ 0 = 0`, `HasDerivWithinAt ψ 0 (Ici 0) 0` (ψ'(0)=0). This picks out the regular solution.
- ODE: (1/ξ²)(ξ²ψ')' = e^{-ψ} stated for ξ > 0 as `deriv (fun x => x^2 * derivWithin ψ (Ici 0) x) ξ = ξ^2 * exp (-ψ ξ)` (multiplied through by ξ² to avoid division). derivWithin on Ici 0 equals the ordinary derivative for x > 0.
- m defined as `beMass ψ ξ = (4π)^(-1/2) * exp(-ψ ξ/2) * ξ^2 * derivWithin ψ (Ici 0) ξ`; (4π)^(-1/2) written as rpow with exponent -(1/2).
- Conclusion: ∃ ξ₁ ξ₂ ξ₃ with the stated numeric brackets; strict inequalities with ξ ≠ the point; domains: ξ ≥ 0 for the max, ξ ≥ ξ₁ for the min, ξ ≥ ξ₂ for the second max; bounds on m(ξ₃) and exp(ψ ξ₃) as stated.
- Decimals are real literals (`6.4507514` etc.) elaborated in ℝ.
- Nothing compiled; proof is `sorry`.
