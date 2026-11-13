# Interpretive choices
- ψ : ℝ → ℝ, only its values on [0,∞) matter. Regularity at 0: `ContDiffOn ℝ 2 ψ (Ici 0)` (C² up to the boundary), `ψ 0 = 0`, and `ψ'(0)=0` as `HasDerivWithinAt ψ 0 (Ici 0) 0` (one-sided, since ψ is only meaningful for ξ ≥ 0).
- ODE stated for ξ > 0 as `deriv (fun x => x^2 * deriv ψ x) ξ = ξ^2 * exp (-ψ ξ)`, i.e. (ξ²ψ')' = ξ² e^{-ψ}, equivalent to the given form after multiplying by ξ². For ξ > 0, `deriv ψ` is the genuine derivative (Ici 0 is a neighbourhood).
- The ODE is assumed globally on all ξ > 0 (the regular solution exists for all ξ; this is a hypothesis, not proved). Uniqueness of the solution is not stated; the theorem quantifies over every ψ satisfying the hypotheses.
- Mass `beMass ψ ξ = (4π)^(-1/2) * exp(-ψ ξ/2) * ξ^2 * deriv ψ ξ`; at ξ = 0 this is 0 (ξ² factor). `(4π)^(-1/2)` is rpow with exponent -(1/2).
- Conclusion: exists ξ₁ with 6.4507514 ≤ ξ₁ ≤ 6.4507515, 1.1822265 ≤ m(ξ₁) ≤ 1.1822266, and for all ξ ≥ 0, ξ ≠ ξ₁, m ξ < m ξ₁ (strict global max). Decimal literals are real numerals.
- Proof left as `sorry`; not compiled.
