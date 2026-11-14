# Interpretive choices
- ψ : ℝ → ℝ; only values on [0,∞) matter. Domain: the solution is assumed to exist (and be C²) on all of [0,∞); this is an assumption (hypothesis), not concluded.
- Regularity at 0: ContDiffOn ℝ 2 ψ (Ici 0), ψ 0 = 0, HasDerivWithinAt ψ 0 (Ici 0) 0 (one-sided derivative 0).
- ODE stated in divergence form for ξ > 0: deriv (fun s => s^2 * deriv ψ s) ξ = ξ^2 * exp(-ψ ξ), equivalent to (1/ξ²)(ξ²ψ')' = e^{-ψ}. Uses `deriv` (two-sided), fine for ξ>0.
- Mass m(ξ) = (4π)^(-1/2) * exp(-ψ ξ/2) * ξ^2 * deriv ψ ξ, with rpow exponent -(1/2). At ξ=0 `deriv` is the two-sided derivative (junk possibly) but multiplied by ξ²=0, so m 0 = 0.
- Claim concluded: ∃ ξ₁ ξ₂ with the numeric bounds; ξ₁ strict global max over ξ ≥ 0; ξ₂ strict min over ξ ≥ ξ₁; bounds on m(ξ₂) and exp(ψ ξ₂). ξ₂ ≥ ξ₁ follows from the bounds.
- Strict inequalities phrased as "ξ ≠ ξ_i → ineq" (unique extremizer) rather than IsMinOn/IsMaxOn.
- Numerals are real literals (decimal). Not compiled.
