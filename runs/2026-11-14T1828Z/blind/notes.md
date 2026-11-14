# Interpretive choices
- ψ : ℝ → ℝ; only values on [0, ∞) matter. Hypothesis bundled in `IsRegularEmdenSolution`.
- Regularity at 0: ContDiffOn ℝ 2 ψ (Ici 0), ψ 0 = 0, derivWithin ψ (Ici 0) 0 = 0 (one-sided, since ψ is only meaningful for ξ ≥ 0).
- ODE stated for ξ > 0 only: (1/ξ²)·deriv (x ↦ x²·deriv ψ x) ξ = exp(-ψ ξ). On (0,∞) (open) `deriv` is the genuine derivative.
- ψ' is `deriv ψ`; at ξ = 0 it is irrelevant since m has a factor ξ².
- Mass: m ξ = (√(4π))⁻¹ · exp(-ψ ξ / 2) · ξ² · deriv ψ ξ  (reading (4π)^(-1/2) as inverse sqrt).
- Assumed: the regular solution hypotheses (ψ is that solution; uniqueness not proved/needed). Concluded: existence of ξ₁..ξ₅ with all numeric bounds and the five strict extremality conditions.
- Domains: first claim over all ξ ≥ 0; the others over ξ ≥ ξ_{k-1} as written; strict inequalities with ξ ≠ ξ_k.
- Decimal bounds are real literals; e^{ψ(ξ₅)} written Real.exp (ψ ξ₅).
- Not compiled.
