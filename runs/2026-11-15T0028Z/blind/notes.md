# Interpretive choices

- ψ : ℝ → ℝ; only values on [0, ∞) matter. Hypothesis is a predicate `IsRegularSolution` (universally quantified, not an existence claim).
- Regularity at 0: ψ continuous on Ici 0, ψ 0 = 0, `HasDerivWithinAt ψ 0 (Ici 0) 0` (one-sided ψ'(0)=0).
- ODE for ξ>0 in divergence form: ψ differentiable at ξ and `HasDerivAt (x ↦ x² · deriv ψ x) (ξ² e^{-ψ ξ}) ξ`, equivalent to (1/ξ²)(ξ²ψ')' = e^{-ψ}. ψ' is `deriv ψ`. Not assumed twice differentiable separately.
- Mass: m ξ = (4π)^(-1/2) e^{-ψ/2} ξ² deriv ψ ξ; at ξ = 0 the ξ² factor kills the junk value of `deriv`.
- Sequence x : ℕ → ℝ (ξ_k), StrictMono, tends to atTop; ξ₀ bounds 6.4507514 ≤ ξ₀ ≤ 6.4507515.
- (i)-(iii): strict inequalities with ξ ≠ the extremum, ξ ≥ 0 for (i), ξ ≥ ξ_{2k} for (ii), ξ ≥ ξ_{2k+1} for (iii).
- (iv) with index parity: maxima at even indices, minima at odd; threshold √(2/π).
- (v) Tendsto (mass ψ) atTop (nhds √(2/π)).
- Existence of the solution is not asserted; uniqueness not needed. Not compiled.
