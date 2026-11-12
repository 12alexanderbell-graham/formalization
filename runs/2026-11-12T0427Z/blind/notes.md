# Interpretive choices
- ψ and its derivative are two functions ψ, dψ : ℝ → ℝ (dψ is ψ' as data, avoiding `deriv` junk values). Only values on [0, ∞) matter.
- Regular solution: ψ 0 = 0, dψ 0 = 0, both ψ and dψ continuous within Ici 0 at 0; for every ξ > 0, HasDerivAt ψ (dψ ξ) ξ and HasDerivAt dψ (exp(-ψ ξ) - (2/ξ) dψ ξ) ξ, i.e. ψ'' + (2/ξ)ψ' = e^{-ψ}, equivalent to (1/ξ²)(ξ²ψ')' = e^{-ψ}. The ODE is assumed on all of (0, ∞) (the true solution is global); only (0, 7] is used.
- Regularity at 0 is expressed by right-continuity of ψ, ψ' at 0 (with the stated values), not by ContDiff. Uniqueness of such a solution is a consequence, not assumed.
- Mass: m ξ = (4π)^(-1/2) * exp(-ψ ξ / 2) * ξ^2 * ψ'(ξ), defined for all ξ via `beMass`; the real power uses rpow with exponent -(1/2).
- Assumed: the IsRegularIsothermal hypothesis. Concluded: existence of ξ₁ in the stated interval, StrictMonoOn on Icc 0 ξ₁, StrictAntiOn on Icc ξ₁ 7, and the bounds on m(ξ₁) and e^{ψ(ξ₁)}.
- Decimal literals are read as exact reals. Not compiled (per brief); proof is `sorry`.
