# Interpretive choices (blind restatement)

- Solution is given as a pair of functions `ψ dψ : ℝ → ℝ` (ψ and its derivative ψ'), no existence/uniqueness asserted; the theorem is for every pair satisfying the hypotheses.
- Domain: only ξ ≥ 0 matters; hypotheses use `HasDerivWithinAt ... (Set.Ici 0) ξ` for ξ ≥ 0 (one-sided at 0). Values for ξ < 0 are unconstrained.
- Regularity at 0: ψ 0 = 0, dψ 0 = 0 (ψ'(0) = 0), plus ψ has derivative dψ on [0,∞).
- ODE in divergence form (avoids dividing by ξ²): the function x ↦ x² ψ'(x) has derivative ξ² e^{-ψ(ξ)} on [0,∞). This is (1/ξ²)(ξ²ψ')' = e^{-ψ} for ξ > 0 and is automatically consistent at 0.
- Mass: `beMass ψ dψ ξ = (√(4π))⁻¹ · exp(-ψ ξ / 2) · ξ² · ψ'(ξ)`, i.e. (4π)^{-1/2} as an inverse square root.
- Conclusion is an existential over ξ : ℕ → ℝ (indexed from 0), StrictMono, tending to atTop, with 6.4507514 ≤ ξ 0 ≤ 6.4507515, then (i)–(viii) in order. "Every radius" means every real x ≥ 0 in (i); in (ii),(iii) x ranges over reals above the stated turning point (implicitly ≥ 0).
- (iv) is stated as a conjunction per k: m(ξ_{2k+1}) < √(2/π) < m(ξ_{2k}).
- (v) is `Tendsto m atTop (nhds (√(2/π)))`.
- (vi)–(viii) use `StrictMonoOn`/`StrictAntiOn` on closed intervals `Icc`.
- Decimal bounds written as real literals; proof is `sorry`; not compiled.
