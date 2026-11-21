# Interpretive choices
- Solution class: a predicate `IsRegularIsothermal w φ`: `w 0 = 0`; for every s ≥ 0, `HasDerivWithinAt w (φ s) (Ici 0) s` (one-sided at 0, ordinary derivative for s > 0); `ContinuousWithinAt φ (Ici 0) 0`; for s > 0, `HasDerivAt φ (-(2/s) * φ s - exp (w s)) s`. No condition on `φ 0` is imposed. w, φ : ℝ → ℝ (values off [0,∞) irrelevant).
- λ(s) = s^2 * exp (w s), written inline as a lambda.
- Turning points: ζ : ℕ → ℝ, StrictMono, tending to atTop. Characterised by strict monotonicity on closed intervals: StrictMonoOn on Icc 0 (ζ 0); StrictAntiOn on Icc (ζ(2k)) (ζ(2k+1)); StrictMonoOn on Icc (ζ(2k+1)) (ζ(2k+2)), for all k. No separate "derivative vanishes" clause (follows from the monotonicity pattern plus differentiability, so omitted).
- λ → 2: `Tendsto λ atTop (𝓝 2)`.
- Decimals: real literals like `(3.321992118 : ℝ)`, closed intervals `Icc a b`; ζ 0 and λ(ζ i) for i = 0..6 each in its stated interval, conjunction of seven statements.
- Existence of ζ is the claim; the statement is for every w, φ satisfying the predicate. Not compiled.
