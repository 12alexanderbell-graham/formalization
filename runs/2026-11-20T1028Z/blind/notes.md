# Interpretive choices

- Solution class: w, φ : ℝ → ℝ. `w 0 = 0`; for every s ≥ 0, `HasDerivWithinAt w (φ s) (Ici 0) s` (one-sided at 0); `ContinuousWithinAt φ (Ici 0) 0`; for every s > 0, `HasDerivAt φ (-(2/s) * φ s - exp (w s)) s`. No condition on φ 0 (w'(0)) is added. Values on s < 0 are unconstrained and irrelevant.
- λ is `gelfandLam w s = s^2 * exp (w s)`.
- Turning points: no derivative characterisation; the ζ_k are given by an explicit sequence `ζ : ℕ → ℝ` that is `StrictMono` and tends to atTop, with monotonicity of λ on closed intervals: StrictMonoOn on [0, ζ 0], StrictAntiOn on [ζ(2k), ζ(2k+1)], StrictMonoOn on [ζ(2k+1), ζ(2k+2)]. Strict monotonicity on the adjacent closed intervals forces these to be the turning points (local extrema).
- λ → 2 stated as `Tendsto (gelfandLam w) atTop (nhds 2)`.
- Decimals are real literals in closed intervals `Set.Icc`, with ζ_0..ζ_3 being `ζ 0 .. ζ 3`.
- Universal over all w, φ satisfying the hypotheses (existence/uniqueness of w is not part of the statement; the claim holds for every such w).
- Proof is `sorry`; not compiled.
