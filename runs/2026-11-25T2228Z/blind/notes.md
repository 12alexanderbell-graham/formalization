# Interpretive choices (blind)
- Solution class: w, φ : ℝ → ℝ; w 0 = 0; for every s ≥ 0, HasDerivWithinAt w (φ s) (Ici 0) s; φ ContinuousWithinAt (Ici 0) at 0; for s > 0, HasDerivAt φ (-(2/s)*φ s - exp (w s)) s. No condition on φ 0. (w'' + 2w'/s + e^w = 0 rewritten via φ.)
- m = beMass w φ s = s^2 * (-φ s) * exp (w s / 2) / sqrt (4π); singular value sqrt (2/π).
- Extrema characterised not by derivatives but by monotonicity on Icc pieces (StrictMonoOn/StrictAntiOn on closed intervals, Icc 0 (ξ 0) for the first), plus global max at ξ 0 over s ≥ 0 (≤, so non-strict as stated), strict min over [ξ(2k), ∞) and strict max over [ξ(2k+1), ∞) (every other point s ≠ extremum is strictly worse).
- Index convention: ξ : ℕ → ℝ, 0-indexed; even index = maxima, odd = minima; "k ≥ 5" is ξ 5 onward (sixth extremum).
- StrictMono ξ and Tendsto ξ atTop atTop both stated; ξ 0 > 0 follows from strict monotonicity on Icc 0 (ξ 0) being nontrivial only implicitly (not stated separately; ξ 0 ≥ 6.45 anyway).
- Limits: Tendsto with 𝓝; exp(2π/√7) written Real.exp (2 * Real.pi / Real.sqrt 7); -exp(-π/√7) as -Real.exp (-Real.pi / Real.sqrt 7). m → √(2/π) as Tendsto (beMass w φ) atTop.
- Bounds: ratio memberships in Icc (9.2) (12.9) and Icc (-0.42) (-0.21), division in ℝ (denominators nonzero by strict inequalities with √(2/π)). Decimal literals typed as ℝ.
- Statement is for every such w (hypotheses are universally quantified; uniqueness of the solution not asserted separately).
