# Interpretive choices
- Solution class: `w φ : ℝ → ℝ` with `w 0 = 0`; `HasDerivWithinAt w (φ s) (Ici 0) s` for all s ≥ 0 (one-sided at 0); `ContinuousWithinAt φ (Ici 0) 0`; `HasDerivAt φ (-(2/s) * φ s - exp (w s)) s` for all s > 0. No condition on φ 0. Bundled as `IsRegularSolution`.
- λ is `lam w s = s^2 * exp (w s)`.
- Turning points: not defined separately; characterised via the monotonicity pattern on closed intervals (`StrictMonoOn` on `Icc 0 (ζ 0)`, `StrictAntiOn` on `Icc (ζ(2k)) (ζ(2k+1))`, `StrictMonoOn` on `Icc (ζ(2k+1)) (ζ(2k+2))`) plus `StrictMono ζ`, `Tendsto ζ atTop atTop`.
- Values: `lam(ζ(2k+1)) < 2 < lam(ζ(2k))`; `Tendsto (lam w) atTop (𝓝 2)`; numerical enclosures as `Icc` membership for `ζ 0` and `lam w (ζ 0)`.
- Ratio limit: `Tendsto (fun k => (lam (ζ(k+1)) - 2)/(lam (ζ k) - 2)) atTop (𝓝 (-exp (-π/√7)))`. Division by zero is junk-valued in Lean, but the strict inequalities make the denominators nonzero.
- Parsed `-Real.exp (-Real.pi / Real.sqrt 7)` as -exp(-(π/√7)); same value.
- Statement quantifies over all (w, φ) satisfying the class; the ζ sequence is existential (uniqueness not asserted).
- Not compiled.
