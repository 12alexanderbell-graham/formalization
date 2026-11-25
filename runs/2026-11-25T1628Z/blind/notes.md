# Interpretive choices

- Solution class: w, φ : ℝ → ℝ (values off [0,∞) irrelevant). Hypotheses: w 0 = 0; for every s ≥ 0, HasDerivWithinAt w (φ s) (Ici 0) s; φ ContinuousWithinAt (Ici 0) at 0; for s > 0, HasDerivAt φ (-(2/s) * φ s - exp (w s)) s. No condition on φ 0 (it is forced to be 0 by the ODE, not assumed). The theorem is stated for every such pair (w, φ), so uniqueness is implicitly part of what is needed.
- Mass: beMass w φ s = s^2 * (-φ s) * exp (w s / 2) / sqrt (4π); singularMass = sqrt (2/π).
- Extrema characterised by explicit ξ : ℕ → ℝ with StrictMono and Tendsto atTop atTop; monotonicity on closed intervals Icc via StrictMonoOn / StrictAntiOn (Icc 0 (ξ 0), Icc (ξ 2k) (ξ 2k+1), Icc (ξ 2k+1) (ξ 2k+2)).
- Global max: ∀ s ≥ 0, m s ≤ m (ξ 0). Strict min over [ξ 2k, ∞): for s ≥ ξ(2k), s ≠ ξ(2k+1), m(ξ(2k+1)) < m s. Strict max over [ξ(2k+1), ∞) analogous with ξ(2k+2).
- Mass vs singular value: for all k, m(ξ(2k+1)) < singularMass < m(ξ(2k)).
- m → singularMass via Tendsto ... atTop (𝓝 singularMass).
- ξ 0 ∈ Icc 6.4507514 6.4507515 (real literals).
- (i) Tendsto (fun k => ξ (k+1) / ξ k) atTop (𝓝 (exp (2π/√7))).
- (ii) Tendsto (fun k => (m (ξ (k+1)) - c)/(m (ξ k) - c)) atTop (𝓝 (-exp (-π/√7))), c = singularMass. Division by zero is not an issue as the ratios are of nonzero terms by the strict inequalities, and the limit statement does not need that anyway.
- `open Filter Topology Set` used for notation 𝓝, Ici, Icc; no compilation done.
