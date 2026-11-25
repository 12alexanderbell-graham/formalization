# Interpretive choices (blind)

- Solution class: w, φ : ℝ → ℝ (only values on [0,∞) matter). Hypotheses: w 0 = 0;
  for every s ≥ 0, HasDerivWithinAt w (φ s) (Ici 0) s (so w'(0) is one-sided, = φ 0);
  φ continuous within Ici 0 at 0; for s > 0, HasDerivAt φ (-(2/s)*φ s - exp (w s)) s.
  No w'(0) condition imposed. (This forces w'(0)=0 and uniqueness, mathematically.)
- λ is `gelfandLam w s = s^2 * Real.exp (w s)`.
- Turning points: not defined separately; ζ : ℕ → ℝ is existentially quantified with
  StrictMono, Tendsto atTop atTop, and the stated strict monotonicity on closed intervals
  Icc 0 (ζ 0), Icc (ζ(2k)) (ζ(2k+1)) (StrictAntiOn), Icc (ζ(2k+1)) (ζ(2k+2)) (StrictMonoOn).
  The monotonicity pattern is what characterises them as turning points.
- 0 < ζ 0 is not stated separately (implied by the ζ 0 numeric bounds).
- Limits: Tendsto with atTop on ℕ or ℝ, nhds written 𝓝 (open Topology).
  λ → 2 over ℝ; ratio of λ-deviations and ζ-ratio as sequences in k : ℕ.
  Limit constants: -Real.exp (-π/√7) and Real.exp (2π/√7).
- Numeric bounds as closed intervals (Icc) with decimal literals in ℝ.
- (ii): "seventh turning point on, k ≥ 6" read as: for all k ≥ 6 (ζ indexed from 0),
  the ratios ζ(k+1)/ζ k and (λ(ζ(k+1))-2)/(λ(ζ k)-2) obey the bounds
  10.3 ≤ · ≤ 11.2 and -0.33 ≤ · ≤ -0.28. Division is real division (denominators are nonzero
  since λ(ζ k) ≠ 2 by the strict inequalities).
- Not compiled.
