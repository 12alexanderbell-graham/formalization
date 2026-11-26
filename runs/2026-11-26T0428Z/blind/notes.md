# Interpretive choices (blind restatement)

- Solution class: functions `w φ : ℝ → ℝ`; `w 0 = 0`; for every s ≥ 0, `HasDerivWithinAt w (φ s) (Ici 0) s`; `φ` continuous within `Ici 0` at 0; for s > 0, `HasDerivAt φ (-(2/s)*φ s - exp (w s)) s`. No condition on `φ 0` beyond these. Values on s < 0 are unconstrained (irrelevant).
- Mass: `mass w φ s = s^2 * (-φ s) * exp (w s / 2) / sqrt (4π)`; singular mass `sqrt (2/π)`.
- Index convention: ξ : ℕ → ℝ, 0-indexed, ξ 0 is the first maximum; even index = maxima, odd = minima.
- Monotonicity: StrictMonoOn / StrictAntiOn on closed intervals `Icc`; first piece `Icc 0 (ξ 0)`.
- Extrema: ξ 0 is a global max via `IsMaxOn` on `Ici 0` (non-strict as stated, "maximum"). Strict minimum of ξ(2k+1) over `Ici (ξ (2k))` and strict maximum of ξ(2k+2) over `Ici (ξ (2k+1))` stated as strict inequality for all other points of those rays.
- Limits: `Tendsto` along `atTop` on ℕ (ratios) and on ℝ (mass); `-exp(-π/√7)` written `-Real.exp (-Real.pi / Real.sqrt 7)`; `exp(2π/√7)` as `Real.exp (2 * Real.pi / Real.sqrt 7)`.
- Quotients of mass deviations are real division (Lean's x/0 = 0 junk value is harmless since the deviations are nonzero by the strict inequalities with singular mass).
- Bounds for k ≥ 5: closed intervals [9.2, 12.9] and [-0.42, -0.21].
- (iv): for each n : ℕ, index shift n+5 → n+6, absolute difference ≤ (23/10)(21/50)^n resp. (3/20)(21/50)^n, using exact rationals.
- Numerals like 6.4507514 are real literals (OfScientific).
- Not compiled; the theorem is `sorry`.
