# Interpretive choices (blind restatement)

- Scale factor `a : ℝ → ℝ`, observation time `t₀`, source emission times `t₃ < t₂ < t₁ < t₀` (higher redshift = earlier). Sources are placed by their redshift: `1 + redshift a t₀ tᵢ = √2, 2√2, 4√2` (hz1..hz3), not by assuming specific times.
- Expansion law `hubble a t = H₀ √(Ωm (1+z)³ + 1 − Ωm)` with `1+z = a t₀ / a t` (i.e. `1 + redshift a t₀ t`) is assumed for all `t ∈ [t₃, t₀]` (the epoch from the earliest source to today). Not assumed outside.
- `H₀ > 0` assumed; `Ωm ∈ [0,1]` as `Set.Icc 0 1`.
- Regularity: `a t > 0` and `DifferentiableAt ℝ a t` for all `t ∈ [t₃, t₀]` (needed so `deriv` is genuine and `1/a` is positive on the comoving integration range; makes `lumDistFlat > 0`). No continuity of the derivative or integrability is assumed separately.
- Fit: `logPolyDL3 a₂ a₃ H z` evaluated at `z = redshift a t₀ tᵢ`; any `a₂ a₃`, `H > 0`. Positivity of the fit at the three redshifts is an explicit hypothesis (hp1..hp3).
- Distance modulus: `5 * logb 10 d` (additive constant dropped, absorbed by the offset). The offset is existentially quantified once (`∃ Δ`) and shared by all three sources.
- "Within 0.05 mag": non-strict `|μ_fit − μ_true − Δ| ≤ 0.05` (`0.05` real literal).
- Junk values of `Real.logb`: `logb 10 d` is junk for `d ≤ 0`. For the fit, positivity hypotheses avoid it; for the true luminosity distance, positivity follows from `a > 0`, `t < t₀` and `H₀ > 0`-driven expansion (not an explicit hypothesis; derivable from hpos). Inside `logPolyDL3`, `logb 10 (1+z)` has `1+z ∈ {√2, 2√2, 4√2} > 0`, so no junk.
- Conclusion strict: `a₃ > 13/5`.
- Used an auxiliary def `blindModulus`; the open namespaces are those in the brief (`BambaY`, `B1` opened but may be unused).
