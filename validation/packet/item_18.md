# Item 18

**Area:** F11

**Source:** Demianski, Piedipalumbo, Sawant, Amati, A&A 598, A113 (2017), arXiv:1609.09631 (v1, v2), p. 3: flat z-series D⁴_L has −105q₀⁴ (should be +105q₀⁴) and D⁴_A (Eq. (23)) has +137j₀ (should be −137j₀); the D⁴_L error is reprinted in Lusso et al., A&A 628, L4 (2019), arXiv:1907.07692 (v1–v4), the quasar+SN+GRB paper claiming > 4σ tension with flat ΛCDM

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- it is false that (`DemDLzClaim`)

Program definitions in this claim:

- `DL1z q` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_DL1z`); its name is not checked (for `q : ℝ`): is defined as `-(1 / 2) * (-1 + q)`
- `DL2z q j k` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_DL2z`); its name is not checked (for `q : ℝ`, `j : ℝ`, `k : ℝ`): is defined as `-(1 / 6) * (1 - q - 3 * q ^ 2 + j + k)`
- `DL3z q j s k` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_DL3z`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `k : ℝ`): is defined as `1 / 24 * (2 - 2 * q - 15 * q ^ 2 - 15 * q ^ 3 + 5 * j + 10 * q * j + s + 2 * k * (1 + 3 * q))`
- `DemDLzClaim` — CLAIM, not pinned; the source-dependent data written inline (printed formula, order of the printed series) agree with an independent blind second reading of the source (`Checked.Trust.Transcriptions.agree_DemDLzClaim`); the quantifiers and hypotheses are the program's formalisation: means for every `a : ℝ → ℝ`, for every `t₀ : ℝ`, if `ContDiff ℝ ⊤ a`, then if for every `t : ℝ`, `0 < a t`, then if `0 < hubble a t₀`, then `(fun t => remLz (fun q j s l x => demDL4 q j s l) 0 a t₀ t) =o[nhds t₀] fun t => redshift a t₀ t ^ 5`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): phrase (hand-written, linted): the cosmographic coefficient with the derivative order of the coefficient `n`, the scale factor `a` and the time of evaluation `t` (`n`-th time derivative of the scale factor over the scale factor divided by the `n`-th power of the Hubble rate; orders 0 and 1 coefficients are one; The order 2 coefficient is minus the deceleration parameter usually written q; The order 3 coefficient is the jerk parameter usually written j; The order 4 coefficient is the snap parameter usually written s; The order 5 coefficient is the lerk parameter usually written l); by definition, `cosmoCoeff n a t` is `iteratedDeriv n a t / (a t * hubble a t ^ n)`
- `curvK K a t₀` — **PINNED** (pin theorem `curvKSpec_pins`): phrase (hand-written, linted): the dimensionless spatial curvature parameter with the spatial curvature constant `K`, the scale factor `a` and the observation time `t₀` (has sign of curvature constant, minus the curvature density parameter; total density parameter minus one; positive for closed and negative for open); by definition, `curvK K a t₀` is `K / (hubble a t₀ ^ 2 * a t₀ ^ 2)`
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): phrase (hand-written, linted): the deceleration parameter with the scale factor `a` and the cosmic time of evaluation `t` (minus acceleration times scale factor over velocity squared; minus the second time derivative times the scale factor divided by the squared first time derivative; negative value means accelerating expansion); by definition, `decel a t` is `-(deriv (deriv a) t * a t) / deriv a t ^ 2`
- `demDL4 q j s l` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_demDL4`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `1 / 120 * (-6 + 6 * q + 81 * q ^ 2 + 165 * q ^ 3 - 105 * q ^ 4 - 110 * q * j + -105 * q ^ 2 * j - 15 * q * s - 27 * j + 10 * j ^ 2 - 11 * s - l)`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): phrase (hand-written, linted): the Hubble rate with the scale factor `a` and the cosmic time of evaluation `t` (logarithmic derivative of the scale factor with respect to cosmic time; positive for expansion and negative for contraction); by definition, `hubble a t` is `deriv a t / a t`
- `lumDist K a t₀ t` — **PINNED** (pin theorem `lumDistSpec2_pins`): phrase (hand-written, linted): the luminosity distance in FLRW with curvature with the spatial curvature constant `K`, the scale factor `a`, the observation time `t₀` and the emission time `t` (positive curvature constant means closed, negative means open; units in which the speed of light is one; positive `K` is closed and negative `K` is open); by definition, `lumDist K a t₀ t` is `a t₀ * (1 + redshift a t₀ t) * transverse K (comoving a t₀ t)`
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): phrase (hand-written, linted): the cosmological redshift with the scale factor `a`, the observation time `t₀` and the emission time `t` (positive when emission precedes observation in an expanding universe; one plus redshift is the scale factor at observation over that at emission; negative redshift is blueshift; zero when emission and observation coincide); by definition, `redshift a t₀ t` is `a t₀ / a t - 1`
- `remLz D4 K a t₀ t` — COMPOSITE, not pinned, so only the formula shown is checked, not its name (for `D4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ`, `K : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `hubble a t₀ * lumDist K a t₀ t - seriesZ (DL1z (decel a t₀)) (DL2z (decel a t₀) (cosmoCoeff 3 a t₀) (curvK K a t₀)) (DL3z (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (curvK K a t₀)) (D4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) (curvK K a t₀)) (redshift a t₀ t)`
- `seriesZ d1 d2 d3 d4 z` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_seriesZ`) (for `d1 : ℝ`, `d2 : ℝ`, `d3 : ℝ`, `d4 : ℝ`, `z : ℝ`): is defined as `z * (1 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4)`

## Author's paraphrase (hand-written; checked only by prose rules)

The flat `d_L(z)` series printed by Demianski et al. 2017 (and Lusso et al. 2019), with its printed
`D⁴_L`, is not `d_L + o(z⁵)` for every analytic, everywhere positive flat scale factor with `H₀ > 0`:
the claim is false.

## Formal statement (Lean 4)

```lean
theorem demDLzClaim_false : ¬ DemDLzClaim := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaK.lumDist`, `Cosmography.BambaZ.curvK`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.BambaZ.DL1z`, `Cosmography.BambaZ.DL2z`, `Cosmography.BambaZ.DL3z`, `Cosmography.DemianskiZ.DemDLzClaim`, `Cosmography.DemianskiZ.demDL4`, `Cosmography.BambaY.comoving`, `Cosmography.BambaZ.remLz`, `Cosmography.BambaZ.seriesZ`, `Cosmography.Transverse.transverse`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, lumDist, curvK, decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): DL1z², DL2z², DL3z², DemDLzClaim², demDL4².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): lumDist: K = 0; cosmoCoeff: n = 3, n = 4, n = 5; curvK: K = 0.
- Source file: `Checked/Cosmography/DemianskiZ.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 18
