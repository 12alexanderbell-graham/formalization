# Item 46

**Area:** F8

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Eqs. (10.38)–(10.51), verbatim from Capozziello & Salzano 2009 (arXiv:0902.0088) Eqs. (31)–(52): z-redshift d_L and d_A fourth-order coefficients D⁴_L, D⁴_A miss the curvature-squared term

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- it is false that (`BambaDAzClaimPast`)

Program definitions in this claim:

- `BambaDAzClaimPast` — CLAIM, not pinned, so only the formula shown is checked, not its name: means for every `K : ℝ`, for every `a : ℝ → ℝ`, for every `t₀ : ℝ`, if `ContDiff ℝ ⊤ a`, then if for every `t : ℝ`, `0 < a t`, then if `0 < hubble a t₀`, then `(fun t => remAz printedDA4z K a t₀ t) =o[nhdsWithin t₀ (Set.Iio t₀)] fun t => redshift a t₀ t ^ 5`
- `DA1z q` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_DA1z`); its name is not checked (for `q : ℝ`): is defined as `-(1 / 2) * (3 + q)`
- `DA2z q j k` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_DA2z`); its name is not checked (for `q : ℝ`, `j : ℝ`, `k : ℝ`): is defined as `1 / 6 * (11 + 7 * q + 3 * q ^ 2 - j - k)`
- `DA3z q j s k` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_DA3z`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `k : ℝ`): is defined as `-(1 / 24) * (50 + 46 * q + 39 * q ^ 2 + 15 * q ^ 3 - 13 * j - 10 * q * j - s - 2 * k * (5 + 3 * q))`
- `angDist K a t₀ t` — **PINNED** (pin theorem `angDistSpec_pins`): the angular-diameter distance d_L/(1 + z)², at observation time `t₀`, of a source emitting at time `t`, in the FLRW model with scale factor `a` and curvature constant `K` (c = 1)
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)
- `curvK K a t₀` — **PINNED** (pin theorem `curvKSpec_pins`): the curvature parameter K/(H₀²·a₀²) at time `t₀` for curvature constant `K` and scale factor `a` (c = 1; equal to −Ω_k)
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): the deceleration parameter −a″(t)·a(t)/a′(t)² of the scale factor `a` at time `t`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): the Hubble rate a′(t)/a(t) of the scale factor `a` at time `t`
- `printedDA4z q j s l k` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedDA4z`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`, `k : ℝ`): is defined as `1 / 120 * (274 + 326 * q + 411 * q ^ 2 + 315 * q ^ 3 + 105 * q ^ 4 - 210 * q * j - 105 * q ^ 2 * j - 15 * q * s + -137 * j + 10 * j ^ 2 - 21 * s - l - 5 * k * (17 + 20 * q + 9 * q ^ 2 - 2 * j))`
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): the redshift a(`t₀`)/a(`t`) − 1, observed at time `t₀`, of light emitted at time `t` (scale factor `a`)
- `remAz D4 K a t₀ t` — COMPOSITE, not pinned, so only the formula shown is checked, not its name (for `D4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ`, `K : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `hubble a t₀ * angDist K a t₀ t - seriesZ (DA1z (decel a t₀)) (DA2z (decel a t₀) (cosmoCoeff 3 a t₀) (curvK K a t₀)) (DA3z (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (curvK K a t₀)) (D4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) (curvK K a t₀)) (redshift a t₀ t)`
- `seriesZ d1 d2 d3 d4 z` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_seriesZ`) (for `d1 : ℝ`, `d2 : ℝ`, `d3 : ℝ`, `d4 : ℝ`, `z : ℝ`): is defined as `z * (1 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4)`

## Author's paraphrase (hand-written; checked only by prose rules)

The review's claim (10.45)–(10.51) is false even for past emission only (`t → t₀⁻`): see
`bambaDAzClaim_false`.

## Formal statement (Lean 4)

```lean
theorem bambaDAzClaimPast_false : ¬ BambaDAzClaimPast := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaA.angDist`, `Cosmography.BambaZ.curvK`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.BambaZ.BambaDAzClaimPast`, `Cosmography.BambaZ.DA1z`, `Cosmography.BambaZ.DA2z`, `Cosmography.BambaZ.DA3z`, `Cosmography.BambaZ.printedDA4z`, `Cosmography.BambaK.lumDist`, `Cosmography.BambaY.comoving`, `Cosmography.BambaZ.remAz`, `Cosmography.BambaZ.seriesZ`, `Cosmography.Transverse.transverse`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, angDist, curvK, decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): BambaDAzClaimPast, DA1z², DA2z², DA3z², printedDA4z².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3, n = 4, n = 5.
- Source file: `Checked/Cosmography/BambaZ.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 46
