# Item 37

**Area:** F5

**Source:** Cattoën & Visser, Class. Quantum Grav. 24, 5985 (2007), arXiv:0710.1887v1, Eq. (59) (also gr-qc/0703122 v1–v3 and arXiv:0809.0537v1 Eq. (32)): deceleration-distance y² coefficient 1/12 should be 1/24

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- it is false that (`CVdQClaimPast`)

Program definitions in this claim:

- `CVdQClaimPast` — CLAIM, not pinned; the source-dependent data written inline (printed formula, order of the printed series) agree with an independent blind second reading of the source (`Checked.Trust.Transcriptions.agree_CVdQClaimPast`); the quantifiers and hypotheses are the program's formalisation: means for every `a : ℝ → ℝ`, for every `t₀ : ℝ`, if `ContDiff ℝ ⊤ a`, then if for every `t : ℝ`, `0 < a t`, then if `0 < hubble a t₀`, then `(fun t => remainderQ printedQ2 a t₀ t) =o[nhdsWithin t₀ (Set.Iio t₀)] fun t => yred a t₀ t ^ 3`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)
- `dQFlat a t₀ t` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_dQFlat`); its name is not checked (for `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `lumDistFlat a t₀ t / (1 + redshift a t₀ t) ^ (3 / 2)`
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): the deceleration parameter −a″(t)·a(t)/a′(t)² of the scale factor `a` at time `t`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): the Hubble rate a′(t)/a(t) of the scale factor `a` at time `t`
- `lumDistFlat a t₀ t` — **PINNED** (pin theorem `lumDistFlat_pins`): the spatially flat luminosity distance a(t₀)·(1 + z)·χ, at observation time `t₀`, of a source emitting at time `t` (scale factor `a`, c = 1, χ the comoving radial distance)
- `printedQ2 q j Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedQ2`); its name is not checked (for `q : ℝ`, `j : ℝ`, `Ω : ℝ`): is defined as `1 / 12 * (3 - 2 * q + 12 * q ^ 2 - 4 * (j + Ω))`
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): the redshift a(`t₀`)/a(`t`) − 1, observed at time `t₀`, of light emitted at time `t` (scale factor `a`)
- `remainderQ D2 a t₀ t` — COMPOSITE, not pinned, so only the formula shown is checked, not its name (for `D2 : ℝ → ℝ → ℝ → ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `hubble a t₀ * dQFlat a t₀ t - seriesQ (D2 (decel a t₀) (cosmoCoeff 3 a t₀) 1) (decel a t₀) (yred a t₀ t)`
- `seriesQ d2 q y` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_seriesQ`) (for `d2 : ℝ`, `q : ℝ`, `y : ℝ`): is defined as `y * (1 - q / 2 * y + d2 * y ^ 2)`
- `yred a t₀ t` — **PINNED** (pin theorem `yRedSpec_pins`): the y-redshift z/(1 + z), observed at time `t₀`, of light emitted at time `t` (scale factor `a`)

## Author's paraphrase (hand-written; checked only by prose rules)

The past-only reading is false (flat de Sitter).

## Formal statement (Lean 4)

```lean
theorem cvdQClaimPast_false : ¬ CVdQClaimPast := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaY.lumDistFlat`, `Cosmography.BambaY.yred`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.CVdQ.CVdQClaimPast`, `Cosmography.CVdQ.dQFlat`, `Cosmography.CVdQ.printedQ2`, `Cosmography.BambaY.comoving`, `Cosmography.CCS.D2`, `Cosmography.CVdQ.remainderQ`, `Cosmography.CVdQ.seriesQ`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, lumDistFlat, yred, decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): CVdQClaimPast², dQFlat², printedQ2².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3.
- Source file: `Checked/Cosmography/CVdQ.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 37
