# Item 33

**Area:** F4

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421 (v1, v2, v3), Eq. (10.54): y-redshift luminosity-distance coefficient D²_{L,y} has the wrong overall sign

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- it is false that (`BambaD2yClaim`)

Program definitions in this claim:

- `BambaD2yClaim` — CLAIM, not pinned; the source-dependent data written inline (printed formula, order of the printed series) agree with an independent blind second reading of the source (`Checked.Trust.Transcriptions.agree_BambaD2yClaim`); the quantifiers and hypotheses are the program's formalisation: means for every `a : ℝ → ℝ`, for every `t₀ : ℝ`, if `ContDiff ℝ ⊤ a`, then if for every `t : ℝ`, `0 < a t`, then if `0 < hubble a t₀`, then `(fun t => remainderY printedD2y a t₀ t) =o[nhds t₀] fun t => yred a t₀ t ^ 3`
- `D1y q` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_D1y`); its name is not checked (for `q : ℝ`): is defined as `-(1 / 2) * (-3 + q)`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): the deceleration parameter −a″(t)·a(t)/a′(t)² of the scale factor `a` at time `t`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): the Hubble rate a′(t)/a(t) of the scale factor `a` at time `t`
- `lumDistFlat a t₀ t` — **PINNED** (pin theorem `lumDistFlat_pins`): the spatially flat luminosity distance a(t₀)·(1 + z)·χ, at observation time `t₀`, of a source emitting at time `t` (scale factor `a`, c = 1, χ the comoving radial distance)
- `printedD2y q j Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedD2y`); its name is not checked (for `q : ℝ`, `j : ℝ`, `Ω : ℝ`): is defined as `-(1 / 6) * (12 - 5 * q + 3 * q ^ 2 - j - Ω)`
- `remainderY D2 a t₀ t` — COMPOSITE, not pinned, so only the formula shown is checked, not its name (for `D2 : ℝ → ℝ → ℝ → ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `hubble a t₀ * lumDistFlat a t₀ t - seriesY (D2 (decel a t₀) (cosmoCoeff 3 a t₀) 1) (decel a t₀) (yred a t₀ t)`
- `seriesY d2 q y` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_seriesY`) (for `d2 : ℝ`, `q : ℝ`, `y : ℝ`): is defined as `y * (1 + D1y q * y + d2 * y ^ 2)`
- `yred a t₀ t` — **PINNED** (pin theorem `yRedSpec_pins`): the y-redshift z/(1 + z), observed at time `t₀`, of light emitted at time `t` (scale factor `a`)

## Author's paraphrase (hand-written; checked only by prose rules)

The printed claim is false (witness: flat de Sitter, `a = exp`, `t₀ = 0`).

## Formal statement (Lean 4)

```lean
theorem bambaD2yClaim_false : ¬ BambaD2yClaim := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaY.lumDistFlat`, `Cosmography.BambaY.yred`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.BambaY.BambaD2yClaim`, `Cosmography.BambaY.D1y`, `Cosmography.BambaY.printedD2y`, `Cosmography.BambaY.comoving`, `Cosmography.BambaY.remainderY`, `Cosmography.BambaY.seriesY`, `Cosmography.CCS.D2`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, lumDistFlat, yred, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): BambaD2yClaim², D1y², printedD2y².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3.
- Source file: `Checked/Cosmography/BambaDLy.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 33
