# Item 19

**Area:** F3

**Source:** Capozziello, Cardone, Salzano, PRD 78, 063504 (2008), arXiv:0802.1583v2, App. A, Eq. (A2): lookback-distance z⁵ coefficient, 7/2 q₀⁴ should be 7/8 q₀⁴

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- it is false that (`CCSD4Claim`)

Program definitions in this claim:

- `CCSD4Claim` — CLAIM, not pinned; the source-dependent data written inline (printed formula, order of the printed series) agree with an independent blind second reading of the source (`Checked.Trust.Transcriptions.agree_CCSD4Claim`); the quantifiers and hypotheses are the program's formalisation: means for every `a : ℝ → ℝ`, for every `t₀ : ℝ`, if `ContDiff ℝ ⊤ a`, then if for every `t : ℝ`, `0 < a t`, then if `0 < hubble a t₀`, then `(fun t => remainder printedD4 a t₀ t) =o[nhds t₀] fun t => redshift a t₀ t ^ 5`
- `D1 q` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_D1`); its name is not checked (for `q : ℝ`): is defined as `-(1 + q / 2)`
- `D2 q j` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_D2`); its name is not checked (for `q : ℝ`, `j : ℝ`): is defined as `1 + q + q ^ 2 / 2 - j / 6`
- `D3 q j s` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_D3`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`): is defined as `-(1 + 3 / 2 * q + 3 / 2 * q ^ 2 + 5 / 8 * q ^ 3 - 1 / 2 * j - 5 / 12 * q * j - s / 24)`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): phrase (hand-written, linted): the `n`-th cosmographic coefficient of the scale factor `a` at time `t` (j, s, l, m for the orders 3, 4, 5, 6; the deceleration parameter is minus the order 2 coefficient); by definition, `cosmoCoeff n a t` is `iteratedDeriv n a t / (a t * hubble a t ^ n)`
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): phrase (hand-written, linted): the deceleration parameter of the scale factor `a` at time `t`; by definition, `decel a t` is `-(deriv (deriv a) t * a t) / deriv a t ^ 2`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): phrase (hand-written, linted): the Hubble rate of the scale factor `a` at time `t`; by definition, `hubble a t` is `deriv a t / a t`
- `printedD4 q j s l` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedD4`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `1 + 2 * q + 3 * q ^ 2 + 5 / 2 * q ^ 3 + 7 / 2 * q ^ 4 - 5 / 3 * q * j - 7 / 8 * q ^ 2 * j - j + j ^ 2 / 12 - 1 / 8 * q * s - s / 6 - l / 120`
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): phrase (hand-written, linted): the redshift at observation time `t₀` of light at emission time `t` (scale factor `a`); by definition, `redshift a t₀ t` is `a t₀ / a t - 1`
- `remainder D4 a t₀ t` — COMPOSITE, not pinned, so only the formula shown is checked, not its name (for `D4 : ℝ → ℝ → ℝ → ℝ → ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `hubble a t₀ * (t₀ - t) - series (D4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)) (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (redshift a t₀ t)`
- `series d4 q j s z` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_series`) (for `d4 : ℝ`, `q : ℝ`, `j : ℝ`, `s : ℝ`, `z : ℝ`): is defined as `z * (1 + D1 q * z + D2 q j * z ^ 2 + D3 q j s * z ^ 3 + d4 * z ^ 4)`

## Author's paraphrase (hand-written; checked only by prose rules)

The printed claim is false (witness: de Sitter, `a = exp`, `t₀ = 0`).

## Formal statement (Lean 4)

```lean
theorem ccsD4Claim_false : ¬ CCSD4Claim := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.CCS.CCSD4Claim`, `Cosmography.CCS.D1`, `Cosmography.CCS.D2`, `Cosmography.CCS.D3`, `Cosmography.CCS.printedD4`, `Cosmography.CCS.remainder`, `Cosmography.CCS.series`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): CCSD4Claim², D1², D2², D3², printedD4².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3, n = 4, n = 5.
- Source file: `Checked/Cosmography/CCSLookback.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 19
