# Item 47

**Area:** F7

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Eqs. (10.61)–(10.63), verbatim from Capozziello & Salzano 2009 Eqs. (62)–(64): curvature terms of the y-redshift angular-diameter-distance coefficients D³_{A,y}, D⁴_{A,y} wrong

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- it is false that (`BambaDA3ClaimPast`)

Program definitions in this claim:

- `BambaDA3ClaimPast` — CLAIM, not pinned; the source-dependent data written inline (printed formula, order of the printed series) agree with an independent blind second reading of the source (`Checked.Trust.Transcriptions.agree_BambaDA3ClaimPast`); the quantifiers and hypotheses are the program's formalisation: means for every `K : ℝ`, for every `a : ℝ → ℝ`, for every `t₀ : ℝ`, if `ContDiff ℝ ⊤ a`, then if for every `t : ℝ`, `0 < a t`, then if `0 < hubble a t₀`, then `(fun t => remA printedDA3 (fun x x_1 x_2 x_3 x_4 => 0) K a t₀ t) =o[nhdsWithin t₀ (Set.Iio t₀)] fun t => yred a t₀ t ^ 4`
- `DA1 q` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_DA1`); its name is not checked (for `q : ℝ`): is defined as `-(1 / 2) * (1 + q)`
- `DA2 q j Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_DA2`); its name is not checked (for `q : ℝ`, `j : ℝ`, `Ω : ℝ`): is defined as `-(1 / 6) * (-q - 3 * q ^ 2 + j + Ω)`
- `angDist K a t₀ t` — **PINNED** (pin theorem `angDistSpec_pins`): phrase (hand-written, linted): the angular diameter distance in FLRW with curvature with the spatial curvature constant `K`, the scale factor `a`, the observation time `t₀` and the emission time `t` (positive curvature constant means closed, negative means open; scale factor at emission times the transverse distance of the comoving distance; positive `K` is closed and negative `K` is open); by definition, `angDist K a t₀ t` is `lumDist K a t₀ t / (1 + redshift a t₀ t) ^ 2`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): phrase (hand-written, linted): the cosmographic coefficient with the derivative order of the coefficient `n`, the scale factor `a` and the time of evaluation `t` (`n`-th time derivative of the scale factor over the scale factor divided by the `n`-th power of the Hubble rate; orders 0 and 1 coefficients are one; The order 2 coefficient is minus the deceleration parameter usually written q; The order 3 coefficient is the jerk parameter usually written j; The order 4 coefficient is the snap parameter usually written s; The order 5 coefficient is the lerk parameter usually written l); by definition, `cosmoCoeff n a t` is `iteratedDeriv n a t / (a t * hubble a t ^ n)`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «orders 0 and 1 coefficients are one» only assuming `a t ≠ 0`; `deriv a t ≠ 0`, «The order 2 coefficient is minus the deceleration parameter usually written q» only assuming `a t ≠ 0`
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): phrase (hand-written, linted): the deceleration parameter with the scale factor `a` and the cosmic time of evaluation `t` (minus acceleration times scale factor over velocity squared; minus the second time derivative times the scale factor divided by the squared first time derivative; negative value means accelerating expansion); by definition, `decel a t` is `-(deriv (deriv a) t * a t) / deriv a t ^ 2`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «negative value means accelerating expansion» only assuming `0 < a t`; `0 < deriv a t`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): phrase (hand-written, linted): the Hubble rate with the scale factor `a` and the cosmic time of evaluation `t` (logarithmic derivative of the scale factor with respect to cosmic time; positive for expansion and negative for contraction); by definition, `hubble a t` is `deriv a t / a t`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «logarithmic derivative of the scale factor with respect to cosmic time» only assuming `0 < a t`; `DifferentiableAt ℝ a t`, «positive for expansion and negative for contraction» only assuming `0 < a t`; `0 < deriv a t`, «positive for expansion and negative for contraction» only assuming `0 < a t`; `deriv a t < 0`
- `omega0 K a t₀` — **PINNED** (pin theorem `omega0Spec_pins`): phrase (hand-written, linted): the present total density parameter Ω0 with the spatial curvature constant `K`, the scale factor `a` and the observation time `t₀` (one plus curvature term, positive curvature constant gives above one; total density parameter and not the matter fraction alone; equals one for zero curvature); by definition, `omega0 K a t₀` is `1 + K / (hubble a t₀ ^ 2 * a t₀ ^ 2)`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «one plus curvature term, positive curvature constant gives above one», «one plus curvature term, positive curvature constant gives above one» only assuming `0 < K`; `hubble a t₀ ≠ 0`; `a t₀ ≠ 0`, «equals one for zero curvature»
- `printedDA3 q j s Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedDA3`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `Ω : ℝ`): is defined as `-(1 / 24) * (-2 * q + 3 * q ^ 2 + 15 * q ^ 3 - j - 10 * q * j - s + 2 * Ω)`
- `remA D3 D4 K a t₀ t` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_remA`) (for `D3 : ℝ → ℝ → ℝ → ℝ → ℝ`, `D4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ`, `K : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `hubble a t₀ * angDist K a t₀ t - yred a t₀ t * (1 + DA1 (decel a t₀) * yred a t₀ t + DA2 (decel a t₀) (cosmoCoeff 3 a t₀) (omega0 K a t₀) * yred a t₀ t ^ 2 + D3 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (omega0 K a t₀) * yred a t₀ t ^ 3 + D4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) (omega0 K a t₀) * yred a t₀ t ^ 4)`
- `yred a t₀ t` — **PINNED** (pin theorem `yRedSpec_pins`): phrase (hand-written, linted): the y redshift with the scale factor `a`, the observation time `t₀` and the emission time `t` (positive for redshift, negative for blueshift; one minus the scale factor at emission over that at observation; always below one for a positive scale factor); by definition, `yred a t₀ t` is `redshift a t₀ t / (1 + redshift a t₀ t)`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «positive for redshift, negative for blueshift» only assuming `0 < a t`; `0 < a t₀`; `0 < redshift a t₀ t`, «positive for redshift, negative for blueshift» only assuming `0 < a t`; `0 < a t₀`; `redshift a t₀ t < 0`, «one minus the scale factor at emission over that at observation» only assuming `a t ≠ 0`; `a t₀ ≠ 0`, «always below one for a positive scale factor» only assuming `0 < a t`; `0 < a t₀`

## Author's paraphrase (hand-written; checked only by prose rules)

The review's claim (10.61) is false even for past emission only (`t → t₀⁻`): see
`bambaDA3Claim_false`.

## Formal statement (Lean 4)

```lean
theorem bambaDA3ClaimPast_false : ¬ BambaDA3ClaimPast := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaA.angDist`, `Cosmography.BambaK.omega0`, `Cosmography.BambaY.yred`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.BambaA.BambaDA3ClaimPast`, `Cosmography.BambaA.DA1`, `Cosmography.BambaA.DA2`, `Cosmography.BambaA.printedDA3`, `Cosmography.BambaA.remA`, `Cosmography.BambaK.lumDist`, `Cosmography.BambaY.comoving`, `Cosmography.CCS.D3`, `Cosmography.Transverse.transverse`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, angDist, omega0, yred, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): BambaDA3ClaimPast², DA1², DA2², printedDA3².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3, n = 4, n = 5.
- Source file: `Checked/Cosmography/BambaAngular.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 47
