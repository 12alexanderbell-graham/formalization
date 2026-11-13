# Item 14

**Area:** Certified numbers of the findings

**Source:** Capozziello, Lazkoz, Salzano, PRD 84, 124061 (2011), arXiv:1104.3096 (v1 and v2), Eq. (22): flat matter + CPL l₀, w_a² term missing a factor 9

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `w₀ : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. the scale factor `a` obeys the flat matter plus CPL dark energy Friedmann expansion law with the present matter density parameter `Ω := 3 / 10`, the present dark energy equation of state `w₀`, the equation of state evolution parameter `wₐ := -1 / 2` and the observation time `t₀` (spatially flat universe with dust and separately conserved dark energy; redshift z is measured from `t₀`; `Ω := 3 / 10` is the present matter density parameter; holds on a whole neighbourhood of `t₀`; present Hubble rate is positive so the universe is expanding)
2. `ContDiffAt ℝ 5 a t₀`

**then**

- `RoundsTo (cosmoCoeff 5 a t₀ - printedCLSL0 (3 / 10) w₀ (-1 / 2)) 2.345 3`

Program definitions in this claim:

- `IsFlatCPL Ω w₀ wₐ a t₀` — **PINNED** (pin theorem `flatCPL_pins`): phrase (hand-written, linted): the scale factor `a` obeys the flat matter plus CPL dark energy Friedmann expansion law with the present matter density parameter `Ω`, the present dark energy equation of state `w₀`, the equation of state evolution parameter `wₐ` and the observation time `t₀` (spatially flat universe with dust and separately conserved dark energy; redshift z is measured from `t₀`; `Ω` is the present matter density parameter; holds on a whole neighbourhood of `t₀`; present Hubble rate is positive so the universe is expanding); by definition, means (`0 < hubble a t₀`) and (`∀ᶠ (t : ℝ) in nhds t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧ hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + (1 - Ω) * (1 + redshift a t₀ t) ^ (3 * (1 + w₀ + wₐ)) * Real.exp (-(3 * wₐ * redshift a t₀ t) / (1 + redshift a t₀ t)))`). Phrase lines proved in Lean (statements in PHRASE_LINES.md): «present Hubble rate is positive so the universe is expanding» only assuming the scale factor `a` obeys the flat matter plus CPL dark energy Friedmann expansion law with the present matter density parameter `Ω`, the present dark energy equation of state `w₀`, the equation of state evolution parameter `wₐ` and the observation time `t₀` (spatially flat universe with dust and separately conserved dark energy; redshift z is measured from `t₀`; `Ω` is the present matter density parameter; holds on a whole neighbourhood of `t₀`; present Hubble rate is positive so the universe is expanding)
- `RoundsTo x d k` — MATH, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_RoundsTo`) (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): phrase (hand-written, linted): the cosmographic coefficient with the derivative order of the coefficient `n`, the scale factor `a` and the time of evaluation `t` (`n`-th time derivative of the scale factor over the scale factor divided by the `n`-th power of the Hubble rate; orders 0 and 1 coefficients are one; The order 2 coefficient is minus the deceleration parameter usually written q; The order 3 coefficient is the jerk parameter usually written j; The order 4 coefficient is the snap parameter usually written s; The order 5 coefficient is the lerk parameter usually written l); by definition, `cosmoCoeff n a t` is `iteratedDeriv n a t / (a t * hubble a t ^ n)`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «orders 0 and 1 coefficients are one» only assuming `a t ≠ 0`; `deriv a t ≠ 0`, «The order 2 coefficient is minus the deceleration parameter usually written q» only assuming `a t ≠ 0`
- `printedCLSL0 Ω w₀ wₐ` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedCLSL0`); its name is not checked (for `Ω : ℝ`, `w₀ : ℝ`, `wₐ : ℝ`): is defined as `35 / 2 + (1 - Ω) / 4 * (213 + (7 - Ω) * wₐ) * wₐ + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀ + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2 + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3 + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4`

## Author's paraphrase (hand-written; checked only by prose rules)

At `Ω = 0.3`, `wₐ = −0.5` and every `w₀`, every flat CPL model has `l₀` exceeding the printed
formula by `2.345`.

## Formal statement (Lean 4)

```lean
theorem F2_error (w₀ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hL : CPL.IsFlatCPL (3 / 10) w₀ (-1 / 2) a t₀)
    (hs : ContDiffAt ℝ 5 a t₀) :
    RoundsTo (cosmoCoeff 5 a t₀ - printedCLSL0 (3 / 10) w₀ (-1 / 2)) 2.345 3 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.CPL.IsFlatCPL`, `Records.printedCLSL0`, `Cosmography.hubble`, `Cosmography.redshift`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, IsFlatCPL.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): printedCLSL0².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `F2_error`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): IsFlatCPL: Ω = 3/10, wₐ = -1/2; RoundsTo: d = 2.345, k = 3; cosmoCoeff: n = 5; printedCLSL0: Ω = 3/10, wₐ = -1/2.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 14
