# Item 40

**Area:** F1

**Source:** Aviles, Gruber, Luongo, Quevedo, PRD 86, 123516 (2012), arXiv:1204.2007 (v1 and v2), Eq. (15): misprinted ΛCDM l₀ and m₀

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`:

**assuming**

1. `0 < Ω`
2. `Ω < 1`
3. `3 * Ω ^ 2 + 2 * Ω - 2 ≠ 0`

**then**

- it is false that (for every `a : ℝ → ℝ`, for every `t₀ : ℝ`, if the scale factor `a` obeys the flat ΛCDM Friedmann expansion law with the present matter density parameter `Ω` and the observation time `t₀` (spatially flat universe with dust and a cosmological constant; `Ω` is the present matter density parameter; holds on a whole neighbourhood of `t₀`; present Hubble rate is positive so the universe is expanding), then if `ContDiffAt ℝ 6 a t₀`, then `cosmoCoeff 6 a t₀ = 1 - 27 / 2 * Ω ^ 2 - 81 * Ω ^ 2 - 81 / 2 * Ω ^ 3`)

Program definitions in this claim:

- `IsFlatLCDM Ω a t₀` — **PINNED** (pin theorem `flatLCDMSpec2_pins`): phrase (hand-written, linted): the scale factor `a` obeys the flat ΛCDM Friedmann expansion law with the present matter density parameter `Ω` and the observation time `t₀` (spatially flat universe with dust and a cosmological constant; `Ω` is the present matter density parameter; holds on a whole neighbourhood of `t₀`; present Hubble rate is positive so the universe is expanding); by definition, means (`0 < hubble a t₀`) and (`∀ᶠ (t : ℝ) in nhds t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧ hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω)`). Phrase lines proved in Lean (statements in PHRASE_LINES.md): «present Hubble rate is positive so the universe is expanding» only assuming the scale factor `a` obeys the flat ΛCDM Friedmann expansion law with the present matter density parameter `Ω` and the observation time `t₀` (spatially flat universe with dust and a cosmological constant; `Ω` is the present matter density parameter; holds on a whole neighbourhood of `t₀`; present Hubble rate is positive so the universe is expanding)
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): phrase (hand-written, linted): the cosmographic coefficient with the derivative order of the coefficient `n`, the scale factor `a` and the time of evaluation `t` (`n`-th time derivative of the scale factor over the scale factor divided by the `n`-th power of the Hubble rate; orders 0 and 1 coefficients are one; The order 2 coefficient is minus the deceleration parameter usually written q; The order 3 coefficient is the jerk parameter usually written j; The order 4 coefficient is the snap parameter usually written s; The order 5 coefficient is the lerk parameter usually written l); by definition, `cosmoCoeff n a t` is `iteratedDeriv n a t / (a t * hubble a t ^ n)`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «orders 0 and 1 coefficients are one» only assuming `a t ≠ 0`; `deriv a t ≠ 0`, «The order 2 coefficient is minus the deceleration parameter usually written q» only assuming `a t ≠ 0`

## Author's paraphrase (hand-written; checked only by prose rules)

The printed m₀ of Eq. (15) is false at every Ω ∈ (0,1) where it differs from the true
polynomial, i.e. every Ω ∈ (0,1) except the root (√7 − 1)/3 of 3Ω² + 2Ω − 2 = 0.

## Formal statement (Lean 4)

```lean
theorem printedM0_false_at {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) (hr : 3 * Ω ^ 2 + 2 * Ω - 2 ≠ 0) :
    ¬ ∀ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ → ContDiffAt ℝ 6 a t₀ →
      cosmoCoeff 6 a t₀ = 1 - 27 / 2 * Ω ^ 2 - 81 * Ω ^ 2 - 81 / 2 * Ω ^ 3 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.IsFlatLCDM`, `Cosmography.Aviles.cosmoCoeff`, `Cosmography.hubble`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatLCDM, cosmoCoeff.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `printedM0_false_at`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 6.
- Source file: `Checked/Cosmography/LCDMWitness.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 40
