# Item 69

**Area:** F1

**Source:** Aviles, Gruber, Luongo, Quevedo, PRD 86, 123516 (2012), arXiv:1204.2007 (v1 and v2), Eq. (15): misprinted ΛCDM l₀ and m₀

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`:

**assuming**

1. `0 < Ω`
2. `Ω < 1`
3. `3 * Ω ^ 2 + 2 * Ω - 2 ≠ 0`

**then**

- it is false that (for every `a : ℝ → ℝ`, for every `t₀ : ℝ`, if the scale factor `a` obeys the flat ΛCDM Friedmann expansion law with matter fraction given by the present matter density parameter `Ω` on some neighbourhood of the observation time `t₀`, with a positive Hubble rate at `t₀` and a positive, differentiable scale factor on that neighbourhood, then if `ContDiffAt ℝ 6 a t₀`, then `cosmoCoeff 6 a t₀ = 1 - 27 / 2 * Ω ^ 2 - 81 * Ω ^ 2 - 81 / 2 * Ω ^ 3`)

Program definitions in this claim:

- `IsFlatLCDM Ω a t₀` — **PINNED** (pin theorem `flatLCDMSpec2_pins`): phrase (hand-written, linted): the scale factor `a` obeys the flat ΛCDM Friedmann expansion law with matter fraction given by the present matter density parameter `Ω` on some neighbourhood of the observation time `t₀`, with a positive Hubble rate at `t₀` and a positive, differentiable scale factor on that neighbourhood; by definition, means (`0 < hubble a t₀`) and (`∀ᶠ (t : ℝ) in nhds t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧ hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω)`)
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): phrase (hand-written, linted): the cosmographic coefficient of the scale factor `a` at the time of evaluation `t` for the derivative order of the coefficient `n` (j, s, l, m for the orders 3, 4, 5, 6; the deceleration parameter is minus the order 2 coefficient); by definition, `cosmoCoeff n a t` is `iteratedDeriv n a t / (a t * hubble a t ^ n)`

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

## Your answers: use ANSWER_FORM.md, item 69
