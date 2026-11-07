# Item 36

**Area:** F1

**Source:** Aviles, Gruber, Luongo, Quevedo, PRD 86, 123516 (2012), arXiv:1204.2007 (v1 and v2), Eq. (15): misprinted ΛCDM l₀ and m₀

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`:

**assuming**

1. `0 < Ω`
2. `Ω < 1`
3. `3 * Ω ^ 2 + 2 * Ω - 2 ≠ 0`

**then**

- it is false that (for every `a : ℝ → ℝ`, for every `t₀ : ℝ`, if the scale factor `a` obeys the flat ΛCDM expansion law H = H₀·√(`Ω`·(1 + z)³ + 1 − `Ω`) on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0, z is the redshift observed at `t₀`, and a is positive and differentiable on that neighbourhood, then if `ContDiffAt ℝ 6 a t₀`, then `cosmoCoeff 6 a t₀ = 1 - 27 / 2 * Ω ^ 2 - 81 * Ω ^ 2 - 81 / 2 * Ω ^ 3`)

Program definitions in this claim:

- `IsFlatLCDM Ω a t₀` — **PINNED** (pin theorem `flatLCDMSpec2_pins`): the scale factor `a` obeys the flat ΛCDM expansion law H = H₀·√(`Ω`·(1 + z)³ + 1 − `Ω`) on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0, z is the redshift observed at `t₀`, and a is positive and differentiable on that neighbourhood
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)

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

## Your answers: use ANSWER_FORM.md, item 36
