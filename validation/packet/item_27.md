# Item 27

**Area:** F2

**Source:** Capozziello, Lazkoz, Salzano, PRD 84, 124061 (2011), arXiv:1104.3096 (v1 and v2), Eq. (22): flat matter + CPL l₀, w_a² term missing a factor 9

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`, `w₀ : ℝ`, `wₐ : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. the scale factor `a` obeys the flat matter plus CPL dark-energy Friedmann expansion law with matter fraction given by the present matter density parameter `Ω`, present dark energy equation of state `w₀` and equation of state evolution parameter `wₐ` on some neighbourhood of the observation time `t₀`, with a positive Hubble rate at `t₀` and a positive, differentiable scale factor on that neighbourhood
2. `ContDiffAt ℝ 5 a t₀`
3. `(1 - Ω) * (7 - Ω) * wₐ = 0`

**then**

- `cosmoCoeff 5 a t₀ ≠ 35 / 2 + (1 - Ω) / 4 * (213 + (7 - Ω) * wₐ) * wₐ + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀ + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2 + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3 + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4`

Program definitions in this claim:

- `IsFlatCPL Ω w₀ wₐ a t₀` — **PINNED** (pin theorem `flatCPL_pins`): phrase (hand-written, linted): the scale factor `a` obeys the flat matter plus CPL dark-energy Friedmann expansion law with matter fraction given by the present matter density parameter `Ω`, present dark energy equation of state `w₀` and equation of state evolution parameter `wₐ` on some neighbourhood of the observation time `t₀`, with a positive Hubble rate at `t₀` and a positive, differentiable scale factor on that neighbourhood; by definition, means (`0 < hubble a t₀`) and (`∀ᶠ (t : ℝ) in nhds t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧ hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + (1 - Ω) * (1 + redshift a t₀ t) ^ (3 * (1 + w₀ + wₐ)) * Real.exp (-(3 * wₐ * redshift a t₀ t) / (1 + redshift a t₀ t)))`)
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): phrase (hand-written, linted): the cosmographic coefficient of the scale factor `a` at the time of evaluation `t` for the derivative order of the coefficient `n` (j, s, l, m for the orders 3, 4, 5, 6; the deceleration parameter is minus the order 2 coefficient); by definition, `cosmoCoeff n a t` is `iteratedDeriv n a t / (a t * hubble a t ^ n)`

## Author's paraphrase (hand-written; checked only by prose rules)

The printed `l₀` is wrong in every flat CPL model with `(1 − Ω)(7 − Ω) wₐ ≠ 0`.

## Formal statement (Lean 4)

```lean
theorem printedL0_ne (Ω w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatCPL Ω w₀ wₐ a t₀)
    (hs : ContDiffAt ℝ 5 a t₀) (hne : (1 - Ω) * (7 - Ω) * wₐ = 0) :
    cosmoCoeff 5 a t₀ ≠ 35 / 2 + (1 - Ω) / 4 * (213 + (7 - Ω) * wₐ) * wₐ
      + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀
      + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2
      + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3
      + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.CPL.IsFlatCPL`, `Cosmography.hubble`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, IsFlatCPL.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `printedL0_ne`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 5.
- Source file: `Checked/Cosmography/CPLCoefficients.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 27
