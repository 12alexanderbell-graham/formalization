# Item 32

**Area:** F1

**Source:** arXiv:1903.11433, Eq. (21): misprinted flat ΛCDM l₀ (printed as 1 + 3Ω_m − (27/2)Ω_m²)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- it is false that (`AvilesL0Claim`)

Program definitions in this claim:

- `AvilesL0Claim` — CLAIM, not pinned; the source-dependent data written inline (printed formula, order of the printed series) agree with an independent blind second reading of the source (`Checked.Trust.Transcriptions.agree_AvilesL0Claim`); the quantifiers and hypotheses are the program's formalisation: means for every `Ω : ℝ`, for every `a : ℝ → ℝ`, for every `t₀ : ℝ`, if the scale factor `a` obeys the flat ΛCDM expansion law H = H₀·√(`Ω`·(1 + z)³ + 1 − `Ω`) on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0, z is the redshift observed at `t₀`, and a is positive and differentiable on that neighbourhood, then if `ContDiffAt ℝ 6 a t₀`, then `cosmoCoeff 5 a t₀ = 1 + 3 * Ω - 27 / 2 * Ω ^ 2`
- `IsFlatLCDM Ω a t₀` — **PINNED** (pin theorem `flatLCDMSpec2_pins`): the scale factor `a` obeys the flat ΛCDM expansion law H = H₀·√(`Ω`·(1 + z)³ + 1 − `Ω`) on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0, z is the redshift observed at `t₀`, and a is positive and differentiable on that neighbourhood
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)

## Author's paraphrase (hand-written; checked only by prose rules)

**Refutation of the printed l₀ in Eq. (21).** On Einstein–de Sitter (Ω = 1) the printed
formula gives `−19/2`, the true value is `35/2`.

## Formal statement (Lean 4)

```lean
theorem avilesL0Claim_false : ¬ AvilesL0Claim := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.IsFlatLCDM`, `Cosmography.Aviles.cosmoCoeff`, `Cosmography.Aviles.AvilesL0Claim`, `Cosmography.hubble`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatLCDM, cosmoCoeff.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): AvilesL0Claim².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 5.
- Source file: `Checked/Cosmography/LCDMCoefficients.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 32
