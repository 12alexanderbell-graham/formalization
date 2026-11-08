# Item 40

**Area:** F1

**Source:** Aviles, Gruber, Luongo, Quevedo, PRD 86, 123516 (2012), arXiv:1204.2007 (v1 and v2), Eq. (15): misprinted ΛCDM l₀ and m₀

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. the scale factor `a` obeys the flat ΛCDM expansion law H = H₀·√(`Ω`·(1 + z)³ + 1 − `Ω`) on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0, z is the redshift observed at `t₀`, and a is positive and differentiable on that neighbourhood
2. `ContDiffAt ℝ 6 a t₀`

**then**

1. `decel a t₀ = 3 / 2 * Ω - 1`
2. `cosmoCoeff 3 a t₀ = 1`
3. `cosmoCoeff 4 a t₀ = 1 - 9 / 2 * Ω`
4. `cosmoCoeff 5 a t₀ = 1 + 3 * Ω + 27 / 2 * Ω ^ 2`
5. `cosmoCoeff 6 a t₀ = 1 - 27 / 2 * Ω - 81 * Ω ^ 2 - 81 / 4 * Ω ^ 3`

Program definitions in this claim:

- `IsFlatLCDM Ω a t₀` — **PINNED** (pin theorem `flatLCDMSpec2_pins`): the scale factor `a` obeys the flat ΛCDM expansion law H = H₀·√(`Ω`·(1 + z)³ + 1 − `Ω`) on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0, z is the redshift observed at `t₀`, and a is positive and differentiable on that neighbourhood
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): the deceleration parameter −a″(t)·a(t)/a′(t)² of the scale factor `a` at time `t`

## Author's paraphrase (hand-written; checked only by prose rules)

**Cosmographic coefficients of flat ΛCDM** (correct version of Aviles et al. Eq. (15)).
For any scale factor obeying `H = H₀ √(Ω(1+z)³ + 1 − Ω)` near `t₀` and six times continuously
differentiable at `t₀`: `q₀ = 3Ω/2 − 1`, `j₀ = 1`, `s₀ = 1 − 9Ω/2`, `l₀ = 1 + 3Ω + 27Ω²/2`,
`m₀ = 1 − 27Ω/2 − 81Ω² − 81Ω³/4`.

## Formal statement (Lean 4)

```lean
theorem flatLCDM_coeffs (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatLCDM Ω a t₀)
    (hs : ContDiffAt ℝ 6 a t₀) :
    decel a t₀ = 3 / 2 * Ω - 1 ∧ cosmoCoeff 3 a t₀ = 1 ∧ cosmoCoeff 4 a t₀ = 1 - 9 / 2 * Ω ∧
    cosmoCoeff 5 a t₀ = 1 + 3 * Ω + 27 / 2 * Ω ^ 2 ∧
    cosmoCoeff 6 a t₀ = 1 - 27 / 2 * Ω - 81 * Ω ^ 2 - 81 / 4 * Ω ^ 3 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.IsFlatLCDM`, `Cosmography.Aviles.cosmoCoeff`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatLCDM, cosmoCoeff, decel.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `flatLCDM_coeffs`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3, n = 4, n = 5, n = 6.
- Source file: `Checked/Cosmography/LCDMCoefficients.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 40
