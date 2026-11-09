# Item 52

**Area:** F9

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI ("testing F(R) gravity by cosmography"), Eq. (11.31), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583, PRD 78, 063504) Eq. (33): the common denominator R of the F(R₀), F″(R₀), F‴(R₀) formulas is wrong, so the printed F(R₀) formula (11.21) fails the paper's own ΛCDM check (11.40); also (11.13) d³R₀/dt³ has a sign error

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- it is false that (`PrintedR3Claim`)

Program definitions in this claim:

- `PrintedR3Claim` — CLAIM, not pinned; the source-dependent data written inline (printed formula, order of the printed series) agree with an independent blind second reading of the source (`Checked.Trust.Transcriptions.agree_PrintedR3Claim`); the quantifiers and hypotheses are the program's formalisation: means for every `a : ℝ → ℝ`, for every `t₀ : ℝ`, if `0 < a t₀`, then if `0 < hubble a t₀`, then if `ContDiffAt ℝ 5 a t₀`, then `deriv^[3] (curv a) t₀ = -6 * hubble a t₀ ^ 5 * (cosmoCoeff 5 a t₀ - cosmoCoeff 4 a t₀ + 2 * (decel a t₀ + 4) * cosmoCoeff 3 a t₀ - 6 * (3 * decel a t₀ + 8) * decel a t₀ - 24)`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): phrase (hand-written, linted): the cosmographic coefficient of the scale factor `a` at the time of evaluation `t` for the derivative order of the coefficient `n` (j, s, l, m for the orders 3, 4, 5, 6; the deceleration parameter is minus the order 2 coefficient); by definition, `cosmoCoeff n a t` is `iteratedDeriv n a t / (a t * hubble a t ^ n)`
- `curv a t` — **PINNED** (pin theorem `ricciSpec_pins`): phrase (hand-written, linted): the Ricci scalar of flat FLRW with scale factor `a` at the cosmic time of evaluation `t` (sign convention of Bamba et al. 2012, Eq. (11.6): negative convention, de Sitter has negative Ricci scalar); by definition, `curv a t` is `-6 * (deriv (hubble a) t + 2 * hubble a t ^ 2)`
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): phrase (hand-written, linted): the deceleration parameter of the scale factor `a` at the cosmic time of evaluation `t` (minus acceleration times scale factor over velocity squared); by definition, `decel a t` is `-(deriv (deriv a) t * a t) / deriv a t ^ 2`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): phrase (hand-written, linted): the Hubble rate of the scale factor `a` at the cosmic time of evaluation `t`; by definition, `hubble a t` is `deriv a t / a t`

## Author's paraphrase (hand-written; checked only by prose rules)

The review's (11.13), `d³R₀/dt³ = −6H₀⁵[l₀ − s₀ + 2(q₀ + 4)j₀ − 6(3q₀ + 8)q₀ − 24]`, does not hold for
every flat FLRW scale factor `C⁵` at `t₀` with `a(t₀) > 0`, `H₀ > 0` (the correct term is
`−2(q₀ + 4)j₀`: `curv_derivs`).

## Formal statement (Lean 4)

```lean
theorem printedR3Claim_false : ¬ PrintedR3Claim := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.FRCosmo.curv`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.FRCosmo.PrintedR3Claim`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, curv, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): PrintedR3Claim².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 5, n = 4, n = 3.
- Source file: `Checked/Cosmography/FRCosmo.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 52
