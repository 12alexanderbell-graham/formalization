# Item 18

**Area:** Certified numbers of the findings

**Source:** Capozziello, Lazkoz, Salzano, PRD 84, 124061 (2011), arXiv:1104.3096 (v1 and v2), Eq. (22): flat matter + CPL l₀, w_a² term missing a factor 9

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `w₀ : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. the scale factor `a` obeys the flat matter + CPL dark-energy expansion law H = H₀·√(Ω(1 + z)³ + (1 − Ω)(1 + z)^(3(1 + w₀ + wₐ))·exp(−3wₐz/(1 + z))) with Ω = `3 / 10`, w₀ = `w₀`, wₐ = `-1 / 2`, on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0 and a is positive and differentiable on that neighbourhood
2. `ContDiffAt ℝ 5 a t₀`

**then**

- `RoundsTo (cosmoCoeff 5 a t₀ - (35 / 2 + (1 - 3 / 10) / 4 * (213 + (7 - 3 / 10) * (-1 / 2)) * (-1 / 2) + (1 - 3 / 10) / 4 * (489 + 9 * (82 - 21 * (3 / 10)) * (-1 / 2)) * w₀ + 9 / 2 * (1 - 3 / 10) * (67 - 21 * (3 / 10) + 3 / 2 * (23 - 11 * (3 / 10)) * (-1 / 2)) * w₀ ^ 2 + 27 / 4 * (1 - 3 / 10) * (47 - 24 * (3 / 10)) * w₀ ^ 3 + 81 / 2 * (1 - 3 / 10) * (3 - 2 * (3 / 10)) * w₀ ^ 4)) 2.345 3`

Program definitions in this claim:

- `IsFlatCPL Ω w₀ wₐ a t₀` — **PINNED** (pin theorem `flatCPL_pins`): the scale factor `a` obeys the flat matter + CPL dark-energy expansion law H = H₀·√(Ω(1 + z)³ + (1 − Ω)(1 + z)^(3(1 + w₀ + wₐ))·exp(−3wₐz/(1 + z))) with Ω = `Ω`, w₀ = `w₀`, wₐ = `wₐ`, on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0 and a is positive and differentiable on that neighbourhood
- `RoundsTo x d k` — MATH, not pinned, so only the formula shown is checked, not its name (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)

## Author's paraphrase (hand-written; checked only by prose rules)

At `Ω = 0.3`, `wₐ = −0.5` and every `w₀`, every flat CPL model has `l₀` exceeding the printed
formula by `2.345`.

## Formal statement (Lean 4)

```lean
theorem F2_error (w₀ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hL : CPL.IsFlatCPL (3 / 10) w₀ (-1 / 2) a t₀)
    (hs : ContDiffAt ℝ 5 a t₀) :
    RoundsTo (cosmoCoeff 5 a t₀ - printedCPLl0 (3 / 10 : ℝ) w₀ (-1 / 2 : ℝ)) 2.345 3 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.CPL.IsFlatCPL`, `Cosmography.hubble`, `Cosmography.redshift`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, IsFlatCPL.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `F2_error`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): IsFlatCPL: Ω = 3/10, wₐ = -1/2; RoundsTo: d = 2.345, k = 3; cosmoCoeff: n = 5.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 18
