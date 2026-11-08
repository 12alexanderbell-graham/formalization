# Item 34

**Area:** F2

**Source:** Capozziello, Lazkoz, Salzano, PRD 84, 124061 (2011), arXiv:1104.3096 (v1 and v2), Eq. (22): flat matter + CPL l₀, w_a² term missing a factor 9

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`, `w₀ : ℝ`, `wₐ : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. the scale factor `a` obeys the flat matter + CPL dark-energy expansion law H = H₀·√(Ω(1 + z)³ + (1 − Ω)(1 + z)^(3(1 + w₀ + wₐ))·exp(−3wₐz/(1 + z))) with Ω = `Ω`, w₀ = `w₀`, wₐ = `wₐ`, on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0 and a is positive and differentiable on that neighbourhood
2. `ContDiffAt ℝ 5 a t₀`

**then**

1. `decel a t₀ = 1 / 2 + 3 / 2 * (1 - Ω) * w₀`
2. `cosmoCoeff 3 a t₀ = 1 + 3 / 2 * (1 - Ω) * (3 * w₀ * (1 + w₀) + wₐ)`
3. `cosmoCoeff 4 a t₀ = -7 / 2 - 33 / 4 * (1 - Ω) * wₐ - 9 / 4 * (1 - Ω) * (9 + (7 - Ω) * wₐ) * w₀ - 9 / 4 * (1 - Ω) * (16 - 3 * Ω) * w₀ ^ 2 - 27 / 4 * (1 - Ω) * (3 - Ω) * w₀ ^ 3`
4. `cosmoCoeff 5 a t₀ = 35 / 2 + (1 - Ω) / 4 * (213 + 9 * (7 - Ω) * wₐ) * wₐ + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀ + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2 + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3 + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4`

Program definitions in this claim:

- `IsFlatCPL Ω w₀ wₐ a t₀` — **PINNED** (pin theorem `flatCPL_pins`): the scale factor `a` obeys the flat matter + CPL dark-energy expansion law H = H₀·√(Ω(1 + z)³ + (1 − Ω)(1 + z)^(3(1 + w₀ + wₐ))·exp(−3wₐz/(1 + z))) with Ω = `Ω`, w₀ = `w₀`, wₐ = `wₐ`, on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0 and a is positive and differentiable on that neighbourhood
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): the deceleration parameter −a″(t)·a(t)/a′(t)² of the scale factor `a` at time `t`

## Author's paraphrase (hand-written; checked only by prose rules)

**Cosmographic coefficients of flat matter + CPL** (correct version of CLS Eqs. (19)–(22)).
q₀, j₀ as printed; s₀ as printed with the dropped minus sign before `27/4` restored; l₀ with
`9 (7 − Ω)` in place of the printed `(7 − Ω)` in the `wₐ²` term.

## Formal statement (Lean 4)

```lean
theorem flatCPL_coeffs (Ω w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatCPL Ω w₀ wₐ a t₀)
    (hs : ContDiffAt ℝ 5 a t₀) :
    decel a t₀ = 1 / 2 + 3 / 2 * (1 - Ω) * w₀ ∧
    cosmoCoeff 3 a t₀ = 1 + 3 / 2 * (1 - Ω) * (3 * w₀ * (1 + w₀) + wₐ) ∧
    cosmoCoeff 4 a t₀ = -7 / 2 - 33 / 4 * (1 - Ω) * wₐ
      - 9 / 4 * (1 - Ω) * (9 + (7 - Ω) * wₐ) * w₀ - 9 / 4 * (1 - Ω) * (16 - 3 * Ω) * w₀ ^ 2
      - 27 / 4 * (1 - Ω) * (3 - Ω) * w₀ ^ 3 ∧
    cosmoCoeff 5 a t₀ = 35 / 2 + (1 - Ω) / 4 * (213 + 9 * (7 - Ω) * wₐ) * wₐ
      + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀
      + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2
      + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3
      + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.CPL.IsFlatCPL`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, IsFlatCPL, decel.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `flatCPL_coeffs`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3, n = 4, n = 5.
- Source file: `Checked/Cosmography/CPLCoefficients.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 34
