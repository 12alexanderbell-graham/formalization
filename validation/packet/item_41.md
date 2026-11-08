# Item 41

**Area:** F9

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI ("testing F(R) gravity by cosmography"), Eq. (11.31), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583, PRD 78, 063504) Eq. (33): the common denominator R of the F(R₀), F″(R₀), F‴(R₀) formulas is wrong, so the printed F(R₀) formula (11.21) fails the paper's own ΛCDM check (11.40); also (11.13) d³R₀/dt³ has a sign error

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. `0 < a t₀`
2. `0 < hubble a t₀`
3. `ContDiffAt ℝ 5 a t₀`

**then**

1. `curv a t₀ = -6 * hubble a t₀ ^ 2 * (1 - decel a t₀)`
2. `deriv (curv a) t₀ = -6 * hubble a t₀ ^ 3 * (cosmoCoeff 3 a t₀ - decel a t₀ - 2)`
3. `deriv^[2] (curv a) t₀ = -6 * hubble a t₀ ^ 4 * (cosmoCoeff 4 a t₀ + decel a t₀ ^ 2 + 8 * decel a t₀ + 6)`
4. `deriv^[3] (curv a) t₀ = -6 * hubble a t₀ ^ 5 * (cosmoCoeff 5 a t₀ - cosmoCoeff 4 a t₀ - 2 * (decel a t₀ + 4) * cosmoCoeff 3 a t₀ - 6 * (3 * decel a t₀ + 8) * decel a t₀ - 24)`

Program definitions in this claim:

- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)
- `curv a t` — **PINNED** (pin theorem `ricciSpec_pins`): the Ricci scalar R = −6(Ḣ + 2H²) of spatially flat FLRW with scale factor `a` at time `t` (sign convention of Bamba et al. 2012, Eq. (11.6))
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): the deceleration parameter −a″(t)·a(t)/a′(t)² of the scale factor `a` at time `t`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): the Hubble rate a′(t)/a(t) of the scale factor `a` at time `t`

## Author's paraphrase (hand-written; checked only by prose rules)

**Correct (11.10)–(11.13).** For every flat FLRW scale factor `C⁵` at `t₀` with `a(t₀) > 0`, `H₀ > 0`,
the Ricci scalar `R = −6(Ḣ + 2H²)` (the review's sign convention) and its first three time derivatives
at `t₀`: `R₀ = −6H₀²(1 − q₀)`, `Ṙ₀ = −6H₀³(j₀ − q₀ − 2)`, `R̈₀ = −6H₀⁴(s₀ + q₀² + 8q₀ + 6)`,
`R⃛₀ = −6H₀⁵[l₀ − s₀ − 2(q₀ + 4)j₀ − 6(3q₀ + 8)q₀ − 24]` (the review's (11.13) prints `+2(q₀ + 4)j₀`).

## Formal statement (Lean 4)

```lean
theorem curv_derivs (a : ℝ → ℝ) (t₀ : ℝ) (ha : 0 < a t₀) (hH : 0 < hubble a t₀)
    (hs : ContDiffAt ℝ 5 a t₀) :
    curv a t₀ = -6 * hubble a t₀ ^ 2 * (1 - decel a t₀) ∧
    deriv (curv a) t₀ = -6 * hubble a t₀ ^ 3 * (cosmoCoeff 3 a t₀ - decel a t₀ - 2) ∧
    deriv^[2] (curv a) t₀ =
      -6 * hubble a t₀ ^ 4 * (cosmoCoeff 4 a t₀ + decel a t₀ ^ 2 + 8 * decel a t₀ + 6) ∧
    deriv^[3] (curv a) t₀ = -6 * hubble a t₀ ^ 5 *
      (cosmoCoeff 5 a t₀ - cosmoCoeff 4 a t₀ - 2 * (decel a t₀ + 4) * cosmoCoeff 3 a t₀
        - 6 * (3 * decel a t₀ + 8) * decel a t₀ - 24) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.FRCosmo.curv`, `Cosmography.decel`, `Cosmography.hubble`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, curv, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `curv_derivs`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3, n = 4, n = 5.
- Source file: `Checked/Cosmography/FRCosmo.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 41
