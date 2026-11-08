# Item 43

**Area:** Certified numbers of the findings

**Source:** Aviles, Gruber, Luongo, Quevedo, PRD 86, 123516 (2012), arXiv:1204.2007 (v1 and v2), Eq. (15): misprinted ΛCDM l₀ and m₀

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- there is `r : ℝ` such that (`RoundsTo r 0.549 3`) and (`0 < r`) and (`r < 1`) and (for every `a : ℝ → ℝ`, for every `t₀ : ℝ`, if the scale factor `a` obeys the flat ΛCDM expansion law H = H₀·√(`r`·(1 + z)³ + 1 − `r`) on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0, z is the redshift observed at `t₀`, and a is positive and differentiable on that neighbourhood, then if `ContDiffAt ℝ 6 a t₀`, then `cosmoCoeff 6 a t₀ = 1 - 27 / 2 * r ^ 2 - 81 * r ^ 2 - 81 / 2 * r ^ 3`)

Program definitions in this claim:

- `IsFlatLCDM Ω a t₀` — **PINNED** (pin theorem `flatLCDMSpec2_pins`): the scale factor `a` obeys the flat ΛCDM expansion law H = H₀·√(`Ω`·(1 + z)³ + 1 − `Ω`) on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0, z is the redshift observed at `t₀`, and a is positive and differentiable on that neighbourhood
- `RoundsTo x d k` — MATH, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_RoundsTo`) (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)

## Author's paraphrase (hand-written; checked only by prose rules)

There is a matter fraction `Ω ≈ 0.549` in `(0, 1)` at which the printed `m₀` agrees with the
true `m₀` of every flat ΛCDM model (`Ω = (√7 − 1)/3`).

## Formal statement (Lean 4)

```lean
theorem F1_m0_agrees : ∃ r : ℝ, RoundsTo r 0.549 3 ∧ 0 < r ∧ r < 1 ∧
    ∀ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM r a t₀ → ContDiffAt ℝ 6 a t₀ →
      cosmoCoeff 6 a t₀ = 1 - 27 / 2 * r ^ 2 - 81 * r ^ 2 - 81 / 2 * r ^ 3 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.IsFlatLCDM`, `Cosmography.Aviles.cosmoCoeff`, `Cosmography.hubble`, `Cosmography.redshift`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatLCDM, cosmoCoeff.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): RoundsTo: d = 0.549, k = 3; cosmoCoeff: n = 6.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 43
