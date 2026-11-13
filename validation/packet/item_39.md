# Item 39

**Area:** Mathematics

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `S : ℝ`, `θ : ℝ → ℝ`, `φ : ℝ → ℝ`:

**assuming**

1. `68 / 5 ≤ S`
2. for every `r : ℝ`, if `r ∈ Set.Icc 0 S`, then `HasDerivWithinAt θ (φ r) (Set.Icc 0 S) r`
3. `ContinuousWithinAt φ (Set.Icc 0 S) 0`
4. for every `r : ℝ`, if `r ∈ Set.Ioc 0 S`, then `HasDerivWithinAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) (Set.Icc 0 S) r`
5. `θ 0 = 2.2062008646`

**then**

- there is `r : ℝ` such that (`r ∈ Set.Ioc 0 (68 / 5)`) and (`0 < φ r`) and (for every `s : ℝ`, if `s ∈ Set.Icc 0 r`, then `0 < θ s`)

## Author's paraphrase (hand-written; checked only by prose rules)

Townes radial equation, undershoot: for every S ≥ 68/5 and every solution θ of
θ'' + (1/r)θ' − θ + θ³ = 0 on (0, S] with θ(0) = 2.2062008646, θ differentiable on [0, S] with
derivative φ and φ continuous at 0, there is r in (0, 68/5] with φ(r) > 0 and θ positive on
[0, r].

## Formal statement (Lean 4)

```lean
theorem townes_under (S : ℝ) (hS : 68 / 5 ≤ S) (θ φ : ℝ → ℝ)
    (hθ : ∀ r ∈ Icc (0 : ℝ) S, HasDerivWithinAt θ (φ r) (Icc 0 S) r)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ r ∈ Ioc (0 : ℝ) S, HasDerivWithinAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) (Icc 0 S) r)
    (h0 : θ 0 = 2.2062008646) :
    ∃ r ∈ Ioc (0 : ℝ) (68 / 5), 0 < φ r ∧ ∀ s ∈ Icc 0 r, 0 < θ s := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `townes_under`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Townes/TownesShooting.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 39
