# Item 07

**Area:** Mathematics

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- there is `c : ℝ` such that (`c ∈ Set.Ioo 2.2062008646 2.2062008647`) and (there is `θ : ℝ → ℝ` such that there is `φ : ℝ → ℝ` such that (`θ 0 = c`) and (`φ 0 = 0`) and (for every `r : ℝ`, if `r ∈ Set.Ici 0`, then `HasDerivWithinAt θ (φ r) (Set.Ici 0) r`) and (`ContinuousWithinAt φ (Set.Ici 0) 0`) and (for every `r : ℝ`, if `r ∈ Set.Ioi 0`, then `HasDerivAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) r`) and (for every `r : ℝ`, if `r ∈ Set.Ici 0`, then `0 < θ r`) and (for every `r : ℝ`, if `r ∈ Set.Ioi 0`, then `φ r < 0`) and (`Filter.Tendsto θ Filter.atTop (nhds 0)`))

## Author's paraphrase (hand-written; checked only by prose rules)

Townes radial equation, existence: there is c in (2.2062008646, 2.2062008647) and a solution
θ of θ'' + (1/r)θ' − θ + θ³ = 0 on (0, ∞) with θ(0) = c, derivative φ on [0, ∞) (one-sided at 0),
φ(0) = 0 and φ continuous at 0, θ positive on [0, ∞), φ negative on (0, ∞) and θ(r) → 0 as
r → ∞.

## Formal statement (Lean 4)

```lean
theorem townes_exists : ∃ c ∈ Ioo (2.2062008646 : ℝ) 2.2062008647, ∃ θ φ : ℝ → ℝ,
    θ 0 = c ∧ φ 0 = 0 ∧
    (∀ r ∈ Ici (0 : ℝ), HasDerivWithinAt θ (φ r) (Ici 0) r) ∧
    ContinuousWithinAt φ (Ici 0) 0 ∧
    (∀ r ∈ Ioi (0 : ℝ), HasDerivAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) r) ∧
    (∀ r ∈ Ici (0 : ℝ), 0 < θ r) ∧ (∀ r ∈ Ioi (0 : ℝ), φ r < 0) ∧
    Tendsto θ atTop (𝓝 0) := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Townes/TownesExists.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 07
