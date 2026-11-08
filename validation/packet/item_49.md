# Item 49

**Area:** Mathematics

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `θ : ℝ → ℝ`, `φ : ℝ → ℝ`:

**assuming**

1. for every `ξ : ℝ`, if `ξ ∈ Set.Icc 0 5`, then `HasDerivWithinAt θ (φ ξ) (Set.Icc 0 5) ξ`
2. `ContinuousWithinAt φ (Set.Icc 0 5) 0`
3. for every `ξ : ℝ`, if `ξ ∈ Set.Ioc 0 5`, then `HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 2) (Set.Icc 0 5) ξ`
4. `θ 0 = 1`

**then**

- there is `ξ₁ : ℝ` such that (`4.3528745959 ≤ ξ₁`) and (`ξ₁ ≤ 4.3528745960`) and (`θ ξ₁ = 0`) and (for every `ξ : ℝ`, if `ξ ∈ Set.Ico 0 ξ₁`, then `0 < θ ξ`) and (`2.4110460120 ≤ -(ξ₁ ^ 2 * φ ξ₁)`) and (`-(ξ₁ ^ 2 * φ ξ₁) ≤ 2.4110460122`) and (`11.402542860 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁))`) and (`ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 11.402542864`)

## Author's paraphrase (hand-written; checked only by prose rules)

Lane–Emden equation θ'' + (2/ξ)θ' + θ² = 0: for every solution θ on (0, 5] with θ(0) = 1, θ
differentiable on [0, 5] with derivative φ, and φ continuous at 0, there is a first zero ξ₁ of θ with
4.3528745959 ≤ ξ₁ ≤ 4.3528745960, at which −ξ₁² θ'(ξ₁) lies between 2.4110460120 and 2.4110460122
and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies between 11.402542860 and 11.402542864.

## Formal statement (Lean 4)

```lean
theorem laneEmden2_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 5, HasDerivWithinAt θ (φ ξ) (Icc 0 5) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 5) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 5, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 2) (Icc 0 5) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 4.3528745959 ≤ ξ₁ ∧ ξ₁ ≤ 4.3528745960 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.4110460120 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.4110460122 ∧
      11.402542860 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 11.402542864 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `laneEmden2_constants`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/LaneEmden2.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 49
