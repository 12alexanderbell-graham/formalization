# Item 02

**Area:** Mathematics

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `θ : ℝ → ℝ`, `φ : ℝ → ℝ`:

**assuming**

1. for every `ξ : ℝ`, if `ξ ∈ Set.Icc 0 7`, then `HasDerivWithinAt θ (φ ξ) (Set.Icc 0 7) ξ`
2. `ContinuousWithinAt φ (Set.Icc 0 7) 0`
3. for every `ξ : ℝ`, if `ξ ∈ Set.Ioc 0 7`, then `HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 3) (Set.Icc 0 7) ξ`
4. `θ 0 = 1`

**then**

- there is `ξ₁ : ℝ` such that (`6.896848615 ≤ ξ₁`) and (`ξ₁ ≤ 6.896848625`) and (`θ ξ₁ = 0`) and (for every `ξ : ℝ`, if `ξ ∈ Set.Ico 0 ξ₁`, then `0 < θ ξ`) and (`2.018235945 ≤ -(ξ₁ ^ 2 * φ ξ₁)`) and (`-(ξ₁ ^ 2 * φ ξ₁) ≤ 2.018235955`) and (`54.1824805 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁))`) and (`ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 54.1824815`)

## Author's paraphrase (hand-written; checked only by prose rules)

Lane–Emden equation of index 3: for every solution θ of θ'' + (2/ξ)θ' + θ³ = 0 on (0, 7] with
θ(0) = 1, θ differentiable on [0, 7] with derivative φ, and φ continuous at 0, there is a first zero
ξ₁ of θ with 6.896848615 ≤ ξ₁ ≤ 6.896848625 (θ > 0 before it), at which the Chandrasekhar-mass
constant −ξ₁² θ'(ξ₁) lies between 2.018235945 and 2.018235955 and ξ₁³/(3 · (−ξ₁² θ'(ξ₁))) lies
between 54.1824805 and 54.1824815.

## Formal statement (Lean 4)

```lean
theorem laneEmden3_constants (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) 7, HasDerivWithinAt θ (φ ξ) (Icc 0 7) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 7) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) 7, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 3) (Icc 0 7) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 6.896848615 ≤ ξ₁ ∧ ξ₁ ≤ 6.896848625 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.018235945 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.018235955 ∧
      54.1824805 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 54.1824815 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `laneEmden3_constants`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/LaneEmden.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 02
