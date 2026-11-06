# Item 50

**Area:** Mathematics

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `S : ℝ`, `w : ℝ → ℝ`, `φ : ℝ → ℝ`:

**assuming**

1. `41 / 10 ≤ S`
2. for every `s : ℝ`, if `s ∈ Set.Icc 0 S`, then `HasDerivWithinAt w (φ s) (Set.Icc 0 S) s`
3. `ContinuousWithinAt φ (Set.Icc 0 S) 0`
4. for every `s : ℝ`, if `s ∈ Set.Ioc 0 S`, then `HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Set.Icc 0 S) s`
5. `w 0 = 0`

**then**

- there is `s₁ : ℝ` such that (`4.071496844 ≤ s₁`) and (`s₁ ≤ 4.071496845`) and (for every `s : ℝ`, if `s ∈ Set.Icc 0 S`, then `s ^ 2 * Real.exp (w s) ≤ s₁ ^ 2 * Real.exp (w s₁)`) and (`3.321992118 ≤ s₁ ^ 2 * Real.exp (w s₁)`) and (`s₁ ^ 2 * Real.exp (w s₁) ≤ 3.321992119`)

## Author's paraphrase (hand-written; checked only by prose rules)

Gelfand problem in the three-dimensional ball, radial branch: for every S ≥ 41/10 and every
solution w of w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with
derivative φ and φ continuous at 0, there is a point s₁ between 4.071496844 and 4.071496845 at which
s² e^{w(s)} attains its maximum over [0, S], and that maximum lies between 3.321992118 and
3.321992119.

## Formal statement (Lean 4)

```lean
theorem gelfand_ball_critical (S : ℝ) (hS : 41 / 10 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ s₁ : ℝ, 4.071496844 ≤ s₁ ∧ s₁ ≤ 4.071496845 ∧
      (∀ s ∈ Icc 0 S, s ^ 2 * Real.exp (w s) ≤ s₁ ^ 2 * Real.exp (w s₁)) ∧
      3.321992118 ≤ s₁ ^ 2 * Real.exp (w s₁) ∧ s₁ ^ 2 * Real.exp (w s₁) ≤ 3.321992119 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `gelfand_ball_critical`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/Gelfand.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 50
