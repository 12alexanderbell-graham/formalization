# Item 49

**Area:** Rigorous simulation of a reaction network

**Source:** see the claim

## Claim in plain words (the system's own text)

There is a solution of the mass-action rate equations of the Michaelis–Menten mechanism
with k₁ = k₋₁ = k₂ = 1, [S]₀ = [E]₀ = 1, [C]₀ = [P]₀ = 0 on the time interval [0, 13/5]
(derivatives within the interval).

## Formal statement (Lean 4)

```lean
theorem mm_solution_exists :
    ∃ s e c p : ℝ → ℝ, IsMMSolution 1 1 1 1 1 0 0 (13 / 5) s e c p := …
```

## Definitions it uses

See GLOSSARY.md: `Sim.MichaelisMenten.IsMMSolution`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsMMSolution.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): IsMMSolution: k₁ = 1, km₁ = 1, k₂ = 1, s₀ = 1, e₀ = 1, c₀ = 0, p₀ = 0, T = 13/5.
- Source file: `Checked/Sim/MichaelisMenten.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 49
