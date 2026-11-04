# Item 47

**Area:** Rigorous simulation of a reaction network

**Source:** see the claim

## Claim in plain words (the system's own text)

Certified half-conversion time of the full Michaelis–Menten mechanism with
k₁ = k₋₁ = k₂ = 1, [S]₀ = [E]₀ = 1, [C]₀ = [P]₀ = 0: every solution of the mass-action rate
equations on the time interval [0, 13/5] (derivatives within the interval) has product
concentration strictly below 1/2 at all times in [0, 2.5665] and strictly above 1/2 at time
2.5666, so half of the substrate is first converted to product between 2.5665 and 2.5666.

## Formal statement (Lean 4)

```lean
theorem mm_half_conversion {s e c p : ℝ → ℝ} (h : IsMMSolution 1 1 1 1 1 0 0 (13 / 5) s e c p) :
    (∀ t ∈ Icc (0 : ℝ) (25665 / 10000), p t < 1 / 2) ∧ 1 / 2 < p (25666 / 10000) := …
```

## Definitions it uses

See GLOSSARY.md: `Sim.MichaelisMenten.IsMMSolution`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsMMSolution.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `mm_half_conversion`.
- Source file: `Checked/Sim/MichaelisMenten.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 47
