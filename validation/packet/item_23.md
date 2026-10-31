# Item 23

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim in plain words (the system's own text)

**Pinning:** any predicate obeying the blind first-principles law is `IsFlatCPL`.

## Formal statement (Lean 4)

```lean
theorem flatCPL_pins (P : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop)
    (h : ∀ Ω w₀ wₐ a t₀, P Ω w₀ wₐ a t₀ ↔ FriedmannCPL Ω w₀ wₐ a t₀) : P = IsFlatCPL := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.CPL.IsFlatCPL`, `Cosmography.hubble`, `Cosmography.redshift`, `Fidelity.FriedmannCPL`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatCPL.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `flatCPL_pins`.
- Source file: `Checked/Fidelity/FriedmannCPL.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 23
