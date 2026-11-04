# Item 29

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim in plain words (the system's own text)

**The program's flat CPL predicate equals the blind first-principles formulation**, for
every `Ω, w₀, wₐ`, every scale factor and every `t₀`.

## Formal statement (Lean 4)

```lean
theorem isFlatCPL_iff_friedmannCPL (Ω w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) :
    IsFlatCPL Ω w₀ wₐ a t₀ ↔ FriedmannCPL Ω w₀ wₐ a t₀ := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.CPL.IsFlatCPL`, `Cosmography.hubble`, `Cosmography.redshift`, `Fidelity.FriedmannCPL`, `Sim.DuffingExists.G`, `Sim.DuffingExists.cl`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatCPL.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `isFlatCPL_iff_friedmannCPL`.
- Source file: `Checked/Fidelity/FriedmannCPL.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 29
