# Item 19

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim in plain words (the system's own text)

**Pinning:** the specification determines the luminosity distance on the whole admissible
domain.

## Formal statement (Lean 4)

```lean
theorem lumDistSpec2_pins (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : LumDistSpec2 D) (K : ℝ)
    (a : ℝ → ℝ) (t₀ t : ℝ) (htt : t ≤ t₀) (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hcont : ContinuousOn a (Set.Icc t t₀)) : D K a t₀ t = lumDist K a t₀ t := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaK.lumDist`, `Cosmography.redshift`, `Cosmography.BambaY.comoving`, `Cosmography.Transverse.transverse`, `Fidelity.AngDistSpec`, `Fidelity.LumDistSpec`, `Fidelity.LumDistSpec2`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: lumDist, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `lumDistSpec2_pins`.
- Source file: `Checked/Fidelity/Pins.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 19
