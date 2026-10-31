# Item 12

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim in plain words (the system's own text)

**Pinning:** any `D` meeting `LumDistSpec2` gives the program's flat luminosity distance at
`K = 0`.

## Formal statement (Lean 4)

```lean
theorem lumDistFlat_pins (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : LumDistSpec2 D) (a : ℝ → ℝ)
    (t₀ t : ℝ) (htt : t ≤ t₀) (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hcont : ContinuousOn a (Set.Icc t t₀)) : D 0 a t₀ t = lumDistFlat a t₀ t := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaY.lumDistFlat`, `Cosmography.redshift`, `Cosmography.BambaY.comoving`, `Fidelity.AngDistSpec`, `Fidelity.LumDistSpec`, `Fidelity.LumDistSpec2`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: lumDistFlat, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `lumDistFlat_pins`.
- Source file: `Checked/Fidelity/FlatPins.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 12
