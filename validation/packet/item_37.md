# Item 37

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim in plain words (the system's own text)

**Pinning:** every `Z` obeying the integrated wavelength-stretching law equals `redshift`
on every ray along which `a > 0` is `C¹`.

## Formal statement (Lean 4)

```lean
theorem redshiftCore_pins (Z : (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : RedshiftSpecCore Z) (a : ℝ → ℝ)
    (t₀ t : ℝ) (hr : RayOK a t t₀) : Z a t₀ t = redshift a t₀ t := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.redshift`, `Fidelity.RayOK`, `Fidelity.RedshiftSpecCore`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `redshiftCore_pins`.
- Source file: `Checked/Fidelity/RedshiftCoeffSpecs.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 37
