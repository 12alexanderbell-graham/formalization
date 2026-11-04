# Item 11

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim in plain words (the system's own text)

**Pinning:** every `C` obeying the cosmographic Taylor law equals `cosmoCoeff` wherever
`a > 0`, `a` is `Cⁿ` near `t₀` and `ȧ(t₀) ≠ 0`.

## Formal statement (Lean 4)

```lean
theorem cosmoCoeffCore_pins (C : ℕ → (ℝ → ℝ) → ℝ → ℝ) (h : CosmoCoeffSpecCore C) (n : ℕ)
    (a : ℝ → ℝ) (t₀ : ℝ) (hok : CoeffOK n a t₀) : C n a t₀ = cosmoCoeff n a t₀ := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Chemistry.RKReduced.q`, `Cosmography.CCS.D1`, `Cosmography.CCS.D2`, `Cosmography.CCS.D3`, `Cosmography.CCS.remainder`, `Cosmography.CCS.series`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`, `Fidelity.CoeffOK`, `Fidelity.CosmoCoeffSpecCore`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `cosmoCoeffCore_pins`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Fidelity/RedshiftCoeffSpecs.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 11
