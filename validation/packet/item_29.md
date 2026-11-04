# Item 29

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim in plain words (the system's own text)

**Pinning:** any `O` meeting `Omega0Spec` is `omega0` wherever `a₀ > 0`, `a` is
differentiable at `t₀` and `H₀ ≠ 0`.

## Formal statement (Lean 4)

```lean
theorem omega0Spec_pins (O : ℝ → (ℝ → ℝ) → ℝ → ℝ) (h : Omega0Spec O) (K : ℝ) (a : ℝ → ℝ)
    (t₀ : ℝ) (ha : 0 < a t₀) (hd : DifferentiableAt ℝ a t₀) (hH : deriv a t₀ / a t₀ ≠ 0) :
    O K a t₀ = omega0 K a t₀ := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaK.omega0`, `Cosmography.hubble`, `Fidelity.Omega0Spec`, `Sim.DuffingExists.G`, `Sim.DuffingExists.cl`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: omega0.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `omega0Spec_pins`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Fidelity/YOmegaKSpecs.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 29
