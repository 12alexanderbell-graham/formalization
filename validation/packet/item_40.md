# Item 40

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim in plain words (the system's own text)

`HubbleSpec` pins `hubble` for every positive scale factor differentiable at `t`
(its `logDeriv` law `H = d ln a/dt` and uniqueness of derivatives).

## Formal statement (Lean 4)

```lean
theorem hubbleSpec_pins (H : (ℝ → ℝ) → ℝ → ℝ) (h : HubbleSpec H) (a : ℝ → ℝ) (t : ℝ)
    (ha : 0 < a t) (hd : DifferentiableAt ℝ a t) : H a t = hubble a t := …
```

Definitions specific to this item:

```lean
/-- The Hubble rate `H = ȧ/a`. (Used by this item in place of the glossary entry.) -/
noncomputable def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t ^ 2
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.hubble`, `Fidelity.HubbleSpec`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `hubbleSpec_pins`.
- Source file: `Checked/Fidelity/Pins.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 40
