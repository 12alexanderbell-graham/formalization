# Item 03

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `H : (ℝ → ℝ) → ℝ → ℝ`, `a : ℝ → ℝ`, `t : ℝ`:

**assuming**

1. `HubbleSpec H`
2. `0 < a t`
3. `DifferentiableAt ℝ a t`

**then**

- `H a t = hubble a t`

Program definitions in this claim:

- `HubbleSpec` — SPEC, not pinned: inductive type with constructors `HubbleSpec.mk : ∀ {H : (ℝ → ℝ) → ℝ → ℝ}, (∀ (a : ℝ → ℝ) (t : ℝ), 0 < a t → DifferentiableAt ℝ a t → HasDerivAt (fun s => Real.log (a s)) (H a t) t) → (∀ (h t : ℝ), H (fun s => Real.exp (h * s)) t = h) → (∀ (n t : ℝ), 0 < t → H (fun s => s ^ n) t = n / t) → (∀ (R t : ℝ), 0 < R → H (fun x => R) t = 0) → (∀ (c : ℝ), 0 < c → ∀ (a : ℝ → ℝ) (t : ℝ), 0 < a t → DifferentiableAt ℝ a t → H (fun s => c * a s) t = H a t) → (∀ (τ : ℝ) (a : ℝ → ℝ) (t : ℝ), 0 < a (t + τ) → DifferentiableAt ℝ a (t + τ) → H (fun s => a (s + τ)) t = H a (t + τ)) → (∀ (a : ℝ → ℝ) (t : ℝ), 0 < a (-t) → DifferentiableAt ℝ a (-t) → H (fun s => a (-s)) t = -H a (-t)) → HubbleSpec H`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): phrase (hand-written, linted): the Hubble rate of the scale factor `a` at the cosmic time of evaluation `t`; by definition, `hubble a t` is `deriv a t / a t ^ 2`

## Author's paraphrase (hand-written; checked only by prose rules)

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
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Fidelity/Pins.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 03
