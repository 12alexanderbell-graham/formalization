# Item 15

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`:

**then**

- (the scale factor `a` obeys the flat ΛCDM Friedmann expansion law with matter fraction given by the present matter density parameter `Ω` on some neighbourhood of the observation time `t₀`, with a positive Hubble rate at `t₀` and a positive, differentiable scale factor on that neighbourhood) if and only if (`FriedmannLCDM Ω a t₀`)

Program definitions in this claim:

- `FriedmannLCDM Ω a t₀` — SPEC, not pinned, so only the formula shown is checked, not its name (for `Ω : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`): means there is `ρ : ℝ → ℝ` such that there is `Λ : ℝ` such that (`∀ᶠ (t : ℝ) in nhds t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧ ρ t * a t ^ 3 = ρ t₀ * a t₀ ^ 3 ∧ (deriv a t / a t) ^ 2 = ρ t + Λ / 3`) and (`0 < deriv a t₀`) and (`Ω = ρ t₀ / (deriv a t₀ / a t₀) ^ 2`)
- `IsFlatLCDM Ω a t₀` — **PINNED** (pin theorem `flatLCDMSpec2_pins`): phrase (hand-written, linted): the scale factor `a` obeys the flat ΛCDM Friedmann expansion law with matter fraction given by the present matter density parameter `Ω` on some neighbourhood of the observation time `t₀`, with a positive Hubble rate at `t₀` and a positive, differentiable scale factor on that neighbourhood; by definition, means (`0 < hubble a t₀`) and (`∀ᶠ (t : ℝ) in nhds t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧ hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω)`)

## Author's paraphrase (hand-written; checked only by prose rules)

**The program's flat ΛCDM predicate equals the blind textbook Friedmann formulation**, for
every `Ω`, every scale factor `a` and every `t₀`.

## Formal statement (Lean 4)

```lean
theorem isFlatLCDM_iff_friedmann (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) :
    IsFlatLCDM Ω a t₀ ↔ FriedmannLCDM Ω a t₀ := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.IsFlatLCDM`, `Cosmography.hubble`, `Cosmography.redshift`, `Fidelity.FriedmannLCDM`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatLCDM.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `isFlatLCDM_iff_friedmann`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Fidelity/FriedmannLCDM.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 15
