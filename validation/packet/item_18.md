# Item 18

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `P : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop`:

**assuming**

1. for every `Ω : ℝ`, for every `w₀ : ℝ`, for every `wₐ : ℝ`, for every `a : ℝ → ℝ`, for every `t₀ : ℝ`, (`P Ω w₀ wₐ a t₀`) if and only if (`FriedmannCPL Ω w₀ wₐ a t₀`)

**then**

- `P = IsFlatCPL`

Program definitions in this claim:

- `FriedmannCPL Ω w₀ wₐ a t₀` — SPEC, not pinned (for `Ω : ℝ`, `w₀ : ℝ`, `wₐ : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`): means there is `ρm : ℝ → ℝ` such that there is `ρde : ℝ → ℝ` such that (`∀ᶠ (t : ℝ) in nhds t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧ (deriv a t / a t) ^ 2 = ρm t + ρde t ∧ ρm t * a t ^ 3 = ρm t₀ * a t₀ ^ 3 ∧ HasDerivAt ρde (-(3 * (deriv a t / a t) * (1 + (w₀ + wₐ * (1 - a t / a t₀))) * ρde t)) t`) and (`0 < deriv a t₀`) and (`Ω = ρm t₀ / (deriv a t₀ / a t₀) ^ 2`)
- `IsFlatCPL Ω w₀ wₐ a t₀` — **PINNED** (pin theorem `flatCPL_pins`): the scale factor `a` obeys the flat matter + CPL dark-energy expansion law H = H₀·√(Ω(1 + z)³ + (1 − Ω)(1 + z)^(3(1 + w₀ + wₐ))·exp(−3wₐz/(1 + z))) with Ω = `Ω`, w₀ = `w₀`, wₐ = `wₐ`, on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0 and a is positive and differentiable on that neighbourhood

## Author's paraphrase (hand-written; checked only by prose rules)

**Pinning:** any predicate obeying the blind first-principles law is `IsFlatCPL`.

## Formal statement (Lean 4)

```lean
theorem flatCPL_pins (P : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop)
    (h : ∀ Ω w₀ wₐ a t₀, P Ω w₀ wₐ a t₀ ↔ FriedmannCPL Ω w₀ wₐ a t₀) : P = IsFlatCPL := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.CPL.IsFlatCPL`, `Cosmography.hubble`, `Cosmography.redshift`, `Fidelity.FriedmannCPL`, `Sim.DuffingExists.G`, `Sim.DuffingExists.cl`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatCPL.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `flatCPL_pins`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Fidelity/FriedmannCPL.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 18
