# Item 32

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `O : ℝ → (ℝ → ℝ) → ℝ → ℝ`, `K : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. `Omega0Spec O`
2. `0 < a t₀`
3. `DifferentiableAt ℝ a t₀`
4. `deriv a t₀ / a t₀ ≠ 0`

**then**

- `O K a t₀ = omega0 K a t₀`

Program definitions in this claim:

- `Omega0Spec` — SPEC, not pinned: inductive type with constructors `Omega0Spec.mk : ∀ {O : ℝ → (ℝ → ℝ) → ℝ → ℝ}, (∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 → O K a t₀ = 1 + K / (a t₀ ^ 2 * (deriv a t₀ / a t₀) ^ 2)) → (∀ (G ρ K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < G → 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 → (deriv a t₀ / a t₀) ^ 2 = 8 * Real.pi * G / 3 * ρ - K / a t₀ ^ 2 → O K a t₀ = ρ / (3 * (deriv a t₀ / a t₀) ^ 2 / (8 * Real.pi * G))) → (∀ (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 → O 0 a t₀ = 1) → (∀ (t₀ : ℝ), 0 < t₀ → O (-1) (fun s => s) t₀ = 0) → (∀ (t₀ : ℝ), t₀ ≠ 0 → O 1 Real.cosh t₀ = 1 + 1 / Real.sinh t₀ ^ 2) → O 1 (fun s => s) 1 = 2 → (∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 → (1 < O K a t₀ ↔ 0 < K)) → (∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 → (O K a t₀ < 1 ↔ K < 0)) → (∀ (c K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < c → 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 → O (c ^ 2 * K) (fun s => c * a s) t₀ = O K a t₀) → (∀ (τ K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 → O K (fun s => a (s + τ)) (t₀ - τ) = O K a t₀) → (∀ (K : ℝ) (a b : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 → a =ᶠ[nhds t₀] b → O K a t₀ = O K b t₀) → O 1 (fun s => s) 1 ≠ 0 → O 1 (fun s => 2 * s) 1 ≠ 2 → Omega0Spec O`
- `omega0 K a t₀` — **PINNED** (pin theorem `omega0Spec_pins`): the total density parameter Ω₀ = 1 + K/(H₀²·a₀²) at time `t₀` for curvature constant `K` and scale factor `a` (c = 1; H₀, a₀ the Hubble rate and scale factor at `t₀`; Ω_k = 1 − Ω₀)

## Author's paraphrase (hand-written; checked only by prose rules)

**Pinning:** any `O` meeting `Omega0Spec` is `omega0` wherever `a₀ > 0`, `a` is
differentiable at `t₀` and `H₀ ≠ 0`.

## Formal statement (Lean 4)

```lean
theorem omega0Spec_pins (O : ℝ → (ℝ → ℝ) → ℝ → ℝ) (h : Omega0Spec O) (K : ℝ) (a : ℝ → ℝ)
    (t₀ : ℝ) (ha : 0 < a t₀) (hd : DifferentiableAt ℝ a t₀) (hH : deriv a t₀ / a t₀ ≠ 0) :
    O K a t₀ = omega0 K a t₀ := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaK.omega0`, `Cosmography.hubble`, `Fidelity.Omega0Spec`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: omega0.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `omega0Spec_pins`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Fidelity/YOmegaKSpecs.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 32
