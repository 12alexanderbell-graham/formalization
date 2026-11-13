# Item 12

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `k : ℝ → (ℝ → ℝ) → ℝ → ℝ`, `K : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. `CurvKSpec k`
2. `0 < a t₀`
3. `DifferentiableAt ℝ a t₀`
4. `deriv a t₀ / a t₀ ≠ 0`

**then**

- `k K a t₀ = curvK K a t₀`

Program definitions in this claim:

- `CurvKSpec` — SPEC, not pinned: inductive type with constructors `CurvKSpec.mk : ∀ {k : ℝ → (ℝ → ℝ) → ℝ → ℝ}, (∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 → k K a t₀ = K / (deriv a t₀ / a t₀ * a t₀) ^ 2) → (∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ ≠ 0 → k K a t₀ = K / deriv a t₀ ^ 2) → (∀ (G ρ K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < G → 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 → (deriv a t₀ / a t₀) ^ 2 = 8 * Real.pi * G / 3 * ρ - K / a t₀ ^ 2 → 8 * Real.pi * G / 3 * ρ / (deriv a t₀ / a t₀) ^ 2 = 1 + k K a t₀) → (∀ (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 → k 0 a t₀ = 0) → (∀ (t₀ : ℝ), 0 < t₀ → k (-1) (fun s => s) t₀ = -1) → (∀ (t₀ : ℝ), t₀ ≠ 0 → k 1 Real.cosh t₀ = 1 / Real.sinh t₀ ^ 2) → (∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 → (0 < k K a t₀ ↔ 0 < K)) → (∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 → (k K a t₀ < 0 ↔ K < 0)) → (∀ (r K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 → k (r * K) a t₀ = r * k K a t₀) → (∀ (c K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < c → 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 → k (c ^ 2 * K) (fun s => c * a s) t₀ = k K a t₀) → (∀ (τ K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 → k K (fun s => a (s + τ)) (t₀ - τ) = k K a t₀) → k (-1) (fun s => s) 1 ≠ 1 → k (-4) (fun s => 2 * s) 1 ≠ -4 → k (-4) (fun s => 2 * s) 1 = -1 → CurvKSpec k`
- `curvK K a t₀` — **PINNED** (pin theorem `curvKSpec_pins`): phrase (hand-written, linted): the dimensionless spatial curvature parameter with the spatial curvature constant `K`, the scale factor `a` and the observation time `t₀` (has sign of curvature constant, minus the curvature density parameter; total density parameter minus one; positive for closed and negative for open); by definition, `curvK K a t₀` is `K / (hubble a t₀ ^ 2 * a t₀ ^ 2)`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «total density parameter minus one», «positive for closed and negative for open» only assuming `hubble a t₀ ≠ 0`; `a t₀ ≠ 0`; `0 < K`, «positive for closed and negative for open» only assuming `hubble a t₀ ≠ 0`; `a t₀ ≠ 0`; `K < 0`

## Author's paraphrase (hand-written; checked only by prose rules)

**Pinning:** any `k` meeting `CurvKSpec` is `curvK` wherever `a₀ > 0`, `a` is
differentiable at `t₀` and `H₀ ≠ 0`.

## Formal statement (Lean 4)

```lean
theorem curvKSpec_pins (k : ℝ → (ℝ → ℝ) → ℝ → ℝ) (h : CurvKSpec k) (K : ℝ) (a : ℝ → ℝ)
    (t₀ : ℝ) (ha : 0 < a t₀) (hd : DifferentiableAt ℝ a t₀) (hH : deriv a t₀ / a t₀ ≠ 0) :
    k K a t₀ = curvK K a t₀ := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaZ.curvK`, `Cosmography.hubble`, `Fidelity.CurvKSpec`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: curvK.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `curvKSpec_pins`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Fidelity/YOmegaKSpecs.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 12
