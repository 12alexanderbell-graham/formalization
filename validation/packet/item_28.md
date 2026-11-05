# Item 28

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `C : ℕ → (ℝ → ℝ) → ℝ → ℝ`, `n : ℕ`, `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. `CosmoCoeffSpecCore C`
2. `CoeffOK n a t₀`

**then**

- `C n a t₀ = cosmoCoeff n a t₀`

Program definitions in this claim:

- `CoeffOK n a t` — SPEC, not pinned, so only the formula shown is checked, not its name (for `n : ℕ`, `a : ℝ → ℝ`, `t : ℝ`): means (`0 < a t`) and (`ContDiffAt ℝ (↑n) a t`) and (`deriv a t ≠ 0`)
- `CosmoCoeffSpecCore` — SPEC, not pinned: inductive type with constructors `CosmoCoeffSpecCore.mk : ∀ {C : ℕ → (ℝ → ℝ) → ℝ → ℝ}, (∀ (n : ℕ) (a : ℝ → ℝ) (t : ℝ), CoeffOK n a t → C n a t = iteratedDeriv n a t / (a t * (deriv a t / a t) ^ n)) → (∀ (n : ℕ) (a : ℝ → ℝ) (t₀ : ℝ), CoeffOK n a t₀ → (fun Δ => a (t₀ + Δ) / a t₀ - ∑ k ∈ Finset.range (n + 1), C k a t₀ * (deriv a t₀ / a t₀ * Δ) ^ k / ↑k.factorial) =o[nhds 0] fun Δ => Δ ^ n) → (∀ (a : ℝ → ℝ) (t : ℝ), CoeffOK 0 a t → C 0 a t = 1) → (∀ (a : ℝ → ℝ) (t : ℝ), CoeffOK 1 a t → C 1 a t = 1) → (∀ (n : ℕ) (a : ℝ → ℝ) (c t : ℝ), 0 < c → CoeffOK n a t → C n (fun s => c * a s) t = C n a t) → (∀ (n : ℕ) (a : ℝ → ℝ) (τ t : ℝ), CoeffOK n a (t + τ) → C n (fun s => a (s + τ)) t = C n a (t + τ)) → (∀ (n : ℕ) (A h t : ℝ), 0 < A → h ≠ 0 → C n (fun s => A * Real.exp (h * s)) t = 1) → (∀ (n : ℕ) (p t : ℝ), 0 < t → p ≠ 0 → C n (fun s => s ^ p) t = (∏ i ∈ Finset.range n, (p - ↑i)) / p ^ n) → (∀ (n : ℕ) (t : ℝ), 0 < t → 2 ≤ n → C n (fun s => s) t = 0) → (∀ (t : ℝ), 0 < t → C 2 (fun s => s ^ (2 / 3)) t = -1 / 2) → (∀ (t : ℝ), 0 < t → C 3 (fun s => s ^ (2 / 3)) t = 1) → C 2 (fun s => s ^ (2 / 3)) 1 ≠ 1 / 2 → C 2 (fun s => Real.exp (2 * s)) 0 ≠ 4 → CosmoCoeffSpecCore C`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)

## Author's paraphrase (hand-written; checked only by prose rules)

**Pinning:** every `C` obeying the cosmographic Taylor law equals `cosmoCoeff` wherever
`a > 0`, `a` is `Cⁿ` near `t₀` and `ȧ(t₀) ≠ 0`.

## Formal statement (Lean 4)

```lean
theorem cosmoCoeffCore_pins (C : ℕ → (ℝ → ℝ) → ℝ → ℝ) (h : CosmoCoeffSpecCore C) (n : ℕ)
    (a : ℝ → ℝ) (t₀ : ℝ) (hok : CoeffOK n a t₀) : C n a t₀ = cosmoCoeff n a t₀ := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.hubble`, `Fidelity.CoeffOK`, `Fidelity.CosmoCoeffSpecCore`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `cosmoCoeffCore_pins`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Fidelity/RedshiftCoeffSpecs.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 28
