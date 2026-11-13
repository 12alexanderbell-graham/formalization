# Item 12

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Z : (ℝ → ℝ) → ℝ → ℝ → ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`:

**assuming**

1. `RedshiftSpecCore Z`
2. `RayOK a t t₀`

**then**

- `Z a t₀ t = redshift a t₀ t`

Program definitions in this claim:

- `RayOK a t t₀` — SPEC, not pinned, so only the formula shown is checked, not its name (for `a : ℝ → ℝ`, `t : ℝ`, `t₀ : ℝ`): means (for every `s : ℝ`, if `s ∈ Set.uIcc t t₀`, then `0 < a s`) and (`ContDiffOn ℝ 1 a (Set.uIcc t t₀)`)
- `RedshiftSpecCore` — SPEC, not pinned: inductive type with constructors `RedshiftSpecCore.mk : ∀ {Z : (ℝ → ℝ) → ℝ → ℝ → ℝ}, (∀ (a : ℝ → ℝ) (t₀ t : ℝ), RayOK a t t₀ → 1 + Z a t₀ t = Real.exp (∫ (s : ℝ) in t..t₀, deriv a s / a s)) → (∀ (a : ℝ → ℝ) (t₀ t : ℝ), RayOK a t t₀ → 1 + Z a t₀ t = a t₀ / a t) → (∀ (a : ℝ → ℝ) (t : ℝ), 0 < a t → Z a t t = 0) → (∀ (a : ℝ → ℝ) (t t₁ t₀ : ℝ), RayOK a t t₁ → RayOK a t₁ t₀ → 1 + Z a t₀ t = (1 + Z a t₀ t₁) * (1 + Z a t₁ t)) → (∀ (a : ℝ → ℝ) (c t₀ t : ℝ), 0 < c → RayOK a t t₀ → Z (fun s => c * a s) t₀ t = Z a t₀ t) → (∀ (a : ℝ → ℝ) (τ t₀ t : ℝ), RayOK a (t + τ) (t₀ + τ) → Z (fun s => a (s + τ)) t₀ t = Z a (t₀ + τ) (t + τ)) → (∀ (a b : ℝ → ℝ) (t₀ t : ℝ), RayOK a t t₀ → Set.EqOn a b (Set.uIcc t t₀) → Z b t₀ t = Z a t₀ t) → (∀ (a : ℝ → ℝ) (t₀ t : ℝ), t < t₀ → RayOK a t t₀ → (∀ s ∈ Set.Ioo t t₀, 0 < deriv a s) → 0 < Z a t₀ t) → (∀ (A h t₀ t : ℝ), 0 < A → Z (fun s => A * Real.exp (h * s)) t₀ t = Real.exp (h * (t₀ - t)) - 1) → (∀ (p t₀ t : ℝ), 0 < t → 0 < t₀ → Z (fun s => s ^ p) t₀ t = t₀ ^ p / t ^ p - 1) → (∀ (t₀ t : ℝ), 0 < t → 0 < t₀ → Z (fun s => s) t₀ t = t₀ / t - 1) → (∀ (A t₀ t : ℝ), 0 < A → Z (fun x => A) t₀ t = 0) → Z (fun s => Real.exp s) 1 0 ≠ 1 → Z (fun s => Real.exp s) 1 0 ≠ Real.exp (-1) - 1 → RedshiftSpecCore Z`
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): phrase (hand-written, linted): the cosmological redshift with the scale factor `a`, the observation time `t₀` and the emission time `t` (positive when emission precedes observation in an expanding universe; one plus redshift is the scale factor at observation over that at emission; negative redshift is blueshift; zero when emission and observation coincide); by definition, `redshift a t₀ t` is `a t₀ / a t - 1`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «positive when emission precedes observation in an expanding universe» only assuming for every `s : ℝ`, `0 < a s`; `StrictMono a`; `t < t₀`, «one plus redshift is the scale factor at observation over that at emission», «zero when emission and observation coincide» only assuming `a t₀ ≠ 0`

## Author's paraphrase (hand-written; checked only by prose rules)

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
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Fidelity/RedshiftCoeffSpecs.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 12
