# Item 14

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`:

**assuming**

1. `LumDistSpec2 D`
2. `t ≤ t₀`
3. for every `s : ℝ`, if `s ∈ Set.Icc t t₀`, then `0 < a s`
4. `ContinuousOn a (Set.Icc t t₀)`

**then**

- `comoving a t₀ t = D 0 a t₀ t / (a t₀ * (1 + redshift a t₀ t))`

Program definitions in this claim:

- `AngDistSpec` — SPEC, not pinned: inductive type with constructors `AngDistSpec.mk : ∀ {D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ}, (∀ (a : ℝ → ℝ) (t₀ t : ℝ), t ≤ t₀ → (∀ s ∈ Set.Icc t t₀, 0 < a s) → ContinuousOn a (Set.Icc t t₀) → D 0 a t₀ t = a t * ∫ (s : ℝ) in t..t₀, 1 / a s) → (∀ (a : ℝ → ℝ) (t₀ t : ℝ), t ≤ t₀ → (∀ s ∈ Set.Icc t t₀, 0 < a s) → ContinuousOn a (Set.Icc t t₀) → D 1 a t₀ t = a t * Real.sin (∫ (s : ℝ) in t..t₀, 1 / a s)) → (∀ (a : ℝ → ℝ) (t₀ t : ℝ), t ≤ t₀ → (∀ s ∈ Set.Icc t t₀, 0 < a s) → ContinuousOn a (Set.Icc t t₀) → D (-1) a t₀ t = a t * Real.sinh (∫ (s : ℝ) in t..t₀, 1 / a s)) → (∀ (c : ℝ), 0 < c → ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ), D (c ^ 2 * K) (fun s => c * a s) t₀ t = D K a t₀ t) → (∀ (τ K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ), D K (fun s => a (s + τ)) (t₀ - τ) (t - τ) = D K a t₀ t) → (∀ t ≤ 0, D 0 Real.exp 0 t = 1 - Real.exp t) → (∀ t ≤ 0, D 0 (fun s => Real.exp (-s)) 0 t = Real.exp (-t) - 1) → (∀ (t : ℝ), 0 < t → t ≤ 1 → D (-1) id 1 t = (1 - t ^ 2) / 2) → (∀ (R : ℝ), 0 < R → ∀ (t₀ t : ℝ), t ≤ t₀ → D 1 (fun x => R) t₀ t = R * Real.sin ((t₀ - t) / R)) → (∀ (R : ℝ), 0 < R → ∀ (t₀ t : ℝ), t ≤ t₀ → D 0 (fun x => R) t₀ t = t₀ - t) → AngDistSpec D`
- `LumDistSpec` — SPEC, not pinned: inductive type with constructors `LumDistSpec.mk : ∀ {D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ}, (∀ t ≤ 0, D 0 Real.exp 0 t = (Real.exp (-t) - 1) * Real.exp (-t)) → (∀ (t : ℝ), 0 < t → t ≤ 1 → D (-1) id 1 t = ((1 / t) ^ 2 - 1) / 2) → (∀ (t₀ t : ℝ), t ≤ t₀ → D 1 (fun x => 1) t₀ t = Real.sin (t₀ - t)) → (∀ (c : ℝ), 0 < c → ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ), D (c ^ 2 * K) (fun s => c * a s) t₀ t = D K a t₀ t) → LumDistSpec D`
- `LumDistSpec2` — SPEC, not pinned: inductive type with constructors `LumDistSpec2.mk : ∀ {D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ}, LumDistSpec D → (∃ DA, AngDistSpec DA ∧ ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ), t ≤ t₀ → (∀ s ∈ Set.Icc t t₀, 0 < a s) → ContinuousOn a (Set.Icc t t₀) → D K a t₀ t = (1 + redshift a t₀ t) ^ 2 * DA K a t₀ t) → LumDistSpec2 D`
- `comoving a t₀ t` — **PINNED** (pin theorem `comoving_pins`): the comoving radial distance χ = ∫ from `t` to `t₀` of ds/a(s) (scale factor `a`, c = 1)
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): the redshift a(`t₀`)/a(`t`) − 1, observed at time `t₀`, of light emitted at time `t` (scale factor `a`)

## Author's paraphrase (hand-written; checked only by prose rules)

**Pinning:** the comoving distance is the flat luminosity distance of any `D` meeting
`LumDistSpec2`, divided by `a₀ (1 + z)`.

## Formal statement (Lean 4)

```lean
theorem comoving_pins (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : LumDistSpec2 D) (a : ℝ → ℝ)
    (t₀ t : ℝ) (htt : t ≤ t₀) (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hcont : ContinuousOn a (Set.Icc t t₀)) :
    comoving a t₀ t = D 0 a t₀ t / (a t₀ * (1 + redshift a t₀ t)) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaY.comoving`, `Cosmography.redshift`, `Fidelity.AngDistSpec`, `Fidelity.LumDistSpec`, `Fidelity.LumDistSpec2`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: comoving, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `comoving_pins`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Fidelity/FlatPins.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 14
