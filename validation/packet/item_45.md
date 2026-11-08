# Item 45

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Rc : (ℝ → ℝ) → ℝ → ℝ`, `a : ℝ → ℝ`, `a' : ℝ → ℝ`, `a'' : ℝ → ℝ`, `t : ℝ`:

**assuming**

1. `RicciFlatFLRWSpec Rc`
2. `0 < a t`
3. `∀ᶠ (s : ℝ) in nhds t, HasDerivAt a (a' s) s`
4. `HasDerivAt a' (a'' t) t`

**then**

- `Rc a t = curv a t`

Program definitions in this claim:

- `RicciFlatFLRWSpec` — SPEC, not pinned: inductive type with constructors `RicciFlatFLRWSpec.mk : ∀ {Rc : (ℝ → ℝ) → ℝ → ℝ}, (∀ (a a' a'' : ℝ → ℝ) (t : ℝ), 0 < a t → (∀ᶠ (s : ℝ) in nhds t, HasDerivAt a (a' s) s) → HasDerivAt a' (a'' t) t → Rc a t = -6 * (a'' t / a t + (a' t / a t) ^ 2)) → (∀ (c h t : ℝ), 0 < c → Rc (fun s => c * Real.exp (h * s)) t = -12 * h ^ 2) → (∀ (t : ℝ), 0 < t → Rc (fun s => s ^ (1 / 2)) t = 0) → (∀ (t : ℝ), 0 < t → Rc (fun s => s ^ (2 / 3)) t = -4 / (3 * t ^ 2)) → (∀ (a a' a'' : ℝ → ℝ) (c t : ℝ), 0 < c → 0 < a t → (∀ᶠ (s : ℝ) in nhds t, HasDerivAt a (a' s) s) → HasDerivAt a' (a'' t) t → Rc (fun s => c * a s) t = Rc a t) → (∀ (a a' a'' : ℝ → ℝ) (τ t : ℝ), 0 < a (t + τ) → (∀ᶠ (s : ℝ) in nhds (t + τ), HasDerivAt a (a' s) s) → HasDerivAt a' (a'' (t + τ)) (t + τ) → Rc (fun s => a (s + τ)) t = Rc a (t + τ)) → RicciFlatFLRWSpec Rc`
- `curv a t` — **PINNED** (pin theorem `ricciSpec_pins`): phrase (hand-written, linted): the Ricci scalar of spatially flat FLRW with scale factor `a` at time `t` (sign convention of Bamba et al. 2012, Eq. (11.6)); by definition, `curv a t` is `-6 * (deriv (hubble a) t + 2 * hubble a t ^ 2)`

## Author's paraphrase (hand-written; checked only by prose rules)

**Pinning:** any `Rc` meeting `RicciFlatFLRWSpec` is `curv` wherever `a > 0` is twice
differentiable at `t`.

## Formal statement (Lean 4)

```lean
theorem ricciSpec_pins (Rc : (ℝ → ℝ) → ℝ → ℝ) (h : RicciFlatFLRWSpec Rc) (a a' a'' : ℝ → ℝ)
    (t : ℝ) (ha : 0 < a t) (h1 : ∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s)
    (h2 : HasDerivAt a' (a'' t) t) : Rc a t = curv a t := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.FRCosmo.curv`, `Cosmography.hubble`, `Fidelity.RicciFlatFLRWSpec`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: curv.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `ricciSpec_pins`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Fidelity/FRSpecs.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 45
