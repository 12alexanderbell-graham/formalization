# Item 13

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`, `a : ℝ → ℝ`, `F : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`:

**then**

- (the second field equation of metric F(R) gravity with dust, Bamba et al. 2012 Eq. (11.5) multiplied by −2F′(R), holds at time `t` for the scale factor `a`, the function F = `F` and dust density parameter `Ω` referred to time `t₀`) if and only if (`FRSecondEq Ω a F t₀ t (curv a)`)

Program definitions in this claim:

- `DustDensity Ω a t₀ t` — SPEC, not pinned, so only the formula shown is checked, not its name (for `Ω : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`): is defined as `3 * (deriv a t₀ / a t₀) ^ 2 * Ω * (a t₀ / a t) ^ 3`
- `FRSecondEq Ω a F t₀ t R` — SPEC, not pinned, so only the formula shown is checked, not its name (for `Ω : ℝ`, `a : ℝ → ℝ`, `F : ℝ → ℝ`, `t₀ : ℝ`, `t : ℝ`, `R : ℝ → ℝ`): means `-2 * deriv F (R t) * deriv (fun s => deriv a s / a s) t = DustDensity Ω a t₀ t + deriv^[3] F (R t) * deriv R t ^ 2 + deriv^[2] F (R t) * deriv^[2] R t - deriv a t / a t * deriv^[2] F (R t) * deriv R t`
- `MasterEq Ω a F t₀ t` — **PINNED** (pin theorem `masterEq_iff_blind`): the second field equation of metric F(R) gravity with dust, Bamba et al. 2012 Eq. (11.5) multiplied by −2F′(R), holds at time `t` for the scale factor `a`, the function F = `F` and dust density parameter `Ω` referred to time `t₀`
- `curv a t` — **PINNED** (pin theorem `ricciSpec_pins`): the Ricci scalar R = −6(Ḣ + 2H²) of spatially flat FLRW with scale factor `a` at time `t` (sign convention of Bamba et al. 2012, Eq. (11.6))

## Author's paraphrase (hand-written; checked only by prose rules)

The program's master equation is the blind `Ḣ` equation with `R = curv a`.

## Formal statement (Lean 4)

```lean
theorem masterEq_iff_blind (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) :
    MasterEq Ω a F t₀ t ↔ FRSecondEq Ω a F t₀ t (curv a) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.FRCosmo.MasterEq`, `Cosmography.FRCosmo.curv`, `Cosmography.FRCosmo.rhoM`, `Cosmography.hubble`, `Fidelity.DustDensity`, `Fidelity.FRSecondEq`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: MasterEq, curv.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `masterEq_iff_blind`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Fidelity/FRSpecs.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 13
