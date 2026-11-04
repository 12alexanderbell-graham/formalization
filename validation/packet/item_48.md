# Item 48

**Area:** F0

**Source:** textbook definition of lookback time and the cosmographic parameters (e.g. Visser 2004, Class. Quantum Grav. 21, 2603)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. `∀ᶠ (t : ℝ) in nhds t₀, DifferentiableAt ℝ a t`
2. `DifferentiableAt ℝ (deriv a) t₀`
3. `a t₀ ≠ 0`
4. `deriv a t₀ ≠ 0`

**then**

- `(fun t => t₀ - t - (redshift a t₀ t - (1 + decel a t₀ / 2) * redshift a t₀ t ^ 2) / hubble a t₀) =o[nhds t₀] fun t => redshift a t₀ t ^ 2`

Program definitions in this claim:

- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): the deceleration parameter −a″(t)·a(t)/a′(t)² of the scale factor `a` at time `t`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): the Hubble rate a′(t)/a(t) of the scale factor `a` at time `t`
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): the redshift a(`t₀`)/a(`t`) − 1, observed at time `t₀`, of light emitted at time `t` (scale factor `a`)

## Author's paraphrase (hand-written; checked only by prose rules)

**Milestone 1** (frozen in commit 6ef1003, audited in runs/2026-10-30T0028Z/audit.md). The lookback time `t₀ - t` of a source with redshift
`z = z(t)` satisfies `t₀ - t = H₀⁻¹ (z - (1 + q₀/2) z²) + o(z²)` as `t → t₀`.

## Formal statement (Lean 4)

```lean
theorem lookback_second_order (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t)
    (ha' : DifferentiableAt ℝ (deriv a) t₀)
    (ha0 : a t₀ ≠ 0) (hH : deriv a t₀ ≠ 0) :
    (fun t => (t₀ - t) - (redshift a t₀ t - (1 + decel a t₀ / 2) * redshift a t₀ t ^ 2)
        / hubble a t₀)
      =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 2) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `lookback_second_order`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Cosmography/Lookback.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 48
