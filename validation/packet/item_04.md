# Item 04

**Area:** F0

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** textbook definition of lookback time and the cosmographic parameters (e.g. Visser 2004, Class. Quantum Grav. 21, 2603)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** the statement is proved in module `Checked.Cosmography.Lookback` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source):** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; non-vacuity: the Checked theorem `Checked.Trust.NV.lookback_second_order` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 4 numbered; 2 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 2 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); statement literals: no blind second reading registered; 4 literals of the statement are grandfathered as never read twice (`scripts/trust/literal_baseline.txt`); the statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. `∀ᶠ (t : ℝ) in nhds t₀, DifferentiableAt ℝ a t`
2. `DifferentiableAt ℝ (deriv a) t₀`
3. `a t₀ ≠ 0`
4. `deriv a t₀ ≠ 0`

**then**

- `(fun t => t₀ - t - (redshift a t₀ t - (1 + decel a t₀ / 2) * redshift a t₀ t ^ 2) / hubble a t₀) =o[nhds t₀] fun t => redshift a t₀ t ^ 2`

Program definitions in this claim:

- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): phrase (hand-written, linted): the deceleration parameter with the scale factor `a` and the cosmic time of evaluation `t` (minus acceleration times scale factor over velocity squared; minus the second time derivative times the scale factor divided by the squared first time derivative; negative value means accelerating expansion); by definition, `decel a t` is `-(deriv (deriv a) t * a t) / deriv a t ^ 2`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «negative value means accelerating expansion» only assuming `0 < a t`; `0 < deriv a t`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): phrase (hand-written, linted): the Hubble rate with the scale factor `a` and the cosmic time of evaluation `t` (logarithmic derivative of the scale factor with respect to cosmic time; positive for expansion and negative for contraction); by definition, `hubble a t` is `deriv a t / a t`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «logarithmic derivative of the scale factor with respect to cosmic time» only assuming `0 < a t`; `DifferentiableAt ℝ a t`, «positive for expansion and negative for contraction» only assuming `0 < a t`; `0 < deriv a t`, «positive for expansion and negative for contraction» only assuming `0 < a t`; `deriv a t < 0`
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): phrase (hand-written, linted): the cosmological redshift with the scale factor `a`, the observation time `t₀` and the emission time `t` (positive when emission precedes observation in an expanding universe; one plus redshift is the scale factor at observation over that at emission; negative redshift is blueshift; zero when emission and observation coincide); by definition, `redshift a t₀ t` is `a t₀ / a t - 1`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «positive when emission precedes observation in an expanding universe» only assuming for every `s : ℝ`, `0 < a s`; `StrictMono a`; `t < t₀`, «one plus redshift is the scale factor at observation over that at emission», «zero when emission and observation coincide» only assuming `a t₀ ≠ 0`

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

## Your answers: use ANSWER_FORM.md, item 04
