# Item 33

**Area:** F1

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** arXiv:1903.11433, Eq. (21): misprinted flat ΛCDM l₀ (printed as 1 + 3Ω_m − (27/2)Ω_m²)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** proved in module `Checked.Cosmography.LCDMCoefficients` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source):** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; non-vacuity: nothing to witness (the statement has no hypothesis to meet); hypotheses: none numbered; statement literals: no blind second reading registered; no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); the statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**It holds that**

- it is false that (`AvilesL0Claim`)

Program definitions in this claim:

- `AvilesL0Claim` — CLAIM, not pinned; the source-dependent data written inline (printed formula, order of the printed series) agree with an independent blind second reading of the source (`Checked.Trust.Transcriptions.agree_AvilesL0Claim`); the quantifiers and hypotheses are the program's formalisation: means for every `Ω : ℝ`, for every `a : ℝ → ℝ`, for every `t₀ : ℝ`, if the scale factor `a` obeys the flat ΛCDM Friedmann expansion law with the present matter density parameter `Ω` and the observation time `t₀` (spatially flat universe with dust and a cosmological constant; `Ω` is the present matter density parameter; holds on a whole neighbourhood of `t₀`; present Hubble rate is positive so the universe is expanding), then if `ContDiffAt ℝ 6 a t₀`, then `cosmoCoeff 5 a t₀ = 1 + 3 * Ω - 27 / 2 * Ω ^ 2`
- `IsFlatLCDM Ω a t₀` — **PINNED** (pin theorem `flatLCDMSpec2_pins`): phrase (hand-written, linted): the scale factor `a` obeys the flat ΛCDM Friedmann expansion law with the present matter density parameter `Ω` and the observation time `t₀` (spatially flat universe with dust and a cosmological constant; `Ω` is the present matter density parameter; holds on a whole neighbourhood of `t₀`; present Hubble rate is positive so the universe is expanding); by definition, means (`0 < hubble a t₀`) and (`∀ᶠ (t : ℝ) in nhds t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧ hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω)`). Phrase lines proved in Lean (statements in PHRASE_LINES.md): «present Hubble rate is positive so the universe is expanding» only assuming the scale factor `a` obeys the flat ΛCDM Friedmann expansion law with the present matter density parameter `Ω` and the observation time `t₀` (spatially flat universe with dust and a cosmological constant; `Ω` is the present matter density parameter; holds on a whole neighbourhood of `t₀`; present Hubble rate is positive so the universe is expanding)
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): phrase (hand-written, linted): the cosmographic coefficient with the derivative order of the coefficient `n`, the scale factor `a` and the time of evaluation `t` (`n`-th time derivative of the scale factor over the scale factor divided by the `n`-th power of the Hubble rate; orders 0 and 1 coefficients are one; The order 2 coefficient is minus the deceleration parameter usually written q; The order 3 coefficient is the jerk parameter usually written j; The order 4 coefficient is the snap parameter usually written s; The order 5 coefficient is the lerk parameter usually written l); by definition, `cosmoCoeff n a t` is `iteratedDeriv n a t / (a t * hubble a t ^ n)`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «orders 0 and 1 coefficients are one» only assuming `a t ≠ 0`; `deriv a t ≠ 0`, «The order 2 coefficient is minus the deceleration parameter usually written q» only assuming `a t ≠ 0`

## Author's paraphrase (hand-written; checked only by prose rules)

**Refutation of the printed l₀ in Eq. (21).** On Einstein–de Sitter (Ω = 1) the printed
formula gives `−19/2`, the true value is `35/2`.

## Formal statement (Lean 4)

```lean
theorem avilesL0Claim_false : ¬ AvilesL0Claim := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.IsFlatLCDM`, `Cosmography.Aviles.cosmoCoeff`, `Cosmography.Aviles.AvilesL0Claim`, `Cosmography.hubble`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatLCDM, cosmoCoeff.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): AvilesL0Claim².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 5.
- Source file: `Checked/Cosmography/LCDMCoefficients.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 33
