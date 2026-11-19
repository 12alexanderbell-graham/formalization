# Item 31

**Area:** F2

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** Capozziello, Lazkoz, Salzano, PRD 84, 124061 (2011), arXiv:1104.3096 (v1 and v2), Eq. (22): flat matter + CPL l₀, w_a² term missing a factor 9

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** the statement is proved in module `Checked.Cosmography.CPLExistence` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source):** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; non-vacuity: the Checked theorem `Checked.Trust.NV.cpl_printedL0_false_at` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 1 numbered; 1 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 0 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); statement literals: no blind second reading registered; 38 literals of the statement are grandfathered as never read twice (`scripts/trust/literal_baseline.txt`); the statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `Ω : ℝ`, `w₀ : ℝ`, `wₐ : ℝ`:

**assuming**

1. `(1 - Ω) * (7 - Ω) * wₐ ≠ 0`

**then**

- there is `a : ℝ → ℝ` such that (the scale factor `a` obeys the flat matter plus CPL dark energy Friedmann expansion law with the present matter density parameter `Ω`, the present dark energy equation of state `w₀`, the equation of state evolution parameter `wₐ` and the observation time `t₀ := 0` (spatially flat universe with dust and separately conserved dark energy; redshift z is measured from `t₀ := 0`; `Ω` is the present matter density parameter; holds on a whole neighbourhood of `t₀ := 0`; present Hubble rate is positive so the universe is expanding)) and (`ContDiffAt ℝ 5 a 0`) and (`cosmoCoeff 5 a 0 ≠ 35 / 2 + (1 - Ω) / 4 * (213 + (7 - Ω) * wₐ) * wₐ + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀ + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2 + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3 + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4`)

Program definitions in this claim:

- `IsFlatCPL Ω w₀ wₐ a t₀` — **PINNED** (pin theorem `flatCPL_pins`): phrase (hand-written, linted): the scale factor `a` obeys the flat matter plus CPL dark energy Friedmann expansion law with the present matter density parameter `Ω`, the present dark energy equation of state `w₀`, the equation of state evolution parameter `wₐ` and the observation time `t₀` (spatially flat universe with dust and separately conserved dark energy; redshift z is measured from `t₀`; `Ω` is the present matter density parameter; holds on a whole neighbourhood of `t₀`; present Hubble rate is positive so the universe is expanding); by definition, means (`0 < hubble a t₀`) and (`∀ᶠ (t : ℝ) in nhds t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧ hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + (1 - Ω) * (1 + redshift a t₀ t) ^ (3 * (1 + w₀ + wₐ)) * Real.exp (-(3 * wₐ * redshift a t₀ t) / (1 + redshift a t₀ t)))`). Phrase lines proved in Lean (statements in PHRASE_LINES.md): «present Hubble rate is positive so the universe is expanding» only assuming the scale factor `a` obeys the flat matter plus CPL dark energy Friedmann expansion law with the present matter density parameter `Ω`, the present dark energy equation of state `w₀`, the equation of state evolution parameter `wₐ` and the observation time `t₀` (spatially flat universe with dust and separately conserved dark energy; redshift z is measured from `t₀`; `Ω` is the present matter density parameter; holds on a whole neighbourhood of `t₀`; present Hubble rate is positive so the universe is expanding)
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): phrase (hand-written, linted): the cosmographic coefficient with the derivative order of the coefficient `n`, the scale factor `a` and the time of evaluation `t` (`n`-th time derivative of the scale factor over the scale factor divided by the `n`-th power of the Hubble rate; orders 0 and 1 coefficients are one; The order 2 coefficient is minus the deceleration parameter usually written q; The order 3 coefficient is the jerk parameter usually written j; The order 4 coefficient is the snap parameter usually written s; The order 5 coefficient is the lerk parameter usually written l); by definition, `cosmoCoeff n a t` is `iteratedDeriv n a t / (a t * hubble a t ^ n)`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «orders 0 and 1 coefficients are one» only assuming `a t ≠ 0`; `deriv a t ≠ 0`, «The order 2 coefficient is minus the deceleration parameter usually written q» only assuming `a t ≠ 0`

## Author's paraphrase (hand-written; checked only by prose rules)

**The printed l₀ of CLS Eq. (22) is false at every parameter point with
`(1 − Ω)(7 − Ω) wₐ ≠ 0`**: there is a flat CPL model with those parameters whose l₀ differs.

## Formal statement (Lean 4)

```lean
theorem printedL0_false_at (Ω w₀ wₐ : ℝ) (hne : (1 - Ω) * (7 - Ω) * wₐ ≠ 0) :
    ∃ a : ℝ → ℝ, IsFlatCPL Ω w₀ wₐ a 0 ∧ ContDiffAt ℝ 5 a 0 ∧
      cosmoCoeff 5 a 0 ≠ 35 / 2 + (1 - Ω) / 4 * (213 + (7 - Ω) * wₐ) * wₐ
        + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀
        + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2
        + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3
        + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.CPL.IsFlatCPL`, `Cosmography.hubble`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, IsFlatCPL.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `cpl_printedL0_false_at`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): IsFlatCPL: t₀ = 0; cosmoCoeff: n = 5, t = 0.
- Source file: `Checked/Cosmography/CPLExistence.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 31
