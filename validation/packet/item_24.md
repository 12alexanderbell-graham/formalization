# Item 24

**Area:** F9

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI ("testing F(R) gravity by cosmography"), Eq. (11.31), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583, PRD 78, 063504) Eq. (33): the common denominator R of the F(R₀), F″(R₀), F‴(R₀) formulas is wrong, so the printed F(R₀) formula (11.21) fails the paper's own ΛCDM check (11.40); also (11.13) d³R₀/dt³ has a sign error

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`:

**assuming**

1. `0 < Ω`
2. `Ω < 1`
3. `243 * Ω ^ 4 + 540 * Ω ^ 3 - 6264 * Ω ^ 2 + 9360 * Ω - 3328 ≠ 0`

**then**

- it is false that (for every `a : ℝ → ℝ`, for every `F : ℝ → ℝ`, for every `t₀ : ℝ`, if `IsFRCosmo Ω a F t₀`, then if `printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) ≠ 0`, then `F (curv a t₀) / (6 * hubble a t₀ ^ 2) = -(P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)) / printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)`)

Program definitions in this claim:

- `FriedmannEq Ω a F t₀ t` — **PINNED** (pin theorem `friedmannEq_iff_blind`): phrase (hand-written, linted): the metric F(R) gravity Friedmann equation with dust holds with the present matter density parameter `Ω`, the scale factor `a`, the gravity Lagrangian function of Ricci scalar `F`, the present time `t₀` and the time of evaluation `t` (negative Ricci scalar convention, minus the common one; constraint equation of metric F of R gravity in flat FLRW; dust source and kappa squared is one; negative Ricci scalar convention with R taken as curv of `a`; multiplied through by `F` prime with no division; derivatives of `F` are taken with respect to R); by definition, means `3 * deriv F (curv a t) * hubble a t ^ 2 = Checked.Cosmography.FRCosmo.rhoM Ω a t₀ t + (F (curv a t) - curv a t * deriv F (curv a t)) / 2 - 3 * hubble a t * deriv (curv a) t * deriv^[2] F (curv a t)`
- `IsFRCosmo` — COMPOSITE, not pinned: inductive type with constructors `IsFRCosmo.mk : ∀ {Ω : ℝ} {a F : ℝ → ℝ} {t₀ : ℝ}, 0 < a t₀ → 0 < hubble a t₀ → ContDiffAt ℝ 5 a t₀ → ContDiff ℝ 4 F → FriedmannEq Ω a F t₀ t₀ → (∀ᶠ (t : ℝ) in nhds t₀, MasterEq Ω a F t₀ t) → deriv F (curv a t₀) = 1 → deriv^[4] F (curv a t₀) = 0 → IsFRCosmo Ω a F t₀`
- `MasterEq Ω a F t₀ t` — **PINNED** (pin theorem `masterEq_iff_blind`): phrase (hand-written, linted): the metric F(R) gravity second equation with dust holds with the present matter density parameter `Ω`, the scale factor `a`, the gravity Lagrangian function of Ricci scalar `F`, the present time `t₀` and the time of evaluation `t` (negative Ricci scalar convention, minus the common one; Hubble rate derivative equation of metric F of R gravity; flat FLRW with dust source and kappa squared is one; negative Ricci scalar convention with R taken as curv of `a`; multiplied through by minus two `F` prime with no division); by definition, means `-2 * deriv F (curv a t) * deriv (hubble a) t = Checked.Cosmography.FRCosmo.rhoM Ω a t₀ t + deriv^[2] (curv a) t * deriv^[2] F (curv a t) + deriv (curv a) t * (deriv (curv a) t * deriv^[3] F (curv a t) - hubble a t * deriv^[2] F (curv a t))`
- `P0 q j s l` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_P0`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `(j - q - 2) * l - (3 * s + 7 * j + 6 * q ^ 2 + 41 * q + 22) * s - ((3 * q + 16) * j + 20 * q ^ 2 + 64 * q + 12) * j - (3 * q ^ 4 + 25 * q ^ 3 + 96 * q ^ 2 + 72 * q + 20)`
- `Q0 q j s l` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_Q0`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `(q ^ 2 - j * q + 2 * q) * l + (3 * q * s + (4 * q + 6) * j + 6 * q ^ 3 + 44 * q ^ 2 + 22 * q - 12) * s + (2 * j ^ 2 + (3 * q ^ 2 + 10 * q - 6) * j + 17 * q ^ 3 + 52 * q ^ 2 + 54 * q + 36) * j + (3 * q ^ 5 + 28 * q ^ 4 + 118 * q ^ 3 + 72 * q ^ 2 - 76 * q - 64)`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): phrase (hand-written, linted): the cosmographic coefficient with the derivative order of the coefficient `n`, the scale factor `a` and the time of evaluation `t` (`n`-th time derivative of the scale factor over the scale factor divided by the `n`-th power of the Hubble rate; orders 0 and 1 coefficients are one; The order 2 coefficient is minus the deceleration parameter usually written q; The order 3 coefficient is the jerk parameter usually written j; The order 4 coefficient is the snap parameter usually written s; The order 5 coefficient is the lerk parameter usually written l); by definition, `cosmoCoeff n a t` is `iteratedDeriv n a t / (a t * hubble a t ^ n)`
- `curv a t` — **PINNED** (pin theorem `ricciSpec_pins`): phrase (hand-written, linted): the Ricci scalar of flat FLRW with the scale factor `a` and the cosmic time of evaluation `t` (negative convention, de Sitter has negative Ricci scalar; Ricci scalar of a spatially flat FLRW metric; negative convention so de Sitter has minus twelve times Hubble rate squared); by definition, `curv a t` is `-6 * (deriv (hubble a) t + 2 * hubble a t ^ 2)`
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): phrase (hand-written, linted): the deceleration parameter with the scale factor `a` and the cosmic time of evaluation `t` (minus acceleration times scale factor over velocity squared; minus the second time derivative times the scale factor divided by the squared first time derivative; negative value means accelerating expansion); by definition, `decel a t` is `-(deriv (deriv a) t * a t) / deriv a t ^ 2`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): phrase (hand-written, linted): the Hubble rate with the scale factor `a` and the cosmic time of evaluation `t` (logarithmic derivative of the scale factor with respect to cosmic time; positive for expansion and negative for contraction); by definition, `hubble a t` is `deriv a t / a t`
- `printedR q j s l` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedR`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `(j - q - 2) * l - (3 * s - 2 * j + 6 * q ^ 2 + 50 * q + 40) * s + ((3 * q + 10) * j + 11 * q ^ 2 + 4 * q + 18) * j - (3 * q ^ 4 + 34 * q ^ 3 + 246 * q + 104)`

## Author's paraphrase (hand-written; checked only by prose rules)

Division form at every `Ω ∈ (0,1)` where the printed `R` is nonzero in ΛCDM
(`printedR` at ΛCDM is `−(243Ω⁴ + 540Ω³ − 6264Ω² + 9360Ω − 3328)/16`).

## Formal statement (Lean 4)

```lean
theorem printedF0_false_at {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1)
    (hR : 243 * Ω ^ 4 + 540 * Ω ^ 3 - 6264 * Ω ^ 2 + 9360 * Ω - 3328 ≠ 0) :
    ¬ ∀ (a F : ℝ → ℝ) (t₀ : ℝ), IsFRCosmo Ω a F t₀ →
      printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) ≠ 0 →
      F (curv a t₀) / (6 * hubble a t₀ ^ 2) =
        -(P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
            + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀))
          / printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.FRCosmo.FriedmannEq`, `Cosmography.FRCosmo.MasterEq`, `Cosmography.FRCosmo.curv`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.FRCosmo.P0`, `Cosmography.FRCosmo.Q0`, `Cosmography.FRCosmo.printedR`, `Cosmography.FRCosmo.IsFRCosmo`, `Cosmography.FRCosmo.rhoM`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, FriedmannEq, MasterEq, curv, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): P0², Q0², printedR².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `printedF0_false_at`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3, n = 4, n = 5.
- Source file: `Checked/Cosmography/FRCosmo.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 24
