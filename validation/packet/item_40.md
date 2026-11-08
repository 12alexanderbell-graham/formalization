# Item 40

**Area:** F9

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI ("testing F(R) gravity by cosmography"), Eq. (11.31), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583, PRD 78, 063504) Eq. (33): the common denominator R of the F(R₀), F″(R₀), F‴(R₀) formulas is wrong, so the printed F(R₀) formula (11.21) fails the paper's own ΛCDM check (11.40); also (11.13) d³R₀/dt³ has a sign error

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`:

**assuming**

1. `0 < Ω`
2. `Ω < 1`

**then**

- there is `a : ℝ → ℝ` such that there is `t₀ : ℝ` such that (the scale factor `a` obeys the flat ΛCDM expansion law H = H₀·√(`Ω`·(1 + z)³ + 1 − `Ω`) on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0, z is the redshift observed at `t₀`, and a is positive and differentiable on that neighbourhood) and (`IsFRCosmo Ω a (fun R => R + 6 * hubble a t₀ ^ 2 * (1 - Ω)) t₀`)

Program definitions in this claim:

- `FriedmannEq Ω a F t₀ t` — **PINNED** (pin theorem `friedmannEq_iff_blind`): the expansion-rate (Friedmann) equation of metric F(R) gravity with dust, Bamba et al. 2012 Eqs. (11.1)–(11.2) multiplied by 3F′(R), holds at time `t` for the scale factor `a`, the function F = `F` and dust density parameter `Ω` referred to time `t₀`
- `IsFRCosmo` — COMPOSITE, not pinned: inductive type with constructors `IsFRCosmo.mk : ∀ {Ω : ℝ} {a F : ℝ → ℝ} {t₀ : ℝ}, 0 < a t₀ → 0 < hubble a t₀ → ContDiffAt ℝ 5 a t₀ → ContDiff ℝ 4 F → FriedmannEq Ω a F t₀ t₀ → (∀ᶠ (t : ℝ) in nhds t₀, MasterEq Ω a F t₀ t) → deriv F (curv a t₀) = 1 → deriv^[4] F (curv a t₀) = 0 → IsFRCosmo Ω a F t₀`
- `IsFlatLCDM Ω a t₀` — **PINNED** (pin theorem `flatLCDMSpec2_pins`): the scale factor `a` obeys the flat ΛCDM expansion law H = H₀·√(`Ω`·(1 + z)³ + 1 − `Ω`) on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0, z is the redshift observed at `t₀`, and a is positive and differentiable on that neighbourhood
- `MasterEq Ω a F t₀ t` — **PINNED** (pin theorem `masterEq_iff_blind`): the second field equation of metric F(R) gravity with dust, Bamba et al. 2012 Eq. (11.5) multiplied by −2F′(R), holds at time `t` for the scale factor `a`, the function F = `F` and dust density parameter `Ω` referred to time `t₀`
- `curv a t` — **PINNED** (pin theorem `ricciSpec_pins`): the Ricci scalar R = −6(Ḣ + 2H²) of spatially flat FLRW with scale factor `a` at time `t` (sign convention of Bamba et al. 2012, Eq. (11.6))
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): the Hubble rate a′(t)/a(t) of the scale factor `a` at time `t`

## Author's paraphrase (hand-written; checked only by prose rules)

(11.40), the paper's own check: for every `Ω ∈ (0,1)` there is a flat ΛCDM scale factor
which, with `F(R) = R + 2Λ`, `Λ = 3H₀²(1 − Ω)`, satisfies every hypothesis of `IsFRCosmo`.

## Formal statement (Lean 4)

```lean
theorem exists_LCDM_model {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    ∃ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ ∧
      IsFRCosmo Ω a (fun R => R + 6 * hubble a t₀ ^ 2 * (1 - Ω)) t₀ := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.IsFlatLCDM`, `Cosmography.FRCosmo.FriedmannEq`, `Cosmography.FRCosmo.MasterEq`, `Cosmography.FRCosmo.curv`, `Cosmography.hubble`, `Cosmography.FRCosmo.IsFRCosmo`, `Cosmography.FRCosmo.rhoM`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatLCDM, FriedmannEq, MasterEq, curv, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `exists_LCDM_model`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Cosmography/FRCosmo.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 40
