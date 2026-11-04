# Item 51

**Area:** F9

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI ("testing F(R) gravity by cosmography"), Eq. (11.31), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583, PRD 78, 063504) Eq. (33): the common denominator R of the F(R₀), F″(R₀), F‴(R₀) formulas is wrong, so the printed F(R₀) formula (11.21) fails the paper's own ΛCDM check (11.40); also (11.13) d³R₀/dt³ has a sign error

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`:

**assuming**

1. `0 < Ω`
2. `Ω < 1`

**then**

- it is false that (for every `a : ℝ → ℝ`, for every `F : ℝ → ℝ`, for every `t₀ : ℝ`, if `IsFRCosmo Ω a F t₀`, then `printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * F (curv a t₀) = -6 * hubble a t₀ ^ 2 * (P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀))`)

Program definitions in this claim:

- `FriedmannEq Ω a F t₀ t` — **PINNED** (pin theorem `friedmannEq_iff_blind`): the expansion-rate (Friedmann) equation of metric F(R) gravity with dust, Bamba et al. 2012 Eqs. (11.1)–(11.2) multiplied by 3F′(R), holds at time `t` for the scale factor `a`, the function F = `F` and dust density parameter `Ω` referred to time `t₀`
- `IsFRCosmo` — COMPOSITE, not pinned: inductive type with constructors `IsFRCosmo.mk : ∀ {Ω : ℝ} {a F : ℝ → ℝ} {t₀ : ℝ}, 0 < a t₀ → 0 < hubble a t₀ → ContDiffAt ℝ 5 a t₀ → ContDiff ℝ 4 F → FriedmannEq Ω a F t₀ t₀ → (∀ᶠ (t : ℝ) in nhds t₀, MasterEq Ω a F t₀ t) → deriv F (curv a t₀) = 1 → deriv^[4] F (curv a t₀) = 0 → IsFRCosmo Ω a F t₀`
- `MasterEq Ω a F t₀ t` — **PINNED** (pin theorem `masterEq_iff_blind`): the second field equation of metric F(R) gravity with dust, Bamba et al. 2012 Eq. (11.5) multiplied by −2F′(R), holds at time `t` for the scale factor `a`, the function F = `F` and dust density parameter `Ω` referred to time `t₀`
- `P0 q j s l` — PRINTED, not pinned, so only the formula shown is checked, not its name (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `(j - q - 2) * l - (3 * s + 7 * j + 6 * q ^ 2 + 41 * q + 22) * s - ((3 * q + 16) * j + 20 * q ^ 2 + 64 * q + 12) * j - (3 * q ^ 4 + 25 * q ^ 3 + 96 * q ^ 2 + 72 * q + 20)`
- `Q0 q j s l` — PRINTED, not pinned, so only the formula shown is checked, not its name (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `(q ^ 2 - j * q + 2 * q) * l + (3 * q * s + (4 * q + 6) * j + 6 * q ^ 3 + 44 * q ^ 2 + 22 * q - 12) * s + (2 * j ^ 2 + (3 * q ^ 2 + 10 * q - 6) * j + 17 * q ^ 3 + 52 * q ^ 2 + 54 * q + 36) * j + (3 * q ^ 5 + 28 * q ^ 4 + 118 * q ^ 3 + 72 * q ^ 2 - 76 * q - 64)`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)
- `curv a t` — **PINNED** (pin theorem `ricciSpec_pins`): the Ricci scalar R = −6(Ḣ + 2H²) of spatially flat FLRW with scale factor `a` at time `t` (sign convention of Bamba et al. 2012, Eq. (11.6))
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): the deceleration parameter −a″(t)·a(t)/a′(t)² of the scale factor `a` at time `t`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): the Hubble rate a′(t)/a(t) of the scale factor `a` at time `t`
- `printedR q j s l` — PRINTED, not pinned, so only the formula shown is checked, not its name (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `(j - q - 2) * l - (3 * s - 2 * j + 6 * q ^ 2 + 50 * q + 40) * s + ((3 * q + 10) * j + 11 * q ^ 2 + 4 * q + 18) * j - (3 * q ^ 4 + 34 * q ^ 3 + 246 * q + 104)`

## Author's paraphrase (hand-written; checked only by prose rules)

The multiplied-out printed relation fails in ΛCDM at every `Ω ∈ (0,1)`.

## Formal statement (Lean 4)

```lean
theorem printedF0Mul_false_at {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    ¬ ∀ (a F : ℝ → ℝ) (t₀ : ℝ), IsFRCosmo Ω a F t₀ →
      printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)
          * F (curv a t₀) =
        -6 * hubble a t₀ ^ 2 *
          (P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
            + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.FRCosmo.FriedmannEq`, `Cosmography.FRCosmo.MasterEq`, `Cosmography.FRCosmo.curv`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.FRCosmo.P0`, `Cosmography.FRCosmo.Q0`, `Cosmography.FRCosmo.printedR`, `Chemistry.RKReduced.q`, `Cosmography.FRCosmo.IsFRCosmo`, `Cosmography.FRCosmo.rhoM`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, FriedmannEq, MasterEq, curv, decel, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): P0², Q0², printedR².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `printedF0Mul_false_at`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 3, n = 4, n = 5.
- Source file: `Checked/Cosmography/FRCosmo.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 51
