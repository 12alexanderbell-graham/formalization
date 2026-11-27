# Item 43

**Area:** Rigorous simulation of a stiff network

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** **The source's own form, as a blind reader wrote it from the source without seeing this statement (each body occurs in the statement below, `check_literals.py`):** `Checked.Trust.SecondReading.robK1` := `4 / 100`; `Checked.Trust.SecondReading.robK2` := `10 ^ 4`; `Checked.Trust.SecondReading.robK3` := `3 * 10 ^ 7`; `Checked.Trust.SecondReading.robInit` := `(1, 0, 0)`; `Checked.Trust.SecondReading.robT` := `40`. the statement is proved in module `Checked.Sim.Robertson` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source), in two parts. (A) Re-derived by the kernel from the statement; holds whoever wrote the statement, its witnesses and its proofs; shows the statement is not vacuous and which hypotheses matter, not that it says what its source says:** non-vacuity: nothing to witness (the statement has no hypothesis to meet); hypotheses: none numbered; no assumption outside the numbering (`TRUST_MAP.md`, shape); part A complete. **(B) Rests on who wrote a statement; CI checks the route of each item (commit order, briefs without the answer), not that its writer was independent of the authors, so each item is evidence of meaning only as far as that independence holds:** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; statement literals: 5 definitions written by a blind second reader of the source are registered for this statement in `scripts/trust/literal_readings.txt` and occur in it (`check_literals.py`) (source names backed by the readers: Robertson) (printed at the head of this line); no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); program definitions the claim uses (listed under the claim): 1 pinned by a specification the program wrote (the kernel checks that the specification determines the definition, not that it says what the source means), 1 of them also determined by a blind reader's specification that they meet (on the domain printed with the definition), 0 with a blind second reading or formulation, 0 with neither (only the formula printed is checked). The statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**It holds that**

- there is `y₁ : ℝ → ℝ` such that there is `y₂ : ℝ → ℝ` such that there is `y₃ : ℝ → ℝ` such that the concentration of species A over time `y₁`, the concentration of species B over time `y₂` and the concentration of species C over time `y₃` are a Robertson chemical kinetics initial value problem solution with the rate constant of the first reaction `k₁ := 1 / 25`, the rate constant of the second reaction `k₂ := 10000`, the rate constant of the third reaction `k₃ := 30000000`, the initial concentration of species A `a₀ := 1`, the initial concentration of species B `b₀ := 0`, the initial concentration of species C `c₀ := 0` and the final time of the interval `T := 40` (A converts to B with rate constant `k₁ := 1 / 25`; B plus C gives A plus C with rate constant `k₂ := 10000`; two B give B plus C with rate constant `k₃ := 30000000`; `y₁` `y₂` `y₃` are concentrations of A B C; holds on the closed time interval from zero to `T := 40`)

Program definitions in this claim:

- `IsRobSolution k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃` — **PINNED** (pin theorem `robSpec_pins`): phrase (hand-written, linted): the concentration of species A over time `y₁`, the concentration of species B over time `y₂` and the concentration of species C over time `y₃` are a Robertson chemical kinetics initial value problem solution with the rate constant of the first reaction `k₁`, the rate constant of the second reaction `k₂`, the rate constant of the third reaction `k₃`, the initial concentration of species A `a₀`, the initial concentration of species B `b₀`, the initial concentration of species C `c₀` and the final time of the interval `T` (A converts to B with rate constant `k₁`; B plus C gives A plus C with rate constant `k₂`; two B give B plus C with rate constant `k₃`; `y₁` `y₂` `y₃` are concentrations of A B C; holds on the closed time interval from zero to `T`); by definition, means (`y₁ 0 = a₀`) and (`y₂ 0 = b₀`) and (`y₃ 0 = c₀`) and (for every `t : ℝ`, if `t ∈ Set.Icc 0 T`, then (`HasDerivWithinAt y₁ (-k₁ * y₁ t + k₂ * y₂ t * y₃ t) (Set.Icc 0 T) t`) and (`HasDerivWithinAt y₂ (k₁ * y₁ t - k₂ * y₂ t * y₃ t - k₃ * y₂ t ^ 2) (Set.Icc 0 T) t`) and (`HasDerivWithinAt y₃ (k₃ * y₂ t ^ 2) (Set.Icc 0 T) t`)). Blind specification readings (part B: a reader who did not see the pinning specification wrote one from the source; `Checked/Trust/SpecAgreement*.lean`): reader E (from memory) AGREES: the definition meets the reader's specification (`Checked.Trust.SpecAgreement.meets_IsRobSolution_E`) and the reader's specification `Checked.Trust.SecondReadingSpecE.RobSpecE` determines it (`Checked.Trust.SpecAgreement.pins_IsRobSolution_E`); reader F (from memory) DISAGREES: the definition does not meet the reader's specification (`Checked.Trust.SpecAgreement.not_meets_IsRobSolution_F`); the reader's specification `Checked.Trust.SecondReadingSpecF.RobSpecF` determines it (`Checked.Trust.SpecAgreement.pins_IsRobSolution_F`) assuming `0 ≤ T`

## Author's paraphrase (hand-written; checked only by prose rules)

There is a solution of the rate equations of Robertson's network on [0, 40] with k₁ = 1/25,
k₂ = 10⁴, k₃ = 3·10⁷ and initial concentrations (1, 0, 0).

## Formal statement (Lean 4)

```lean
theorem rob_exists : ∃ y₁ y₂ y₃ : ℝ → ℝ,
    IsRobSolution (1 / 25) 10000 30000000 1 0 0 40 y₁ y₂ y₃ := …
```

## Definitions it uses

See GLOSSARY.md: `Sim.Robertson.IsRobSolution`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsRobSolution.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): IsRobSolution: k₁ = 1/25, k₂ = 10000, k₃ = 30000000, a₀ = 1, b₀ = 0, c₀ = 0, T = 40.
- Source file: `Checked/Sim/Robertson.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 43
