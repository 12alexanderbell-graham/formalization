# Item 27

**Area:** Fluid mechanics

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** **The source's own form, as a blind reader wrote it from the source without seeing this statement (each body occurs in the statement below, `check_literals.py`):** `Checked.Trust.SecondReading.hiemenzRhs` := `fun f p q η => -(f η * q η) - 1 + p η ^ 2`; `Checked.Trust.SecondReading.hiemenzWindowTyped` := `fun S => Set.Icc 0 S`; `Checked.Trust.SecondReading.hiemenzWindow` := `fun S => Set.Icc 0 S`; `Checked.Trust.SecondReading.hiemenzWall` := `fun g => g 0 = 0`; `Checked.Trust.SecondReading.hiemenzStartLow` := `fun q => q 0 = 1.2325876568`; `Checked.Trust.SecondReading.hiemenzHorizon` := `Set.Ioc 0 (15 / 2)`. the statement is proved in module `Checked.Hiemenz.Hiemenz` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source), in two parts. (A) Re-derived by the kernel from the statement; holds whoever wrote the statement, its witnesses and its proofs; shows the statement is not vacuous and which hypotheses matter, not that it says what its source says:** non-vacuity: the Checked theorem `Checked.Trust.NV.hiemenz_under` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 7 numbered; 7 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 0 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); no assumption outside the numbering (`TRUST_MAP.md`, shape); part A complete. **(B) Rests on who wrote a statement; CI checks the route of each item (commit order, briefs without the answer), not that its writer was independent of the authors, so each item is evidence of meaning only as far as that independence holds:** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; statement literals: 6 definitions written by a blind second reader of the source are registered for this statement in `scripts/trust/literal_readings.txt` and occur in it (`check_literals.py`) (printed at the head of this line); no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); program definitions the claim uses: none. The statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `S : ℝ`, `f : ℝ → ℝ`, `p : ℝ → ℝ`, `q : ℝ → ℝ`:

**assuming**

1. `15 / 2 ≤ S`
2. for every `η : ℝ`, if `η ∈ Set.Icc 0 S`, then `HasDerivWithinAt f (p η) (Set.Icc 0 S) η`
3. for every `η : ℝ`, if `η ∈ Set.Icc 0 S`, then `HasDerivWithinAt p (q η) (Set.Icc 0 S) η`
4. for every `η : ℝ`, if `η ∈ Set.Icc 0 S`, then `HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Set.Icc 0 S) η`
5. `f 0 = 0`
6. `p 0 = 0`
7. `q 0 = 1.2325876568`

**then**

- there is `η : ℝ` such that (`η ∈ Set.Ioc 0 (15 / 2)`) and (`q η < 0`) and (for every `s : ℝ`, if `s ∈ Set.Icc 0 η`, then `p s < 1`)

## Author's paraphrase (hand-written; checked only by prose rules)

Hiemenz stagnation-point flow, undershoot: for every S ≥ 15/2 and every solution of
f''' + f f'' + 1 − f'² = 0 on [0, S] (f has derivative p, p has derivative q, q has derivative
−f q − 1 + p², within [0, S]) with f(0) = 0, p(0) = 0 and q(0) = 1.2325876568, there is
η in (0, 15/2] with q(η) < 0 and p < 1 on [0, η].

## Formal statement (Lean 4)

```lean
theorem hiemenz_under (S : ℝ) (hS : 15 / 2 ≤ S) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt f (p η) (Icc 0 S) η)
    (hp : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt p (q η) (Icc 0 S) η)
    (hq : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Icc 0 S) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 1.2325876568) :
    ∃ η ∈ Ioc (0 : ℝ) (15 / 2), q η < 0 ∧ ∀ s ∈ Icc 0 η, p s < 1 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `hiemenz_under`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Hiemenz/Hiemenz.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 27
