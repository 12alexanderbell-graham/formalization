# Item 30

**Area:** Fluid mechanics

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** **The source's own form, as a blind reader wrote it from the source without seeing this statement (each body occurs in the statement below, `check_literals.py`):** `Checked.Trust.SecondReading.hiemenzRhs` := `fun f p q η => -(f η * q η) - 1 + p η ^ 2`; `Checked.Trust.SecondReading.hiemenzHalfLineTyped` := `Set.Ici 0`; `Checked.Trust.SecondReading.hiemenzHalfLine` := `Set.Ici 0`; `Checked.Trust.SecondReading.hiemenzWall` := `fun g => g 0 = 0`; `Checked.Trust.SecondReading.hiemenzEdge` := `nhds 1`; `Checked.Trust.SecondReading.hiemenzShear` := `fun q => 1.2325876568 < q 0 ∧ q 0 < 1.2325876569`. the statement is proved in module `Checked.FalknerSkan.Limit` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source):** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; non-vacuity: the Checked theorem `Checked.Trust.NV.hiemenz_limit_window` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 6 numbered; 6 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 0 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); statement literals: 6 definitions written by a blind second reader of the source are registered for this statement in `scripts/trust/literal_readings.txt` and occur in it (`check_literals.py`) (printed at the head of this line); no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); the statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `f : ℝ → ℝ`, `p : ℝ → ℝ`, `q : ℝ → ℝ`:

**assuming**

1. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f (p η) (Set.Ici 0) η`
2. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p (q η) (Set.Ici 0) η`
3. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Set.Ici 0) η`
4. `f 0 = 0`
5. `p 0 = 0`
6. `Filter.Tendsto p Filter.atTop (nhds 1)`

**then**

1. `1.2325876568 < q 0`
2. `q 0 < 1.2325876569`

## Author's paraphrase (hand-written; checked only by prose rules)

Hiemenz stagnation-point flow: every solution of f''' + f f'' + 1 − f'² = 0 on [0, ∞) (f has derivative p, p has
derivative q, q has derivative −f q − 1 + p², one-sided at 0) with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞ has wall shear q(0) = f''(0) strictly between
1.2325876568 and 1.2325876569.

## Formal statement (Lean 4)

```lean
theorem hiemenz_limit_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    1.2325876568 < q 0 ∧ q 0 < 1.2325876569 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `hiemenz_limit_window`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/FalknerSkan/Limit.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 30
