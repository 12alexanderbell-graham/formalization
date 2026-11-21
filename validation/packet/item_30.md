# Item 30

**Area:** Data claims

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** the statement is proved in module `Checked.Data.Moresco16` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source):** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; non-vacuity: the Checked theorem `Checked.Trust.NV.table5_oL_inconsistent` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 3 numbered; 3 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 0 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); statement literals: no blind second reading registered; 14 literals of the statement are grandfathered as never read twice (`scripts/trust/literal_baseline.txt`); the statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `N : ℝ`, `c : ℝ`:

**assuming**

1. `4 < N`
2. `N ≤ 31`
3. `|c + 2 * 3 + 2 * 3 * (3 + 1) / (N - 3 - 1) - 21.41| ≤ 5e-3`

**then**

- `5e-3 < |c + 3 * Real.log N - 25.71|`

## Author's paraphrase (hand-written; checked only by prose rules)

Table 5, row oLCDM (k = 3): for every N with 4 < N ≤ 31 and every value c of −2 ln L_max,
if c + 6 + 24/(N − 4) is within 0.005 of the printed AICc 21.41, then c + 3 ln N differs from
the printed BIC 25.71 by more than 0.005.

## Formal statement (Lean 4)

```lean
theorem table5_oL_inconsistent (N c : ℝ) (hN : 4 < N) (hN31 : N ≤ 31)
    (hA : |c + 2 * 3 + 2 * 3 * (3 + 1) / (N - 3 - 1) - 21.41| ≤ 0.005) :
    0.005 < |c + 3 * Real.log N - 25.71| := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `table5_oL_inconsistent`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Data/Moresco16.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 30
