# Item 46

**Area:** Chemistry

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** proved in module `Checked.Chemistry.CubicEOS` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source):** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; non-vacuity: the Checked theorem `Checked.Trust.NV.critCubic_existsUnique` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 2 numbered; 2 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 0 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); statement literals: no blind second reading registered; 2 literals of the statement are grandfathered as never read twice (`scripts/trust/literal_baseline.txt`); the statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `u : ℝ`, `w : ℝ`:

**assuming**

1. `-2 < u`
2. `0 < 1 + u + w`
3. `u + w < -1`

**then**

- there is exactly one `x : ℝ` such that (`1 < x`) and (`critCubic u w x = 0`)

Program definitions in this claim:

- `critCubic u w x` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_critCubic`) (for `u : ℝ`, `w : ℝ`, `x : ℝ`): is defined as `x ^ 3 - 3 * x ^ 2 - 3 * (u + w) * x - (u ^ 2 + u * w - w)`

## Author's paraphrase (hand-written; checked only by prose rules)

The critical cubic has exactly one root above 1 (x = v_c/b > 1).

## Formal statement (Lean 4)

```lean
theorem critCubic_existsUnique (u w : ℝ) (hu : -2 < u) (h1 : 0 < 1 + u + w) (h2 : u + w < -1) :
    ∃! x : ℝ, 1 < x ∧ critCubic u w x = 0 := …
```

## Definitions it uses

See GLOSSARY.md: `Chemistry.CubicEOS.critCubic`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `critCubic_existsUnique`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Chemistry/CubicEOS.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 46
