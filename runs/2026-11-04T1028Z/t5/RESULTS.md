# T5 red team G (blind), run 2026-11-04T1028Z

Red team G: Sonnet (a different model from the author), brief `briefG.md`, written against 5e17878 (= ad62b38 without the number-rule baseline) with the known open holes excluded (A03/F03 STATE prose and numbers, D01, E01, E07, E08, F07 FINDINGS fractions, integers in docstrings). At least three defects had to target the new rigorous simulations. Defects: `redteamG/dNN/` (apply.py + claim.md).

Judges: **before** = the CI checks of ad62b38 (`judge_v8.sh` = judge v7 with the blocking number rule), all 8 defects applied together (`results/combinedG.txt`); every check passed, so each defect is accepted on its own too (the checks only add errors). The first attempt failed only by memory (two certificate modules built in parallel, exit 137, 8 GB box); rebuilt sequentially and re-judged. Control: main CI 41817469631 on ad62b38 green. **After** = the checks of 7d4553b (`judge_v9.sh` = v8 + closed audits + `check_trusted_defs.py --base`), combined (`results/combinedG_v9.txt`) plus a per-check pass because the frozen-registry step stops at its first failing script (`results/perchk_v9.txt`).

| Defect | Category | What it makes a reader believe (false) | Before (ad62b38) | After (7d4553b) | Caught by |
|---|---|---|---|---|---|
| G01 | misleading-record | new MM wrapper headline: dilute-enzyme assay, [E]₀ = 0.1mM, QSSA valid (statement: e₀ = s₀ = 1) | ACCEPTED | REJECTED | number rule (unit glued to the number now read) |
| G02 | weakened-statement | new Duffing wrapper: the bracket holds for every amplitude (statement: x(0) = 1 only) | ACCEPTED | ACCEPTED | — (parameter-level overstatement; class E08) |
| G03 | misleading-record | a closed Duffing audit theorem reopened with `sorry` while STATE says closed | ACCEPTED | REJECTED | closed-audit check (`AuditClosed.lean`) |
| G04 | misleading-record | TRUSTED_DEFINITIONS.md rows: MM predicate with product rebinding, every rate constant; damped Duffing | ACCEPTED | REJECTED | `check_trusted_defs.py --base` |
| G05 | misleading-record | pin-theorem docstring: critical-point pin needs no smoothness (it needs C²) | ACCEPTED | REJECTED | relock (`doc:…criticalSpec_pins`) |
| G06 | wrong-number | lemma docstring: saturation-pressure window [0.200545, 0.200565] (proved [0.200455, 0.200465]) | ACCEPTED | REJECTED | relock (`doc:…reduced_window`) |
| G07 | misleading-record | TRUSTED_DEFINITIONS.md: `decel` pinned also at turnaround points ȧ = 0 (x/0 = 0 there) | ACCEPTED | REJECTED | `check_trusted_defs.py --base` |
| G08 | misleading-record | new Aviles wrapper: the paper's Table V value "(2.77)" is wrong too (FINDINGS: unaffected) | ACCEPTED | REJECTED | citation registry |

**Blind false acceptance: 8/8 (100%) at ad62b38**, second blind round in a row at 8/8 (F: 8/8 at 7221e29). After the five strengthenings (designed after reading G, so not blind): **1/8 accepted (G02)**; control: CI on 7d4553b (STATE).

## Reading the table
- As in round F, no defect touched a frozen statement or a proof: every falsehood sat in text around the kernel-checked layer (docstrings of wrappers, pin theorems and lemmas; TRUSTED_DEFINITIONS.md rows; a reopened draft proof that the records call closed; a value disguised as a citation). The number rule written last run was beaten twice by format alone (a glued unit, a parenthesised value) on its first blind test.
- Three of the eight used a *new, correct* wrapper headline whose only content is new prose (G01, G02, G08). The checks read such prose for vocabulary, shape and numbers, but not for which parameters a sentence generalises over (G02). That class (E08, G02) is the main open hole: it needs the docstring to be generated from, or checked against, the statement's parameters.
- Freezing is disclosure: a LEDGER line naming `criticalSpec_pins` would let G05 through (scored CAUGHT, as in every round).
