# T5 results, judge v6 (run 2026-10-31T1028Z)

Judge: `judge_v6.sh` = judge v5 (the CI checks on main: Checked + Work build, forbidden tokens, trust step after author relock, certified numbers, frozen and number diffs against the base) + `check_prose.py` (and `--base`) + the author regenerating the validation packet. Base 62584ab = first version of the prose check; 38e8efb = after hardening with red team E's defects in view (shape through one unfolding step, per-conjunct record rule, frozen docstrings). In v6 the "relock" step also runs `check_prose --base`, so "prose" is listed alone when both fired. `Dd04p` = port of D04 without its (stale) TRUST_MAP edits.

| Defect | Base | Category | Verdict | Caught by |
|---|---|---|---|---|
| Ad03 | 62584ab | misleading-record | ACCEPTED |  |
| Ad04 | 62584ab | wrong-definition | REJECTED | prose |
| Ad05 | 62584ab | weakened-statement | REJECTED | prose |
| Bd04 | 62584ab | wrong-definition | REJECTED | prose |
| Dd01 | 62584ab | misleading-record | NOT JUDGED (apply failed on the current tree) |  |
| Dd04 | 62584ab | mistranscription | NOT JUDGED (apply failed on the current tree) |  |
| Dd04p | 38e8efb | mistranscription | REJECTED | numbers, prose |
| Ed01 | 38e8efb | wrong-definition | ACCEPTED |  |
| Ed03 | 38e8efb | weakened-statement | REJECTED | prose |
| Ed05 | 38e8efb | wrong-number | REJECTED | prose |
| Ed06 | 38e8efb | misleading-record | REJECTED | relock |
| Ed07 | 38e8efb | wrong-definition | ACCEPTED |  |
| Ed08 | 38e8efb | wrong-statement | ACCEPTED |  |
| control | 62584ab |  | ACCEPTED |  |

## Reading the table
- **The class the run targeted is closed:** A04, B04 (wrong definition named and described as a pinned quantity), A05 (existential headline read as universal), D04 (record of a free formula) were ACCEPTED by every earlier check version; all four are now REJECTED. Control passes (no false rejection).
- **Red team E** (Sonnet, written against 62584ab, aimed at the new check; its own replica predicted 8/8 accepted): judged at 38e8efb, 3 caught (E03 `Set.Nonempty` existential, E05 free conjunct beside a pinned one, E06 generalised docstring of an existing record: frozen docstrings), 3 accepted (E01 "angular-size distance" synonym + name outside the name rule; E07 `local notation` formula called "flux distance"; E08 an RK corollary labelled Peng–Robinson: parameters, not names, carry the meaning), 2 not judged (E02 docstring of the pinned `decel`, E04 polarity flip of a refutation's docstring: both edit base modules, ~30 min rebuild each; both change frozen docstrings, so the frozen registry should reject them as it rejected E06 — to be confirmed next run).
- **Caveat (teaching to the test):** the 38e8efb hardening was designed after reading E's defects; E03/E05/E06 measure that the fixes work, not the false-acceptance rate of a blind attack. The blind number is: 62584ab vs E = 8/8 accepted by E's replica (unjudged); a fresh red team (F) against the current main is the next blind measurement.
- After the judging, synonyms for E01/E07 were added to the glossary (grow-only; `angular-size distance`, `flux distance`, …); they are not judged here.
- Not addressed this run, still open: A03 (STATE scope prose; ACCEPTED again), D01 (labels next to certified numbers; its apply no longer matches FINDINGS: needs a port).
