# Run 2026-11-13T0028Z (scheduled)

**THE RESULT:** parts 2/5 and 3. (1) Twelve more rows of Ganapol's reverse-flow Falkner–Skan table are promoted to Checked: β = −0.04 … −0.09 and −0.11 … −0.16 (`Checked/FalknerSkan/NegReversedWallShearRows.lean`), each a solution with a ten-decimal wall-shear window, existence, |f'| ≤ 1 and the fast-approach class, with β read blind from the typeset Table 7. With the four rows already in Checked (−0.10 earlier, −0.17 … −0.19), 16 of the table's 19 rows are now Checked statements; PROVED once CI is green on every job. (2) Part 3: a blind red team (AJ) on the verified findings got **6/6 wrong findings accepted on main** despite last run's FB1–FB6; the repair FB7 freezes every finding's prose against the CI base (changes need a LEDGER line naming the finding): AFTER 0/6, not blind.

**What can a scientist now trust without checking it themselves, that they could not before?** (a) The reverse-flow wall shear f''(0) of the Falkner–Skan boundary layer at β = −0.04 … −0.16 to ten decimals (e.g. −0.0966367874 at β = −0.04, −0.1334212378 at β = −0.15), as Checked statements whose β was read blind from the published table, not typed by the author. (b) That the words of a verified finding in FINDINGS.md have not been changed silently since the last green CI run: every change is named in LEDGER.

**Weakest unchecked step:** the restatement audit of the twelve rows is run 1228Z's blind restatement instantiated per row by script (no new blind restater); uniqueness of the reverse-flow solution in its class is numerical only. On the findings layer, the words of a new or disclosed finding are still the author's (FB7 checks disclosure, not content). The promotion is not yet judged by CI (local replica only).

## Start
- 00:28Z. add_repo was not exposed. The pre-cloned checkout was detached and shallow with a stale local `main`; `git fetch --unshallow` and `git checkout -B main origin/main` gave 07b7a68. No LOCK; taken in d118f4c.
- Local Lean: elan + Mathlib cache ≈ 4 min. CI artifact `checked-build` of 43311405425 (50d4d16) restored in 21 s (after `pip install zstandard`). The 38 certificate modules of the rows (`Checked/FSRev/R<Row>{Over,Slow,Tube}.lean`, `RAssembleA`, `RTubeA`, added by run 2228Z after 50d4d16) built locally in ≈ 60 min on 2 cores, shared with the red-team judge.

## CI read
- **43311405425 (50d4d16, run 2028Z's final push: check_findings.py): success on every job.**
- 43333104273 (07b7a68, run 2228Z's final push: 35 FSRev modules) was still running at 01:35Z (nanoda shards and checked job building; the work job too). The next run reads it.

## Bottleneck (and what a yes/no changes)
- Part rotation: 2/5 at 2228Z, 3 at 2028Z, 2/5 + 1 at 1828Z. STATE's next step named the promotion of the eleven rows plus row −0.15 (item 0(a)) and, for part 3, a fresh blind round on the findings layer against FB1–FB6 (item 0(d)).
- Promotion: a yes makes Ganapol Table 7 a Checked table (16/19 rows), PROVED with the next green CI. Part 3: a yes (round AJ caught) would let findings be quoted as measured; a no names the holes.

## Work
1. **Blind β reading of Table 7** (`fsrev_reader/`): brief 8bceab0 (rows by position, no values, no three-digit integers), Sonnet reader 5b32796 (≈ 1 min; derived f''' + f f'' + β(1 − f'²) = 0 with β = 2m/(m + 1), checked with sympy, read twelve β from the typeset crop), copy dfe3ff3 (`Checked/Trust/SecondReadingFSRevTable.lean`, constants disclosed in LEDGER). All twelve agree with the frozen statements.
2. **Promotion** by `scripts/promote_rev_table.py` (template: run 1828Z's `promote_rev_rows.py`): statements verbatim from the freezes cf66704 (eleven rows) and 33cd0de (−0.15), names changed only; headlines, literal readings; relock, TRUST_MAP, CLAIMS, packet. Compiled first time. The first module name `NegReversedTable` needed the vocabulary word `table`, which turned seven older "Table 2/5" paraphrases into V10 errors: renamed to `NegReversedWallShearRows` (existing words) before any push; LEDGER correction line.
3. **Blind red team AJ** (`t5/`, RESULTS.md): brief 3f66ca9 first, Sonnet on a read-only snapshot, Lean-free (FINDINGS/registries only), 5 min. BEFORE 6/6 ACCEPTED: F12 class widened in Scope, F13 printed values swapped between sources, F1 a coefficient of the correct formula changed, F4 Lean coverage of every curvature claimed, F14 uniqueness claimed, F10 printed values swapped between parameters. Repair: `check_findings.py` FB7 (prose of verified findings frozen against BASE; changed/new/removed needs a LEDGER line naming `FINDINGS.md` and `F<k>`), 6 new controls. AFTER: 0/6, each only by FB7 (not blind).

## Verification
- (filled below)

## LOCK
- Taken 00:30Z (d118f4c); heartbeat 086cd55. Removed in the final commit.

## Next run's starting point
- (see STATE "Exact next step")
