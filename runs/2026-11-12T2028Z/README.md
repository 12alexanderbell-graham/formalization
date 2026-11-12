# Run 2026-11-12T2028Z (scheduled)

**THE RESULT:** part 3 (measured trust), by rotation. This was the first blind red team on the verified-findings layer (round AI, Sonnet). On main, all 6 seeded wrong findings passed every check. For example, a correct published value could be declared wrong, and two findings' certificates could be swapped, with CI green. The repair is `scripts/trust/check_findings.py` (FB1–FB6, blocking). It rejects all six and three further variants. That AFTER figure is not blind.

**What a scientist can now trust without checking:** when a verified finding says a published value is too large, CI has checked that value's whole rounding interval against a certified Lean window. For F13 this covers all five printed tables. Before, it rested on a prose sentence. The printed β and values a finding quotes are numerals of the Lean statement. Each finding shows its own certificate. Its Correct line names the solution class the record assumes.

**Weakest unchecked step:** the Scope and Plain-words prose of a finding is still free. FB6 reads only the Correct line and only registered class atoms. FB5 reads only parentheticals after a cited headline. In F1–F11, 24 printed values and size words are baselined, not bound.

## Start
- 20:28Z. add_repo was not exposed. The pre-cloned checkout was detached, with a stale local main whose commits are on origin `wip/*` branches. `git checkout -B main origin/main` gave 02fb347. There was no LOCK; it was taken in d0b20ae.
- Local Lean was available. The elan installer and Mathlib cache took about 5 min. The CI artifact `checked-build` of 43268238201 (6a660ac) was restored after `pip install zstandard`. Run 1828Z's twelve FSRev modules and `NegReversedRows` were built incrementally (about 16 min).
- CI: 43294811277 (02fb347, run 1828Z's final push) was in progress the whole run. Next run reads it.

## Bottleneck
- Part rotation: part 3 had made no progress since run 0828Z (five runs). The rule of run 0428Z gives it this run.
- The newest output is new science and verified findings: F12–F14 and the Falkner–Skan rows. No blind round had attacked whether the system can be made to certify a false finding.
- A yes (defects caught) would let the findings be quoted as measured. A no names the holes to repair.

## Round AI — `t5/RESULTS.md`
- The brief was committed first (7ad53ed). The red team was Sonnet, blind, on a read-only snapshot, and took 6 min. Its output was committed verbatim before judging (4620626).
- All six defects edit the verified-findings prose of FINDINGS.md. BEFORE, judged with every CI Python check (`judge_ai.sh`): **6/6 ACCEPTED**.
- The repair is `check_findings.py`:
  - FB1: a generated block stands only in its own finding's section.
  - FB2: printed values are bound to Lean (`[src=H]`, `[src>H]`, `[src<H]`, against the rounding interval).
  - FB3: no bare `[src]` on lines that state a finding.
  - FB4: spelled-out sizes are baselined.
  - FB5: uniqueness and generality words after a cited headline.
  - FB6: class phrases in the Correct line, from a grow-only registry.
- Side repair: `check_numbers.py` labels relative differences as differences.
- The F12–F14 printed values are now bound in FINDINGS. No number changed.
- AFTER: full judge on a7b0125 (FB1–FB5), then direct runs of the final FB3/FB6: 0/6, plus three variants.

## Verification
- Local CI replica vs 6a660ac, the newest green ancestor:
  - The trust step (StatementDeps, Claims, every Python check) was green except check_status_lines S1. A STATE bullet began with the status word "Verified"; it was renamed, and S1, check_necessity and check_necessity_prose were rerun green.
  - Frozen step: 21 commands, 0 failed.
  - goal_guard, make_packet --check, precheck_citations and route_control: green.
  - No generated file changed (TRUST_MAP, CLAIMS, PHRASE_LINES, frozen.txt).

## LOCK
- Taken 20:29Z (d0b20ae); heartbeat 4bd2cf8. Removed in the final commit.

## Next run's starting point
- Read CI: 43294811277 (02fb347: `NegReversedRows` promotion, NecessityS), then this run's final push (check_findings in CI).
- Then parts 2/5 (promote `Work/FalknerSkan/ReversedRows.lean` row −0.15 with a blind β reading of Ganapol Table 7; or the whole Table 7) or part 1, by rotation (STATE "Exact next step" 0).
