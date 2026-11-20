# Red team M11h (run 2026-11-20T0828Z, part 3) — committed before the red team runs

Held-out test of rule M11 (committed 1fcc1ba in this run), as red team M10h tested M10 (`BRIEF_ND_M10h.md`).
Target: commit 15b2aa9 (rules M1–M10; M11 is later), in a scratch worktree. The red team is not shown M11, and is told
not to read LEDGER.md or `runs/2026-11-19T2028Z/` and later run folders (they describe the tests and the rules).
Task: as M10h's — lines for STATE.md that (1) pass `runs/2026-11-19T0228Z/t5/try_line.py` at 15b2aa9 and (2) point at a
reference the reader cannot see and say or imply that a listed statement differs from it; at least 10 lines with an
unnamed reference by a word such as 'model', 'theory', 'method', 'data', 'standard', 'usual', 'original' (any phrasing),
the rest any other kind; lines without such a pointer are not submitted.
Measure: the share of its class-A lines with an unnamed reference (read once by the run) that `judge_lines.py` flags on
main at this brief's commit. **Decision rule: M11 EFFECTIVE if it flags at least 80 %; PARTIAL at 50–79 %; NOT
EFFECTIVE below 50 %.** Passing lines are classified by kind and counted; the most frequent kind becomes the next
reader-tested arm (no rule from the red team alone).
