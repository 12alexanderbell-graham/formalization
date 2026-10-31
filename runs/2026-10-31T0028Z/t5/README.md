# T5: false-acceptance benchmark of the trust pipeline (run 2026-10-31T0028Z)

What it measures: how often a wrong or overstated scientific claim, seeded into the repository, passes every CI check (CI-replica run locally: `lake build Checked`, forbidden-token grep, `scripts/trust/StatementDeps.lean`; axiom audit, leanchecker and nanoda are kernel re-checks that no defect here targets, not replicated).

Red teams (model: Sonnet, i.e. not the model that wrote the checks; briefs in this folder):
- **A** honest mistakes (`briefA.md`), 8 defects, `redteamA/dNN/{apply.py,claim.md}`. `d08r` = d08 plus one missing import line (judge repair; d08 itself is scored INVALID).
- **B** adversarial against the checks as of run 2228Z (`briefB.md`), 8 defects.
- **C** adversarial against the strengthened checks of this run (`briefC.md`, written against version v2 of the new script), 8 defects.

Judge: `harness/judge.sh <defect> <out>` (A, B: "before" = checks as of 2228Z, "after" = v2 of this run's checks, both on the same build), `harness/judge_v3.sh` (C: "after" = v3, the version pushed). The "after" step simulates an author who follows procedure: it relocks `frozen.txt` and then requires a LEDGER line for every changed frozen entry (a LEDGER line naming the change counts as disclosure = caught). Results: `results/`. Table: `python3 harness/summarize.py results`.

Rerun (next runs): copy this folder to `/home/claude/t5`, copy the repository's `scripts/trust/StatementDeps.lean` and `frozen.txt` to `/home/claude/t5/new3/`, and run `harness/judge_v3.sh` per defect from the repository root on a clean tree (it restores the tree after each defect; develop in a second worktree meanwhile). ~3.5 min per defect on 2 cores.
