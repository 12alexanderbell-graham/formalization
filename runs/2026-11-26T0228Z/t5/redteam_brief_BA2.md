# Red team BA, round 2 (run 2026-11-26T0228Z) — committed alone, before round 2 runs

Round 1 (same red teamer, `redteamBA/`, report in `RESULTS_BENCH.md`) got two forged closures accepted, both through
the helper clause `t.isPrefixOf c` (a closure theorem named `Checked`). The rule now counts a helper as the
closure's own only when its name is `<t>.<one component>` and it is declared in the closure's module
(`ownHelper` in `closureFaults`); a new forged control (`ClosureControls` as a theorem name) fails under the old
clause. Both round-1 forgeries are now rejected.

Round 2 task: the brief of round 1 (`redteam_brief_BA.md`) unchanged, against the current `closureFaults`, files
under `runs/2026-11-26T0228Z/t5/redteamBA2/`. At most 15 attempts or 25 minutes.

Decision rule (pre-registered): an accepted forgery that reaches a theorem of the program's library (not a re-proof
from Mathlib alone) is fixed in this run and becomes a control; an accepted forgery that re-proves a side from
Mathlib alone with a bound variable threaded through (residue of test AZ, hole B of round 1) is recorded as residue
with its cost in lines, not fixed in this run.
