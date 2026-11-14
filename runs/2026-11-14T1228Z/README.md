# Run 2026-11-14T1228Z (scheduled)

**THE RESULT:** part 3 by rotation (parts 2/5 moved at 1028Z, part 1 at 0828Z, part 3 last at 0628Z) — the measured false-acceptance rate of the verified-findings layer after its frame was fixed (FB14/FB15), and the repairs. Blind red team AO got **4 of 4 valid wrong findings accepted by every Python check of CI** (6 defects, 2 out of scope by the brief), none through the frame: three author-written registry phrases printed into generated Correct lines and one parser differential (U+2028). Repairs FB16–FB18 close all six (AFTER, not blind) and remove the last author input of the trusted lines: a new class phrase must now be copied from a blind reading (brief → reading → copy, planted controls in CI).

**What can a scientist now trust without checking it themselves, that they could not before?** That every word of a verified finding's generated heading, Printed and Correct lines comes from Lean (via CLAIMS.md and the record blocks) or from a blind reader's committed text — no longer from a registry phrase the author typed, from a Markdown link, from text a line separator hid from the checks, or from a reading guide the author can reword.

**Weakest unchecked step:** that the blind readers (of printed values and, from now on, of class phrases) were blind and right — structure is checked (order, isolation, no leak in the brief), blindness is not; and the repairs themselves are unmeasured blind until the next round.

## Start
- 12:28Z. add_repo not exposed; pre-cloned checkout detached with a stale (and shallow) local main; `git checkout -B main origin/main` = 20252cb (unshallowed at 13:39Z with `git fetch --unshallow`: the red team's snapshot was cloned from the shallow checkout, see below). No LOCK → taken (38fe62e).
- Local Lean: elan + Mathlib cache ≈ 2 min; `checked-build` of 43563791919 (96643b0) restored (first attempt failed: no zstd decompressor in the fresh container — `scripts/restore_checked_build.sh` now installs one up front); `lake build Checked` to HEAD ≈ 6 min; StatementDeps (no relock) 11 min, Claims 4 min: tree unchanged (generated files current).
- CI at start: 43581569718 (c3ca8a4) checked job in progress since 10:06Z; 43590961602 (071b543) work green, checked pending.

## Bottleneck (and what a yes/no changes)
- STATE 0o (a): a blind round against FB14/FB15. Yes (accepted): the next attack class on the findings layer and its repair; no (all caught): the first blind 0/n on this layer — the measure the trust track exists for.

## What we did
1. Brief `t5/briefAO.md` (copy of AN's: rules now FB10–FB15; asks for weaknesses of a new kind — what the generators read, name resolution, the reading guide, rendering, history rules) committed in 5536d4b before the snapshot `/home/claude/fzAO` (clone of 5536d4b + this run's fresh `.lake` files; the clean tree fails only goal_guard).
2. Red team AO (Sonnet, 40 min, blind; output committed verbatim d8d4b1b before judging). Judge `t5/judge_ao.sh` (copy of AN's) on full-history trees; results `t5/RESULTS.md`.
3. Repairs 1084a9f (+ this commit): FB16, FB17 (a)/(b), FB18, FB15 word list, packet Source label; `route_control.py` FB17 planted controls (all six behave).

## Results
- BEFORE (blind, 5536d4b): d01, d02, d03, d06 (valid) and d04, d05 (out of scope by the brief) ACCEPTED by every Python check of CI (d06 also by StatementDeps' citation rule, run on its tree: exit 0). AFTER (1084a9f, not blind): d01 FB15+FB17 (b), d02 FB17 (a)+(b), d03 FB17 (b), d04 FB18, d06 FB16; d05 still passes but the packet labels the line as hand-written and unchecked. Table: `t5/RESULTS.md`.
- CI read: 43581569718 (c3ca8a4) green on every job (completed 13:46Z) → the F4–F7 records (cb49239) and NecessityAD (4a73412) judged in CI. 43590961602 (071b543, `bonnor_ebert_second_max`) in its checked job from 13:26Z at the end: PROVED not yet claimed.

## Not done / next
- STATE 0r: CI read of 071b543; then part 1 or parts 2/5 by rotation; part 3 later: a blind round against FB16–FB18 (the LEDGER experiment's refutation test).

## Local checks and push
- `check_findings.py --selftest` 73 controls green; `route_control.py` 11 controls behave; `make_packet.py --check` current; `records_check.py c3ca8a4` (newest green ancestor): 41 commands, 0 failed. No `.lean` file changed this run (StatementDeps/Claims at the start: tree unchanged).
