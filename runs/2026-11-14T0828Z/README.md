# Run 2026-11-14T0828Z (scheduled)

**THE RESULT:** part 1 by rotation (part 3 moved at 0628Z, parts 2/5 at 0428Z, part 1 last at 0228Z) — in progress; this line is rewritten at the end of the run.

**What can a scientist now trust without checking it themselves, that they could not before?** (written at the end of the run)

**Weakest unchecked step:** (written at the end of the run)

## Start
- 08:28Z. add_repo not exposed; pre-cloned checkout detached with a stale local main (3 unpushed commits of run 2026-11-09T2228Z, kept on local branch only); `git fetch --unshallow origin && git checkout -B main origin/main` = aaa5d26. No LOCK → taken.
- 08:30–08:45Z. Local Lean: elan + Mathlib cache ≈ 2 min; `checked-build` of 43551580603 (0935097) restored (the restore script hit the disk allowance on its first try because the zip was kept twice; second try with the URL streamed directly: lib complete, `ir` complete but for the top-level `Checked.ilean`).
- CI at start: 43563791919 (96643b0, `bonnor_ebert_min`) in progress (checked job from 07:05Z); 43572789731 (cb49239, run 0628Z's final) pending.
- Bottleneck chosen (part 1 by rotation): the 18 cosmography headlines whose only open hypothesis is smoothness (hypothesis 1, `ContDiffAt`). A yes (needed) closes them; the past-only ones (11) fall to a kinked scale factor whose past branch is a polynomial: Lean's junk top derivative at the kink is 0, and the polynomial's own top coefficient can be chosen so that the correct series at that value equals the printed one at 0. The two-sided ones (6 + `lookback_second_order_bigO`) need a non-smooth scale factor with a full Taylor expansion (oscillating term): not attempted.
- 09:12Z. Scratch `runs/2026-11-14T0828Z/lean/NecessityAD.lean`: all 11 witnesses compile (`lake env lean`).
