# Run 2026-11-06T1028Z (scheduled)

**THE RESULT:** parts 1/2 (the certified Robertson t = 10¹¹ enclosure and the refutation of the printed Bari reference promoted to `Checked`) and part 3 (blind red team N: 4/6 wrong claims accepted by the newest checks; six new checks reject all six, not blind).

**What can a scientist now trust without checking it themselves, that they could not before?** The Robertson (ROBER) state at t = 10¹¹ — every solution's y₁, y₂, y₃ in certified intervals, and the Bari test set's printed y₃ more than 10⁻¹⁴ too small — now sits in `Checked` with the full evidence chain: kernel proof, pinned solution predicate, non-vacuity witness, generated claim in CLAIMS.md, and the end time and printed value read a second time by a blind reader from the typeset page (PROVED once the promotion's CI, including the nanoda replay, is green). And six more kinds of misleading claim (arithmetic over source numbers posing as a certified target, edits to existing readings, briefs that leak the answer in words, spelling variants of model names, "throughout"/"always" over fixed-time results, grading words such as "reliable") are now rejected by CI.

**Measure:** Checked headlines 171 → 174 (all on pinned definitions; NV 113/113); blind false-acceptance of the round-M checks on round N: 4/6; after the new checks 0/6 (not blind).

**Weakest unchecked step:** the nanoda replay of the large `decide +kernel` Chebyshev certificates (CI of 6f0816d, not yet read); and for the new checks, that they were written knowing the defect classes (a blind red team O must measure them).

## Start
- 10:28Z: no LOCK; pre-cloned checkout detached; `git checkout -B main origin/main` = 8a64b6d. add_repo not exposed. Local Lean: elan installer accepted; Mathlib cache being fetched.

## Work
1. **Bottleneck:** Robertson t = 10¹¹ was PROVED only in Work; promotion makes the refutation of a published reference value a Checked result with every evidence link. A no (a check rejecting it, nanoda failing) would show where the evidence route breaks for long certificate chains. Part rotation: part 5 nominally due (4 runs); recorded deviation — Robertson 0828Z is chemistry's first certified answer not in print, so part 5's chemistry clause moved; mathematics remains the part-5 gap (next run).
2. **Promotion** (`scripts/promote_robL.py`): 14 Work modules copied (namespace, specific imports; ChebBound with the Chebyshev imports); compiled first time (10 min). Docstring prose fixes (rules 3, 5, 7). Full `lake build Checked` green (≈ 57 min); StatementDeps relock 174/174 pinned, NV 113/113; Claims 174; all trust scripts green.
3. **Blind literal reading** of the end time and printed y₃ (Sonnet, typeset Bari ROBER page rendered at 200 dpi): brief 2f42516 → reading b07359e → copy 6fc653c; values agree with run 0828Z's reading. check_blind_route rejected the route on the brief's file template (`import Mathlib.Data.Real.Basic`): template lines exempted (7cfdee5, LEDGER).
4. **Red team N** (Sonnet, blind, ≈ 9 min) on a snapshot of 6fc653c; **check-writer** (Opus, blind to the defect files but briefed after reading N's report) wrote five scripts in a separate worktree; judged in one combined tree (`t5/judge_N.sh`, `t5/judge_N.out`): before 4/6 accepted, after 0/6 with `+eval` slots and `check_prose_eval` added by me (`t5/RESULTS.md`).

## End
- Records: STATE (Robertson section, results, trust track, environment, daily review, exact next step), LEDGER, CHANGELOG, PROMPT working notes; LOCK removed.
- CI: 8a64b6d 42200080559 green on every job; 6fc653c 42203584616 failed in the checked job (expected B3 false positive; repaired before the next push); 6f0816d (promotion), a08a62a, e5766ae and the records commit: read next run.
