# Run 2026-11-04T0428Z (scheduled)

Environment: add_repo not exposed; repo pre-cloned (detached at 7e849af; a stale local `main` was reset to origin/main, its commits are on `origin/control/frozen-*`). LOCK of run 0228Z was 123 min old and its holder was still reading CI, so this run took the auditor role (48.4) and only wrote inside its own `runs/` folder until run 0228Z removed the lock (84c050b, ~04:31Z). **Local Lean worked** (elan installer accepted; full uncached program build ≈ 35 min on 2 cores). CI: 41774575151 (LOCK commit) green; later ids in STATE.

**THE RESULT:** part 3 (measured trust) moves, as the part-rotation rule required (last moved 1028Z of 2026-10-31). The program got its first *blind* false-acceptance measurement of the current pipeline, and three new blocking checks closed five of the eight holes it found.

**WHAT CAN A SCIENTIST NOW TRUST WITHOUT CHECKING IT THEMSELVES?** That a definition's docstring, a spec field's docstring or a Checked module's documentation (what the validation packet and the trust map show them) cannot be changed without a LEDGER disclosure; that a "²" (second reading agrees) mark in TRUST_MAP.md stands for an agreement with an independent second transcription, not with itself; that decimals in FINDINGS.md code spans and pin claims in TRUSTED_DEFINITIONS.md are machine-checked. And, newly measured: what the pipeline does *not* yet guarantee (below).

**WEAKEST UNCHECKED STEP NOW:** STATE.md prose and numbers (F03, F04's STATE half; class A03) and fractions in FINDINGS.md (F07): hand-written, read by no script. A reader who takes a number from STATE.md instead of a headline docstring or a certified FINDINGS number is trusting prose.

**BOTTLENECK AND WHY:** STATE's next step for part 3 was to re-judge the open holes and measure blind. Every earlier T5 round after the first was either designed against known holes (teaching to the test, noted in 1028Z) or judged only after a fix. Yes (low blind acceptance) = the system's trust number exists and is good; no = the number exists and names the next checks. It was no: **8/8 accepted** by the checks on main at 7221e29.

**WHAT WE DID:**
1. Red team F (Sonnet, different model, brief `t5/briefF.md`, written against 7221e29, known holes excluded): 8 defects (`t5/redteamF/`), all valid (one borderline: F02 misdescribes the Maxwell spec's content; the property it claims may hold for vdW as a consequence).
2. Judged at 7221e29 with the CI-equivalent judge (v6; `t5/judge_v6_local.sh`; md-only defects with the fast judge `t5/judge_md.sh`, whose Lean outputs come from the control run at the same base; the four Lean-touching defects applied together, `t5/combinedLean/`, errors attributed per constant): **8/8 ACCEPTED, control ACCEPTED**.
3. Root cause: every defect put the falsehood in reader-facing text that no script reads, or in a check that tested form but not independence. Fixes (LEDGER 2026-11-04 · run 0428Z): (a) second readings must have an independent `Checked.Trust.SecondReading*` right-hand side (F06); (b) docstrings of every classified definition, of the fields of classified structures and of every Checked module are frozen as new `doc:`/`moduledoc:` entries (180 new entries; none of the 283 old ones changed) (F01, F02, F04 module doc); (c) decimals inside code spans other than names/paths are checked (F05); (d) new `scripts/trust/check_trusted_defs.py`: pin claims in TRUSTED_DEFINITIONS.md must match `pins.txt` (F08). All four tested on the clean tree (no false positives: 0 new prose problems, packet up to date, goal guard ok).
4. Re-judged at 924a9d6 with judge v7 (= v6 + check_trusted_defs): F01, F02, F04 rejected at relock (changed `doc:`/`moduledoc:` entries without a LEDGER line), F05 at numbers, F06 at the trust step, F08 by `check_trusted_defs.py`; F03, F07 accepted; control accepted.

**RESULT:** blind false acceptance **8/8** at 7221e29 (control accepted); after the four checks (924a9d6, judge v7): **2/8** accepted (F03 STATE numbers, F07 a fraction in FINDINGS), 6/8 rejected, control accepted. Table: `t5/RESULTS.md`.

**WHAT COULD STILL BE WRONG:** freezing is disclosure, not prevention: a LEDGER line naming the definition lets a changed docstring through (the judge scores that as caught, as in every round). New definitions with false docstrings are still possible when no glossary term is involved (F01's wording avoided the glossary). The "after" numbers measure fixes designed after reading F's defects; the next blind number needs red team G.

**NEXT:** STATE "Exact next step".
