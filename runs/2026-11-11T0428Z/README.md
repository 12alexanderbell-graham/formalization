# Run 2026-11-11T0428Z (scheduled)

**THE RESULT:** part 3 (measured trust; rotation: no part-3 progress for four runs) — first blind red team on hypothesis necessity (T2b): **5/6 misleading necessity lines accepted by every check as submitted (6/6 with a trivial repair); fixed by generated `shape:` entries and the blocking rule N4, 0/6 after (not blind)**; the honest count of fully classified headlines is 14/151, not 22.

**What can a scientist now trust without checking it themselves, that they could not before?** That a headline TRUST_MAP.md reports as having every hypothesis classified has no assumption hidden where the numbering does not look (after a `let`, inside a conclusion-level definition, in a subtype binder) and no hypothesis classified only as part of a bundle or because the conclusion repeats it; and that two hypotheses labelled redundant are redundant each alone, not together.

**Weakest unchecked step behind the results:** the 26 `bundled` headlines (model predicates behind pinned definitions) still have their predicate's parts unclassified one by one; restatements are detected only syntactically.

**Measure:** blind false acceptance on the necessity layer 5/6 (6/6 repaired) → 0/6 after the fix (not blind); fully classified headlines 22 → 14 (correction, of 151); NEEDED/REDUNDANT unchanged 255/51.

## Start
- 04:27Z. LOCK held by run 0232Z (started 02:32Z, heartbeat 03:30Z, promotion with a full build): auditor role, writes only in this folder (48.4). Repo pre-cloned (detached HEAD); `git fetch --unshallow`; main = origin/main 7d4c53f.
- Local Lean: elan installer accepted; Mathlib cache ≈ 1 min; full `lake build Checked` 04:31–05:31Z (detached; MMCerts first).
- Run 0232Z released the LOCK at 05:39Z (separation promotion bef143b–b51befb); LOCK taken 0b5193d at 05:58Z.

## Part 3: blind red team AF (`t5/`)
- Brief `t5/briefAF.md` (9be5ce1, committed before the red team started); Sonnet red team on a read-only worktree snapshot of 7d4c53f, ≈ 15 min; output `t5/redteamAF/` committed unchanged (e0ecabc) before judging.
- Judge `t5/judge_AF.sh`: all six defects in one tree, each defect's modules compiled alone first; BEFORE (scripts of 7d4c53f) and AFTER (fix committed locally as the base) columns; table and root cause in `t5/RESULTS.md`.
- Fix (written after reading the report): `scripts/trust/StatementDeps.lean` `necConjuncts`/`necShape`; `scripts/trust/check_necessity.py` N4 + label + controls; `scripts/trust/necessity_shape_baseline.txt` (26 lines, all `bundled`); TRUST_MAP.md regenerated on the post-promotion main (frozen registry and CLAIMS.md unchanged).

## Lessons
- A generated "every hypothesis classified" count was computed on a different object (binders as written) than the one a reader means (every assumption): the first blind round on the layer got through with every defect. Generated completeness claims need their escape shapes listed by the generator.
- Auditor role while another run builds: the red team, its judging and the fix all fit in the other run's build wait; landing the fix needed only an incremental build after the release.

## Next
- STATE exact next step 0/0b: read CI of this push (N4 live); part 1 item 3e (per-conjunct necessity for the bundled predicates) or parts 2/5.
