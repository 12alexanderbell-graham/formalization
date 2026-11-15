# Run 2026-11-15T1628Z (scheduled)

**THE RESULT:** part 3 by rotation (measured trust) — a pre-registered review with blind readers showed that a label does not stop a reader: one unchecked line saying a verified finding was withdrawn made 3/3 readers drop it under the candidates banner and 3/3 inside the finding's own labelled notes (0/2 on the clean page). The verified findings now have a generated reader page with no author words on it (`VERIFIED_FINDINGS.md`, FB26), measured by readers (2/2 correct) and by a blind red team (AU) whose only route onto it — registry phrases through a forged reading — is closed.

**What can a scientist now trust without checking it themselves, that they could not before?** That the page the program points them to for its verified findings (`VERIFIED_FINDINGS.md`) contains no sentence an author chose: every line is generated from the Lean records (statements, certified numbers, blind readings bound by agreement lemmas, class restrictions shown as the Lean hypotheses themselves), so no unchecked note can withdraw, extend or relabel a finding there. Measure: blind readers misled by an unchecked withdrawal line 6/6 on FINDINGS.md, 0 possible on the generated page (the defect files generate a byte-identical page); readers of the generated page alone 2/2 correct on every item; red team AU: 7 defects, all through the forged registry route, 3/3 readers repeated d01's false phrase before the fix; after it no defect's words reach the page.

**Weakest unchecked step:** the blind readings bound to printed values are model readers whose source descriptions an author could forge only through the reader-file route (ancestry-locked, not independent of the program); F8 and F11 have records of sizes only, so the generated page cannot say what they refute. For the physics: CI 43721065108 (b7d5a44) read green on every job incl. nanoda 4/4 at the end of this run → `Checked.Math.GelfandExtrema.gelfand_extrema` PROVED.

## Start
- 16:28Z. add_repo not exposed; pre-cloned checkout had a stale local `main` (Nov 9, diverged); `git checkout -B main origin/main` at 878502b, unshallowed. No LOCK → taken (1c409a8).
- Local Lean: elan (authorized), `lake exe cache get`, `checked-build` of 43709741164 (0a52be0) restored; `lake build Checked` to main ≈ 4 min; StatementDeps ≈ 10 min, Claims ≈ 3 min — generated files unchanged (293 headlines, NV 176/176, needed 666, redundant 185, open 148).
- CI at start: 43721065108 (b7d5a44) in progress; 43731774283 (878502b) pending. Neither concluded during the run.

## Bottleneck (and what a yes/no changes)
- Rotation: part 3. Run 1028Z's experiment: after FB24/FB25 only forged-route or labelled defects remain, unless a reader-facing review judges the banner insufficient. The label rule itself had never been measured with readers. Yes (readers ignore labelled prose) → the label-based validity of the findings rounds stands; no → every labelled region is a live channel, and the page a reader is pointed to must carry no author prose.

## What we did
1. Pre-registered reader review (`t5/reader_brief.md`, key committed first): 10 blind Sonnet readers, one page each (`t5/READERS.md`). Banner 3/3 misled, notes label 3/3 misled, overstatement contradicted by generated lines 0/3, generated page 2/2 correct. Brief AT (written first, for a red team under the old label rule) was not run.
2. FB26 (`scripts/trust/make_verified_page.py`, blocking in the goal-guard job and the trust step): `VERIFIED_FINDINGS.md` = generated part of each verified finding + certified numbers, fails closed; FINDINGS.md's fixed reading guide and README point to it.
3. Blind red team AU (Sonnet, brief 25a8b95, validity by readers of the generated page; output `t5/redteamAU/`, committed before judging): records, presence and reader descriptions locked; the registry phrase route (forged reading) put false class words into generated Correct lines. BEFORE: every judged defect ACCEPTED by every check; 3/3 readers of d01's page repeated its false phrase. Fix: the page re-generates each Correct line with `hypothesis` + Lean text in place of phrases (10 controls). AFTER: no defect's words on the page (`t5/RESULTS_AU.md`).
4. Root cause of the red team's two disk-full stops: `route_control.py` leaked a ~110 MB scratch repo per call (20 GB); now removed at exit.
5. Local: records_check.py 0a52be0 (42 commands, 0 failed) before the AU fix; again at the end (see CHANGELOG).

## Next
- STATE 1f: CI read (878502b, 82ebb61); then parts 2/5 by rotation.
