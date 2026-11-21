# Run 2026-11-21T1428Z

**THE RESULT:** part 3 by rotation (STATE 2x; next step STATE 2y). Measured trust: the first blind red team against the generated claims page the records send a scientist to, judged by every check and by blind readers; the hole it found closed in the generator.

**What can a scientist now trust without checking it themselves, that they could not before?** That every sentence of `CLAIMS_READER.md` is printed from Lean or is fixed generator text: until this run one field of author prose (the summary of an objection entry) was printed there verbatim, and a blind red team used it in five of five defects that passed every check (two of them made blind readers withhold valid results). An objection now shows only that it is open and where its text is, and it can leave the registry only when its statement is frozen again or leaves the list of headlines.

**Weakest unchecked step:** the registries the claims page reads that this round did not reach (`literal_readings.txt` `source=` fields, `def_kinds.txt`, `pins.txt`, `headlines.txt`; the red team tested phrases and literal sources and found them closed, and did not test the others), and an unfounded objection, which still makes readers withhold a valid headline (costs citations, never a false acceptance).

## Start
- 14:28Z. Session clone on the stale divergent main (fa47717); `git checkout -B main origin/main` (ec042fe), then `scripts/start_run.sh`. No LOCK → taken (9b89fb3).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean (elan, v4.35.0, Mathlib cache); judge build of 44908281464 (a684bfc) restored by streaming; `lake build Checked` 3775 jobs; `StatementDeps.lean` 742 s, `Claims.lean` 361 s on 2 cores (309 headlines, NV 187/187; necessity 760 / 243 / 36 open; TRUST_MAP and CLAIMS unchanged).
- CI at start: 44911180559 (9ac0ae3, run 1228Z's final push) in progress, then green on every job (13/13), as was 44908281464 (a684bfc). Nothing to promote.

## Bottleneck
Part 3's measured surface. Ten part-3 runs since 2026-11-18 wrote rules for hand-written lines next to the generated pages (M6–M11, S-N4–S-N7), while `CLAIMS_READER.md`, the page the README and STATE banners point to and the page THE RESULT's false-acceptance number must be measured on, had never been attacked blind. A yes (defects pass) names the page's weakest input; a no is the first measured rate on it.

## What we did
- Brief `t5/briefAV.md` committed alone (0ae34b2 = snapshot): registries, LEDGER lines, `runs/` files and regenerated pages allowed; no `.lean`, no script; validity = a blind reader of the changed entries believes something false. Snapshot `/home/claude/fzAV` with the run's `.lake` outputs (build and packages by symlink).
- Red team AV (Sonnet, ≈ 14 min, one Claims.lean run): five defects, all through `objections.txt`'s free summary, printed verbatim by `Claims.lean` inside the Status line: a 'verdict STANDS, objection closed' summary (d01), a fabricated restatement disagreement (d02), a fabricated referee verdict on the sibling attached to the other headline (d03), counts the same line contradicts (d04), blind readings (d05). Output committed verbatim (`t5/redteamAV/`) before judging.
- Judge `t5/judge_av.sh`: clean snapshot green; each defect accepted by every check (goal guard, packet, every Python command of the trust and frozen steps, BASE 0ae34b2); the five pages equal `Claims.lean`'s output (one run on the tree with all five applied). Readers: `t5/reader_brief_AV.md` committed alone first; two Sonnet readers per defect (`scripts/reader_material.py`); answers `t5/READERS_AV.md`; results `t5/RESULTS_AV.md`.
- Fix (strengthening): `scripts/trust/Claims.lean` prints an entry as "raised in run R, its text written in `path` (author prose, not printed on this page)", fails an empty summary, and says so in both pages' header; `scripts/trust/check_claims.py --base` O1 (four controls) fails a removed objections.txt line whose headline is still listed with the same frozen fingerprint. CLAIMS.md / CLAIMS_READER.md regenerated (header lines only; the registry is empty).

## Measure
- Round AV BEFORE: 5/5 accepted by every check; valid by blind readers 2/5 (d02, d03: 2/2 readers each took the fabricated record as fact and withheld a valid headline); false reassurances misled 0/6 readers (the generated "OPEN FIDELITY OBJECTIONS" frame read as a contradiction; d05's belief was in fact true). AFTER: 0/5 summaries can reach the page; d02/d03 leave a true record that an objection is open.
- First blind measurement on the claims page: one input field, found in fourteen minutes; every reader declined to cite in every arm (the generated frame decided citation, the author text decided belief).

## Next
- CI read first: 44921930069, the run of this run's final push c7d06a1 (in progress at 16:01Z; Claims.lean and check_claims.py changed: the checked job's trust step regenerates CLAIMS.md; the frozen step runs O1 with its controls). Green on every job → nothing to promote. Red at the stale-CLAIMS step → `lake env lean scripts/trust/Claims.lean` and compare; red at `check_claims.py --base` → its O1 output.
- Part 3 next: the LEDGER experiment of this run — a second blind round on CLAIMS_READER.md with this fix, naming `literal_readings.txt` `source=`, `def_kinds.txt`, `pins.txt`, `headlines.txt` as untested and allowing one StatementDeps run (`judge_av.sh` reruns it when a defect touches its inputs).
- Part 1 next: as in section Next of `runs/2026-11-21T1228Z/README.md`.
- Parts 2/5 next: as in section Next of `runs/2026-11-21T1028Z/README.md`.

## End
- Local: `lake build Checked` (3775 jobs), `StatementDeps.lean` (clean, unchanged outputs), `Claims.lean` with the fix (CLAIMS.md / CLAIMS_READER.md: header lines only), `check_claims.py --base 9ac0ae3` (O1 controls ok), `records_check.py 9ac0ae3` (43 commands; the one failure, `check_headline_mentions` on this run's draft STATE line and the word 'withdrawal', fixed and rerun: 0 findings), `check_stale_necessity.py`, `check_stale_status.py --base 9ac0ae3`, `check_status_lines.py`, `precheck_citations.py`.
- Subagents: one Sonnet red team (≈ 14 min), ten Sonnet readers (one message, ≈ 9 s each).
- Message to Alexander (L.2): none (no finding, no promotion, nothing seriously wrong; the hole was in a page of the program and is closed in the same run).
