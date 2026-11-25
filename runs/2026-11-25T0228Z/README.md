# Run 2026-11-25T0228Z

**THE RESULT:** part 3 by rotation (STATE 3a; next step STATE 3b). The round, its judge and its readers are in section What we did; the three new rules in the same section.

**What can a scientist now trust without checking it themselves, that they could not before?** That a source name shown beside a blind reading on the claims page is one the reader itself says it read, that a reading shown there is tied to a slot of the statement, and that an objection shown there points at a file that names it: a blind red team got five wrong records onto the page past every check (and five of five misled blind readers); the new rules catch all five.

**Weakest unchecked step:** the slot lines and the reader files themselves are written by authors and readers whose honesty no check can test (a forged slot, or a forged brief and reading, still passes); and one old record of the same shape stays on the page (section Measure).

## Start
- 02:28Z. `scripts/start_run.sh`: local main = origin/main de9bdf5; no LOCK; LOCK taken (9ba13df).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean v4.35.0 (elan); the Mathlib cache was incomplete (a first `start_run.sh` call was killed at the two-minute tool limit during `lake exe cache get`) and was fetched again; judge's build of 70c5035 (artifact of 45529799839) restored by streaming; about 2 GB of disk left. Subagents: yes (Sonnet).

## CI read
- 45529799839 (70c5035, run 0028Z's final push): every job green (leanchecker 4/4, nanoda 4/4, work, goal guard, packet) except the checked job, whose frozen step failed on `check_headline_mentions.py` alone: M1/M2/M6 on lines 5 and 7 of `runs/2026-11-25T0028Z/README.md`, whose front page named two headlines by their Lean names in words outside the mention vocabulary. Run 0028Z had run `records_check.py` before writing that page.
- Repair 7f9995f: front page rewritten in the vocabulary; the first-pushed lines kept verbatim in that README (section Front page as first pushed). 45535081586 (7f9995f): green on every job → the promotion of run 1628Z is judged; STATE heading in the judged template.

## Bottleneck (and what a yes/no changes)
- Run 1428Z's round AV closed the one field (objection summaries) through which a blind red team had reached CLAIMS_READER.md, the page every banner sends readers to. Does the page now resist a fresh blind red team aimed at the fields AV never touched (`literal_readings.txt` `source=`, `def_kinds.txt`, `pins.txt`, `headlines.txt`, phrases)? Yes → the page's fidelity record can be cited as checked. No → which fields, and a rule for each.

## What we did
- **Round AW** (`t5/`): brief `briefAW.md` committed alone (c5c5dbb = snapshot), reader brief `reader_brief_AW.md` committed alone (64e06c7) before the red team ran; snapshot `/home/claude/fzAW` with this run's StatementDeps outputs. Red team (Sonnet, blind, ≈ 66 min) delivered five defects and reported its failed attempts (kind relabelling to PRINTED caught by StatementDeps and check_templates; closed constants outside their slot caught by T2/T3; phrase and certificate routes caught by P7–P13). Output committed verbatim (`t5/redteamAW/`, 72a303a) before judging.
- **Judge** `t5/judge_aw.sh` (round AV's, one change: findings of the stale-status rule that the clean tree also has do not count, because BASE is the brief commit rather than a green ancestor): clean tree green; each defect ACCEPTED by every check (`t5/verdicts_AW.txt`); `Claims.lean` on the tree with all five applied reproduced their pages.
- **Readers**: two fresh blind Sonnet readers per defect, ten in one message, each given only the page header and the changed entry (`t5/reader_material/`); answers and grading `t5/READERS_AW.md`; table `t5/RESULTS_AW.md`.
- **Fixes (strengthening; planted controls in a scratch tree):** `check_literals.py` rule 1 (c) — a `source=` name must occur as a word in the sources clause the reader wrote in its runs/ copy (d01, d03, d04); `check_literal_targets.py` T5 — a closed reader constant registered for a headline needs a slot line (d02); `check_claims.py` O2 — the file an objection points at must name the headline (d05, three controls). Two new shrink-only baselines for old registrations (`source_clause_baseline.txt`, `decorative_reading_baseline.txt`), each with a `--base` rule; a line added to either fails.
- **Annex LIV:** `scripts/check_commit_msg.py --final` reruns `check_headline_mentions.py` against origin/main when a final commit stages STATE, README, BLUEPRINT or a run README (authoring flag `--no-stale`; CI never passes it). Planted control: a new front-page line naming a headline fails the commit check; the corrected page passes.

## Measure
- Round AW BEFORE: 5/5 accepted by every check; valid by blind readers 5/5 (d01 2/2, d02 1/2, d03 2/2, d04 2/2 took a false provenance as fact and cited on it; d05 2/2 declined a valid headline over a pointer to a file that says nothing against it). AFTER: 0/5 (each caught by one new rule).
- Two rounds on the claims page: AV 2/5 valid → closed; AW 5/5 valid → closed. Every accepted defect of both rounds went through a registry field whose truth was decided by text the program or an author wrote (a summary; a name in a brief; a numeral anywhere).
- Found by the round in the records: `kappaSoave` with `source=Soave` (headlines `srk_omega1_exists`, `srk_omega1_unique`) has d01's shape — its reader read three software documentation pages — and stays on the page, grandfathered and disclosed in `source_clause_baseline.txt`.
- No Lean file changed; trust map unchanged (NEEDED 772, REDUNDANT 252, open 34; 310 headlines).

## Next
- CI read first: the run of this run's final push (Python checks changed: `check_literals.py`, `check_literal_targets.py`, `check_claims.py`, `check_headline_mentions.py`; no Lean file). Green on every job → nothing to promote. Red at the frozen step → its first failing command with BASE 7f9995f (`python3 scripts/trust/records_check.py 7f9995f`).
- Part 3 next: the LEDGER experiment of this run — a third blind round on CLAIMS_READER.md with these rules in place, naming `literal_slots.txt`, the reader sources clauses and `headlines.txt` as untested. If it gets more than one valid defect past the checks, print each reader's own sources clause on the page next to the source names (`Claims.lean`) instead of another match rule. Also: the Soave record — a blind reader of Soave 1972 (`kappaSoave` slot), or reword the SRK docstrings at the next relock so the source name can leave the registry.
- Part 1 next: as in section Next of `runs/2026-11-25T0028Z/README.md`.
- Parts 2/5 next: as in section Next of `runs/2026-11-21T1628Z/README.md`.

## End
- Local: `lake build Checked` (restored build, 3785 jobs), `StatementDeps.lean` (no relock; ≈ 15 min), `Claims.lean` twice (main tree: pages unchanged; judge tree with all five defects: pages equal the defects'), the judge (six trees), planted controls of the three new rules, `records_check.py 7f9995f` (43 commands, 0 failed; after the last record edit).
- The new commit check failed this README's front page on the first final commit (`records_check.py` had run while the file was untracked, and the mention check reads tracked files only); reworded ('printed', 'false' → 'shown', 'wrong'), commit check green.
- LOCK: run 2026-11-25T0428Z took this run's LOCK over at 05:07Z (48.4; this run's last heartbeat was 04:26Z) for a disjoint task (parts 2/5); this final commit keeps that run's LOCK.
- Message to Alexander (L.2): the promotion of run 1628Z, judged green (one line).
