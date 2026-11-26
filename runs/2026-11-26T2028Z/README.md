# Run 2026-11-26T2028Z

**THE RESULT:** part 3 (what the gates catch, and what a reader may rely on): every headline's fidelity record now says which of its parts the kernel re-derives from the statement — holding whoever wrote anything — and which rest on who wrote a statement, with generated totals; a pre-registered reader test kept the split (old page 3 misclassifications in 3 readers, new page 0 in 3).

**What can a scientist now trust without checking it themselves, that they could not before?** Which part of a claim's fidelity record still stands if the program's authors wrote every reading themselves: for each of the 316 headlines the Status line separates (A) non-vacuity, hypothesis necessity and shape, re-derived by the kernel from the statement, from (B) objection entries, blind readings, grandfathered literals and the specifications that pin definitions; 291/316 headlines have part A complete. Before, the record was one list and 2/3 readers counted a program-written pinning specification as kernel evidence.

**Weakest unchecked step:** the specifications that pin definitions. 494 definition uses on the claims page rest on a specification the program wrote (the kernel checks only that it determines the definition); no part-B item covers them, and 6/6 readers named exactly this (the Robertson ODE system of `rob_state40`) as what an outside party should redo.

## Start
- 20:28Z. Session clone detached at e8e94a4 (= origin/main); local `main` was stale and divergent, reset to origin/main (`git checkout -B main origin/main`; `scripts/start_run.sh` then found nothing local-only). No `LOCK`; LOCK taken f8ff7bc.
- `EXTERNAL_LOCK`: run 2026-11-26T1529Z, heartbeat 20:20Z (8 minutes old, then refreshed during this run): the external targets stay with it; this run does the rotation (part 3).
- Env: repo ok (`add_repo` not exposed; clone present). Local Lean (elan, 4.35.0, Mathlib cache), judge's build of e73f59e restored by streaming, `lake build Checked` replayed (3846 jobs). Subagents: six Sonnet readers.

## CI read
- 45883803792 (2b0ad6a, run 1828Z's final push): **success** on every job. Nothing to promote (no `Checked` change).
- 45879038856 (e73f59e, a PROMPT push from a chat session): failure in the frozen step, `check_headline_mentions.py` M2 on the heading of `runs/2026-11-26T1529Z/README.md` (reproduced locally with base 1a6d332: 5 findings); already repaired by run 1828Z in 2b0ad6a (0 findings at HEAD), green above. Base for this run's checks: 2b0ad6a.

## Bottleneck
Section Next of `runs/2026-11-26T1428Z/README.md`: three part-3 runs showed that every check on a reading certifies its route, not its author (a copy of the headline passes as a blind reading). The record on each Status line mixed kernel-re-derived facts and author-dependent ones in one list. Yes (readers separate them better with a split) → the page says plainly what survives distrust of the authors, and the trust metric counts it; no → revert, and the header sentence suffices.

## What we did
1. **Two-part record** (`scripts/trust/Claims.lean`): the Status line's fidelity record is printed as **(A) re-derived by the kernel from the statement** — the non-vacuity witness, the necessity of each numbered hypothesis, and the shape entries (assumptions the numbering does not reach or reaches only as a bundle), with "part A complete" or "PART A INCOMPLETE (reason)" — and **(B) rests on who wrote a statement** — objection entries, blind literal readings, grandfathered literals, and the definitions the claim uses counted as pinned by a program-written specification / with a blind second reading or formulation / with neither. Header paragraphs on both pages explain the split; a generated **Split totals** line replaces a placeholder after the loop. All substrings that `check_claims_fresh.py` parses are kept.
2. **Shape in part A** (`scripts/trust/StatementDeps.lean`): the first build counted 307/316 complete because Claims.lean did not see shape entries; StatementDeps now writes `.lake/necessity_shape.tsv` (16 headlines; CI runs it before Claims.lean in the same step) and Claims.lean fails if the file is missing. With shape: **291/316**, equal to TRUST_MAP's 164/189 fully classified plus 127 headlines without hypotheses.
3. Regenerated CLAIMS.md, CLAIMS_READER.md (TRUST_MAP.md, PHRASE_LINES.md unchanged) and the validation packet (`make_packet.py`; its 48 items carry Status lines; round 2 not sent, so not frozen).
4. **Reader test** (`t5/reader_brief.md`, committed in 4cfe6bd with the fix and both pages before any reader ran; results `t5/RESULTS.md`): one headline (`rob_state40`), worst-case authorship; old page 3 errors (two readers counted the pinned definition as kernel evidence, one the literal coverage), new page 0; Q2 ("is there machine-checked evidence the statement says what its source says?") "no" 6/6. Rule met: split kept.

## Measure
- Trust metric (new, generated in the page headers): part A complete **291/316**; numbered hypotheses 1082 (804 needed, 263 redundant, 15 open). Part B: 147 headlines with blind literal readings, 121 with grandfathered literals, 0 open objections; definition uses 494 pinned by program-written specifications, 536 with a blind second reading or formulation, 86 with neither.
- Readers: misclassified record items 3/3 readers' worth on the old page → 0 on the new (3 + 3 readers, one headline; a direction, not a rate).

## Next
- CI read first: the run of this run's final push (Claims.lean and StatementDeps.lean changed; the pages and packet regenerated). Green on every job → nothing to promote. Red → its first failing command with 2b0ad6a as base (if the trust step fails on a missing `.lake/necessity_shape.tsv`, StatementDeps did not run first in that job).
- External test: while `EXTERNAL_LOCK` is fresh, run 1529Z keeps it (PROMPT 11).
- Part 3 next: the part-B gap the readers named — **blind second readings of pinning specifications**. 494 definition uses rest on a specification only the program wrote; start with the definitions reached by the most headlines (count from CLAIMS.md: `— **PINNED**` lines per definition), a reader writes the specification from the source alone, and a Checked theorem states its agreement with the pinned one (as `Checked/Trust/Transcriptions*.lean` does for PRINTED definitions); print the count per headline in part B. Also: the page could say that literal readings are compared by exact value (reader new1).
- Part 1 next: as in section Next of `runs/2026-11-26T1828Z/README.md`. Parts 2/5 next: as in section Next of `runs/2026-11-26T1628Z/README.md`.

## End
- Local: restored judge build, `lake build Checked`, StatementDeps + Claims (17.8 min together), `make_packet.py`, `records_check.py 2b0ad6a` (46 commands, 0 failed after the last record edit; earlier passes failed on the stale packet and on one STATE line's words, both fixed).
- Message to Alexander (L.2): none (no headline or status changed; a page-format change with a small reader test).
