# Run 2026-11-25T2028Z

**THE RESULT:** part 3 by rotation (STATE 3j; next step STATE 3k). The test and the rule of this run are in section What we did.

**What can a scientist now trust without checking it themselves, that they could not before?** That an objection to a statement's meaning shown as closed on the claims page was closed by a Lean theorem equating the statement with a blind reader's statement of the source, proved without any theorem of the program; a note, a verdict or any other file cannot close it (section What we did; `runs/2026-11-25T2028Z/t5/RESULTS_AZ.md`).

**Weakest unchecked step:** a closure proof that re-proves the headline from Mathlib alone, written so that no closed subterm proves a side, passes the rule while the reading may still be weak (section Measure); and blindness of a reading remains structural (commit order, no answer in the brief), as for every second reading.

## Start
- 20:27Z. `scripts/start_run.sh`: local main = origin/main 20ecc43; no LOCK (taken 87fb791, 48.4).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean v4.35.0 (elan), Mathlib cache present. Judge's build of d198472 (artifact of 45683665296) restored by streaming; `lake build Checked` replayed (3809 jobs). Subagents: six blind Sonnet readers.

## CI read
- 45683665296 (d198472, run 1828Z's final push): green on every job (goal guard, packet, changes, work, checked incl. the trust and frozen steps, leanchecker 4/4, nanoda 4/4). Nothing to promote (necessity theorems only).

## Bottleneck (and what a yes/no changes)
- Round AY: an entry of `scripts/trust/objections.txt` whose own note withdraws the query stays open for ever (rule O1), and readers decline to cite on it 2/2. A sticky registry also rewards not entering a doubt at all, the dangerous direction. Yes (a closure route readers accept and a forger cannot use cheaply) → an objection can be answered by evidence instead of by changing the statement. No → O1 stays and the cost is recorded.

## What we did
- **Test AZ, pre-registered** (`runs/2026-11-25T2028Z/t5/reader_brief_AZ.md`, committed alone in 76727bd before any reader ran): AY's material of the open entry on `lookback_second_order_bigO` in three versions (`scripts/material_az.py`): O open; V closed by a referee verdict file named by its path; E closed by a Lean theorem equating the statement with a blind reader's statement of the source, proved without any theorem of the program. Six fresh blind Sonnet readers, two per version. Results `t5/RESULTS_AZ.md`: O 0/2 cite (AY reproduced), V 2/2 cite, E 2/2 cite.
- **Decision by the pre-registered rule:** V stays out (its closing file is author prose the program writes, and readers cite on it as on a checked closure: a forger's full lever). E adopted:
  - `scripts/trust/Claims.lean`: `closureFaults` — the theorem named in a fifth field `closed by <theorem>` of an entry must state `R ↔ H` with `H` the headline's statement and `R` a definition of a `Checked.Trust.SecondReading*` module (so `check_blind_route.py` and `check_brief_leak.py` apply), every constant its proof reaches, followed through the program's definitions, may be no theorem of the program (no proof stored as a definition either), and no closed subterm of the proof may be a proof of either side by itself (`iff_of_true` with both sides re-proved). Eight planted controls in the same file run before any page is written: two valid closures accepted (`Iff.rfl`, a rewrite under the binder), six forged ones rejected for the planted reason (proof through the headline, through a helper theorem, through a proof stored as a definition; both sides re-proved from the core library; a reading outside the blind modules; neither side the statement). The Status line prints a closed entry with the theorem's name; the header of both pages states the rule and that no other entry or text can mark an objection settled.
  - `scripts/trust/check_claims.py` O1 counts an entry by its first four fields (a closure field keeps it; a reworded summary is still a removal; two new controls). `check_claims_fresh.py` F4 counts closed entries as well (one new control). `check_headline_mentions.py`: a closed entry licenses no dispute line (M3 needs an open one). `objections.txt` header: the closure format and why a file never closes an entry.
- The registry has no entry today, so no page entry changes; the header of CLAIMS.md and CLAIMS_READER.md does (regenerated, 313 claims).
- **Annex LIV:** PROMPT working note and LEDGER experiment (an equivalence of two proved propositions says nothing about meaning; the constants of its proof decide it).

## Measure
- Readers citing after a closure: E 2/2, V 2/2; open control 0/2. A forged verdict file would lift the doubt for 2/2 readers; the page never accepted one, and the header now says so.
- Forged closures rejected by the generator's controls: 6/6; valid controls accepted 2/2 (also run standalone in a scratch file with the faults printed, plus a `simp only` bridge, accepted, and one honest `rw` bridge on a toy statement that is itself a library lemma, rejected: the second rule's known false rejection).
- Known residue (`t5/RESULTS_AZ.md`): a re-proof of the whole headline written so that no closed subterm proves a side, with no lemma of the program, passes, and the reading can then be weak; cheap only for statements Mathlib proves in a line.
- Trust map unchanged (necessity 783 / 258 / 29 open; 313 headlines).

## Next
- CI read first: the run of this run's final push (Claims.lean, three Python checks, the two pages). Green on every job → nothing to promote. Red → its first failing command with the newest ancestor green on every job (d198472) as base.
- Part 3 next: the first honest closure, on a real objection, to measure the two proof rules on a real bridge (false rejections) and to attack them with a forged closure of the same headline (a blind red team given `closureFaults` and the eight controls). Then a fifth round on `headlines.txt` with a StatementDeps budget, and the multi-token reader constants of `redteamAY/brute.py` (section Next of `runs/2026-11-25T1428Z/README.md`).
- Part 1 next: as in section Next of `runs/2026-11-25T1828Z/README.md` (`fs_neg_decay_equal` 1).
- Parts 2/5 next: as in section Next of `runs/2026-11-25T1628Z/README.md`.

## End
- Local: `scripts/start_run.sh`, judge's build of d198472 restored by streaming, `lake build Checked` (3809 jobs, replayed), `Claims.lean` (313 claims, controls passed, 4 min 54 s), the closure controls standalone (scratch file, faults printed), `check_claims.py`, `check_claims.py --base d198472`, `check_claims_fresh.py` and `--selftest`, `check_claim_vocab.py`, `goal_guard.py`, `records_check.py d198472` (after the commit).
- CI read in this run: 45683665296 (d198472) green on every job.
- Message to Alexander (L.2): none (no finding, nothing wrong, no decision of his).
- CI of this run's final push 0be38fb: 45702125173 (started 21:12Z); the next run reads it (section Next).
