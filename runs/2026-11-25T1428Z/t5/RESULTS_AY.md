# Blind round AY — fourth round on the generated claims page CLAIMS_READER.md — run 2026-11-25T1428Z

Red team: Sonnet, blind (brief `briefAY.md` committed alone, 220e359 = the snapshot's HEAD; standalone clone
`/home/claude/fzAY` with this run's StatementDeps and Claims.lean outputs, `phrases.jsonl` included; build and packages
by symlink; ≈ 32 min). Asked for five defects; delivered five (`redteamAY/`, apply.py + claim.md each, its report and
its search script `brute.py`; the regenerated pages each apply.py copies are not committed: Claims.lean reproduces them,
checked for d01).
Readers: `reader_brief_AY.md` committed alone (bd5aec5) before the red team ran; answers and grading `READERS_AY.md`.

Judge `judge_ay.sh` (AX's, plus: commit what apply.py leaves uncommitted), BASE 220e359, Claims.lean per defect, every
Python command of the goal guard, the packet check and lean.yml's trust and frozen steps; no defect touched an input of
StatementDeps. Two trees in parallel (A: clean, d01, d04; B: d02, d03, d05). Verdicts `verdicts_AY.txt`.

| d | headline | registry route | planted belief | false? (judge) | checks BEFORE | readers | verdict | AFTER |
|---|---|---|---|---|---|---|---|---|
| d01 | `CPLExistence.printedL0_false_at` / `AvilesWitness.printedL0_false_at` | `objections.txt` entry under the namesake of the statement its note doubts (O2 matches the last name component) | the namesake's meaning is in doubt; the doubted statement has no objection | yes (the note examines only the AvilesWitness statement) | ACCEPTED | 2/2 decline to cite the namesake | VALID (lowers trust) + VALID-BY-HEADER (hides a recorded doubt) | CAUGHT by O3 |
| d02 | phrase lines of `IsFlatLCDM`, `IsFlatCPL` | `phrase_certs.txt`: certified by theorems proving only H > 0 | the model identity lines are proved | yes | CAUGHT (Claims.lean P13) | — | INVALID | — |
| d03 | phrase lines of `cosmoCoeff` (jerk, snap, lerk) | `phrase_certs.txt`: certified by `cosmoCoeff_two` | as d02 | yes | CAUGHT (Claims.lean P13) | — | INVALID | — |
| d04 | `lookback_second_order_bigO` | `objections.txt` entry whose note drops the query | the meaning is in doubt | yes (the note's verdict is STANDS) | ACCEPTED | 2/2 decline to cite | VALID (lowers trust), by design not closed | unchanged |
| d05 | Duffing phrase lines | `phrase_certs.txt`: certified by `duffing_initial` | as d02 | yes | CAUGHT (Claims.lean P13) | — | INVALID | — |

Not tried in the time: slot swaps in `literal_slots.txt` (the red team found rule T3 of `check_literal_targets.py`
rejects a slot line covering nothing, so only swaps between equal values pass), `headlines.txt` (each try needs a
StatementDeps rerun and new freeze and witness lines), the B3 header exemption (needs a new reader `.lean`, out of the
round's allowed changes), and multi-token reader constants that would cover literals of unrelated headlines if
registered (`brute.py`; close to AX d04, which rule 1 (d) closed for one-numeral name-free readings only).
