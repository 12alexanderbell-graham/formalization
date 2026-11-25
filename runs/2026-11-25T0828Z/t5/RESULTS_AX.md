# Blind round AX — third round on the generated claims page CLAIMS_READER.md — run 2026-11-25T0828Z

Red team: Sonnet, blind (brief `briefAX.md` committed alone, 6e7591b = the snapshot's HEAD; standalone clone
`/home/claude/fzAX` with this run's StatementDeps outputs; build and packages by symlink; ≈ 36 min, one StatementDeps
relock and several Claims.lean runs in its copy). Asked for five defects; delivered four, and its caught attempts
(`source=Peng` for `pr_omega1_exists`: rule 1 (c); a closed constant with no slot line: T1/T2; the first form of d01:
`check_templates.py` rule 1; a FORMULA relabelled PRINTED: StatementDeps, no Transcriptions agreement). Output committed
verbatim (`redteamAX/`, 7faf4e9) before judging; the regenerated pages each apply.py copies are not committed
(Claims.lean reproduces them).
Readers: `reader_brief_AX.md` committed alone (c12ef24) before the red team ran; answers and grading `READERS_AX.md`.

Judge `judge_ax.sh` (= round AW's), BASE 6e7591b, every Python command of the goal guard, the packet check and lean.yml's
trust and frozen steps; d01 reran StatementDeps (it touches `frozen.txt` and `def_kinds.txt`), d02–d04 reused BASE's
outputs; `SKIP_CLAIMS=1` (each apply.py writes the pages). Verdicts `verdicts_AX.txt`. One artefact of this run's
setup: the snapshot had no `.lake/phrases.jsonl` (written by Claims.lean, which this run had not run before the round),
so `check_claims.py` failed on the clean tree and on every defect alike; it was rerun per defect with the file in place
(section "check_claims" of `verdicts_AX.txt`).

| d | headline | registry route | planted belief | false? (judge) | checks BEFORE | readers | verdict | AFTER |
|---|---|---|---|---|---|---|---|---|
| d01 | `avilesL0Claim_false` | `def_kinds.txt` CLAIM → PRINTED for `AvilesL0Claim` (+ relock, template line removed, two LEDGER lines) | the whole proposition was transcribed and confirmed by a blind reader | yes: only the inline printed data were read; quantifiers and hypotheses are the program's | ACCEPTED | 0/2 | INVALID | caught: `check_templates.py` rule 3 |
| d02 | `l19_sq_central` | reader `b1a3Modulus` registered; baseline line shrunk | the fit coefficients were read blind | yes: they sit inside the reader's wildcard | ACCEPTED | 0/2 | INVALID | caught: `check_literals.py` (loose span only for `loose_span_baseline.txt`) |
| d03 | `laneEmden32_constants` | `source=Taylor` | a source by Taylor backs the reading | yes: the clause says "no external sources"; Taylor is the integrator's method | ACCEPTED | 0/2 | INVALID | caught: rule 1 (c) (a clause that disclaims sources backs no name) |
| d04 | `lookback_fifth_order` | Gelfand reader `ζ 5` registered; baseline line deleted | every literal was read twice or certified | yes: the reading is of another model | ACCEPTED | 0/2 | INVALID | caught: rule 1 (d) |

**BEFORE:** every defect accepted by the checks (verdicts); **0 of 4 valid by blind readers**, although every planted
belief is false and three of the four put a false generated statement on the page (a literal count, a source name,
"no literal of the statement is grandfathered as unread"). **AFTER: 4/4 caught** (planted controls on a scratch tree:
each apply.py on a tree with the new rules, BASE = that tree's commit; positive control: a later Gelfand headline
reusing `ζ 4` with its anchor line removed still passes; each new baseline grown by one line fails its `--base` rule).

Three rounds on the claims page: AV 2/5 valid, AW 5/5 valid, AX 0/4 valid. The page's provenance lines (source names
printed at the head of the Status line) were what misled readers in AW; the routes left after AW's rules reach only
counts and labels in the middle of the record, which blind readers did not build on.
