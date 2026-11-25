# Run 2026-11-25T0828Z

**THE RESULT:** part 3 by rotation (STATE 3d; next step STATE 3e). The round, its judge and its readers are in section What we did; the four new rules in the same section.

**What can a scientist now trust without checking it themselves, that they could not before?** That a count of blind-read numbers shown on the claims page counts only numbers the reader itself wrote, that a reading shown there was made for that statement's own model, that a source name shown there is not a word from a reader's note saying it used no source, and that a statement shown as a transcription is not a proposition the program built around reader data: a third blind red team got four such records onto the page past every check; the new rules catch all four.

**Weakest unchecked step:** the readers' honesty (a forged brief and reading still passes, as in rounds AV and AW); and which hypotheses of each `CLAIM` the source in fact makes — the page says they are the program's, and no check compares them with the source.

## Start
- 08:27Z. `scripts/start_run.sh`: local main = origin/main 0f6bb06; no LOCK; LOCK taken (c88c88c).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean v4.35.0 (elan), Mathlib cache; judge's build of dcdaa3b (artifact of 45568879141) restored by streaming; `lake build Checked` replayed it (3791 jobs); StatementDeps without relock (≈ 15 min; outputs unchanged). Disk: 1–2 GB free after the restore (pip and Mathlib download caches removed). Subagents: one red team, eight readers (Sonnet).

## CI read
- Nothing to read: 45568879141 (dcdaa3b), the run of the last final push, was read green on every job by run 0628Z; the commits after it are records with the skip marker.

## Bottleneck (and what a yes/no changes)
- Rounds AV and AW each got every defect past the checks of the claims page through one registry field per round (AW: 5/5 valid). With AW's three rules in place, does a fresh blind red team still get records onto the page that mislead a reader, through the fields AW named as untested (`literal_slots.txt`, the readers' sources clauses, `headlines.txt`, the definition-header exemption of B3)? Yes → which fields, and a rule each (and, per run 0228Z's plan, print each reader's own sources clause on the page). No → the page's fidelity record can be cited as having resisted three rounds.

## What we did
- **Round AX** (`t5/`): brief `briefAX.md` committed alone (6e7591b = snapshot), reader brief `reader_brief_AX.md` committed alone (c12ef24) before the red team ran; snapshot `/home/claude/fzAX` with this run's StatementDeps outputs. Red team (Sonnet, blind, ≈ 36 min) delivered four defects and its caught attempts; output committed verbatim (`t5/redteamAX/`, 7faf4e9) before judging.
- **Judge** `t5/judge_ax.sh` (round AW's), two trees in parallel (d01 needs StatementDeps): verdicts `t5/verdicts_AX.txt`.
- **Readers:** two fresh blind Sonnet readers per defect, eight in one message, each given only the page header and the changed entry (`t5/reader_material/`); grading `t5/READERS_AX.md`: **0 of 4 valid** — every planted belief is false, but no reader built a conclusion on it. Table `t5/RESULTS_AX.md`.
- **Fixes anyway** (each puts a false generated statement on the page; strengthening only; planted controls on a scratch tree):
  - `check_literals.py` — the loose span match (every numeral in a matched span, including those a binder wildcard swallowed) now applies only to the six old pairs of the new shrink-only `loose_span_baseline.txt`; every other pair is matched strictly (d02: `b1a3Modulus`'s wildcard swallowed the fit coefficients of `l19_sq_central`).
  - `check_literals.py` rule 1 (d) — a binder reader constant with one numeral and no name but its binders (`fun ζ => ζ 5`) may be registered for a new headline only if its module is, imports, is imported by, or shares a direct model import with the module of a headline it was read for (`namefree_reading_baseline.txt`, 148 old pairs, shrink-only) (d04: the Gelfand reader `ζ 5` covered the order 5 of a cosmography series). Positive control: a Gelfand headline reusing `ζ 4` with its own line removed passes through its anchors.
  - `check_literals.py` rule 1 (c) — a sources clause that says the reader used no outside source (`no … sources`, `sources: none`) backs no source name (d03: `Taylor` of "Taylor odefun … no external sources").
  - `check_templates.py` rule 3 — a program proposition (`: Prop`) with a generated claim reading must be labelled CLAIM in `def_kinds.txt` (d01: relabelled PRINTED, it left the template rules and the page dropped "the quantifiers and hypotheses are the program's formalisation").
- Not attacked by the red team in its time: `literal_slots.txt`, `headlines.txt`, the B3 definition-header exemption (listed again in section Next).

## Measure
- Round AX BEFORE: 4/4 accepted by the checks (verdicts); valid by blind readers 0/4. AFTER: 0/4 accepted.
- Three rounds on the claims page: AV 2/5 valid → closed; AW 5/5 valid → closed; AX 0/4 valid (4 false records reached the page; 4 closed).
- Trust map unchanged (NEEDED 775, REDUNDANT 254, open 33; 311 headlines). No Lean file changed.

## Next
- CI read first: the run of this run's final push (Python checks changed: `check_literals.py`, `check_templates.py`; two new baselines; no Lean file). Green on every job → nothing to promote. Red → its first failing command with the newest ancestor green on every job (dcdaa3b) as base (`python3 scripts/trust/records_check.py dcdaa3b`).
- Part 3 next: the fields no round has touched — `literal_slots.txt` (a slot line at a role the reader did not mean), `headlines.txt`, and the B3 definition-header exemption of `check_blind_route.py` — as a fourth blind round, or a held-out reader test of the Status line itself (which of its items readers use: AX's readers passed over counts and source names in its middle, AW's took the provenance at its head as fact). The Soave record (`source_clause_baseline.txt`) stays as in run 0228Z's Next.
- Part 1 next: as in section Next of `runs/2026-11-25T0628Z/README.md`.
- Parts 2/5 next: as in section Next of `runs/2026-11-25T0428Z/README.md`.

## End
- Local: `scripts/start_run.sh`, judge build of dcdaa3b restored by streaming, `lake build Checked` (3791 jobs), `StatementDeps.lean` (no relock; outputs and TRUST_MAP.md unchanged), the judge (two trees), `check_claims.py` per defect with `.lake/phrases.jsonl` in place, planted controls of the four new rules on a scratch tree, `Claims.lean` (pages unchanged), `records_check.py dcdaa3b` (46 commands, 0 failed).
- CI of the final push: not read in this run (section Next).
- Message to Alexander (L.2): none (no finding, no promotion, nothing wrong).
