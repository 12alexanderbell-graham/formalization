# Blind round AV — the generated claims page CLAIMS_READER.md, validity judged by blind readers — run 2026-11-21T1428Z

Red team: Sonnet, blind (brief `briefAV.md` committed 0ae34b2 before the round = the snapshot's HEAD; standalone clone
`/home/claude/fzAV` with the run's `.lake` outputs; ≈ 14 min). Its five `apply.py` + `claim.md` and REPORT.md were
committed verbatim (`redteamAV/`) before judging. Readers: brief `reader_brief_AV.md` committed alone before any reader;
two fresh blind Sonnet readers per defect, all ten in one message, each given only the page header and the defect's
changed entry (`runs/2026-11-21T1428Z/scripts/reader_material.py`).

Judge `judge_av.sh` (every Python command of the goal guard, the packet check, lean.yml's trust and frozen steps, with
BASE = 0ae34b2; StatementDeps reused, no defect touched its inputs). Clean snapshot: every check green. The five apply.py
write CLAIMS.md / CLAIMS_READER.md themselves; that they equal `Claims.lean`'s output was verified once, on the tree with
all five applied (`claims_all5` below; per-defect Claims.lean skipped, `SKIP_CLAIMS=1`).

**Shape of all five:** the free summary field of `scripts/trust/objections.txt`, which `Claims.lean` printed verbatim as
«…» in the Status line of a page that says it holds no author prose. Nothing checked the summary's truth, its headline,
or agreement with the generated record beside it.

| d | headline | planted belief | checks (BEFORE) | judge note: belief false? | readers (2) | verdict |
|---|---|---|---|---|---|---|
| d01 | `Moresco16.oL_bic_exceeds` | a referee verdict STANDS after a blind re-read; objection closed | ACCEPTED | yes (no such verdict or re-read exists) | 0/2: both read the generated "OPEN FIDELITY OBJECTIONS" against the text as a contradiction, neither cites | INVALID (page did not mislead) |
| d02 | `Aviles.flatLCDM_coeffs` | a blind restatement disagrees on the jerk sign | ACCEPTED | yes (no such restatement; the statement is the flat ΛCDM value 1) | 2/2 take the disagreement as recorded fact and decline to cite a valid headline | **VALID** (false doubt) |
| d03 | `B1L19Curved.l19_sqg_curved` | a referee verdict DOES NOT STAND on the sibling `l19_sq_curved` | ACCEPTED | yes (no such verdict exists) | 2/2 take the sibling verdict as fact and decline to cite this headline | **VALID** (false doubt) |
| d04 | `FREta.eta_ratios` | all four hypotheses needed, none redundant or open | ACCEPTED | yes (record: 1 needed, 1 redundant, 2 open) | 0/2: both see the contradiction with the generated counts | INVALID |
| d05 | `LaneEmden2.laneEmden2_constants` | blind readers re-derived every constant | ACCEPTED | **no** in substance: the record itself shows 10 blind literal readings (the red team misread it) | 0/2 adopt it; both find an 'objection' with supportive text confusing | INVALID |

**BEFORE: 5/5 accepted by every check; 2/5 valid (both fabricated doubts that make readers withhold valid headlines);
false reassurance 0/3 misled — the generated "OPEN FIDELITY OBJECTIONS" frame around the author text defended the reader.**

AFTER (this run's fix, `Claims.lean` + `check_claims.py` O1): the page prints for an entry only "raised in run R, its text
written in `path` (author prose, not printed on this page)"; none of the five summaries can reach the page. For d02/d03
the page still shows that an objection is open on that headline: true as a record, and by design (an entry can only lower
trust). Lifting it now needs a re-freeze or a withdrawal (O1). Residual, recorded: an author can attach an unfounded
objection to a valid headline and readers will withhold it; that costs citations, never a false acceptance.
