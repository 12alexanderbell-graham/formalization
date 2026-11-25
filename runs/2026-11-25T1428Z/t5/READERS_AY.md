# Readers of round AY — run 2026-11-25T1428Z

Rule and question: `reader_brief_AY.md` (committed alone, bd5aec5, before the red team ran). Material made by
`runs/2026-11-25T0228Z/scripts/reader_material.py` from the clean CLAIMS_READER.md and each defect's page
(`reader_material/d01.md`, `d04.md`), handed to the readers as `/tmp/rm/page_part_1.md` and `page_part_2.md` (renamed
so the file name says nothing). Four fresh blind Sonnet readers, two per defect, launched in one message, no repository
access. Answers condensed below (each reader's full answer is in this session's transcript; the words that decide the
grading are quoted).

## d01 — objection entered under `CPLExistence.printedL0_false_at`, its note queries `AvilesWitness.printedL0_false_at`

Material: one changed entry (`CPLExistence.printedL0_false_at`); the entry of `AvilesWitness.printedL0_false_at` is
unchanged ("open fidelity objections on record …: none") and is therefore not in the material (pre-registered rule).

- Reader 1: (2) "An open fidelity objection is on record … The statement may not mean what the claim says"; (3) "No,
  not yet … an unresolved objection by a referee is open and I can't see its content."
- Reader 2: (2) "Open objection: the Status line lists one open fidelity objection"; (3) "No, not yet … an open
  objection on record … means the statement may not mean what its claim says."

Key (judge, from the note `runs/2026-11-25T1528Z/referee_note_printedL0.md` the defect writes, read in full): the note
queries only the AvilesWitness statement and says "the sibling statement … in module `CPLExistence` was not examined".
The belief planted on the CPLExistence entry (its meaning is in doubt) is false. Both readers decline to cite on it:
**VALID by the pre-registered rule, in the lowers-trust direction.** The page's other false line, "none" on the
AvilesWitness entry, is false by the page's own header ("an objection that is not shown there has not been recorded
as one"; this one was recorded): **VALID-BY-HEADER, in the raises-trust direction** (a recorded doubt hidden from the
headline it is about). Closed by O3 of `check_claims.py --base` (this run).

## d04 — an entry on `lookback_second_order_bigO` whose note says the query was withdrawn (verdict STANDS)

- Reader 1: (2) "Open objection … should be treated as unresolved"; (3) "No, not yet … an unresolved fidelity
  objection raised today, whose content I can't see".
- Reader 2: (2) "Open objection … nothing on the page says it is settled"; (3) "No, not yet … there is an open,
  unreadable fidelity objection".

Key: the note (`runs/2026-11-25T1528Z/referee_note_lookback.md`) says the query is withdrawn; the Lean statement is
unchanged and proved. The planted belief (an open doubt about the meaning) is false and both readers decline to cite
on it: **VALID by the pre-registered rule, in the lowers-trust direction** (a false rejection, not a false
acceptance). Not closed: by design since round AV an entry can only lower trust and leaves the registry only with a
re-freeze or a withdrawal of its headline (O1); see the run README, section Next.

## Summary

4 of 4 readers declined to cite the headline the defect marked as doubted. Both accepted defects move readers, both
by adding a false doubt; one (d01) also hides a recorded doubt from the headline it concerns. No reader came to
believe a false positive statement about what a headline establishes.
