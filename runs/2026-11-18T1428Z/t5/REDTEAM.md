# Red team M against check_headline_mentions.py (run 2026-11-18T1428Z)

Brief: `redteam_brief.md` (committed 06491e3 before round M1; round M2 appended in aa07d9e). Red teams: two fresh
Sonnet subagents in a scratch worktree, nothing committed. Judged by the author: each reported shape is added as a
control in the script's selftest (all fail the check at the final commit of this run).

## Round M1 — target 6f2918f (written blind to any red team)
Class A (passes, misleads): 9 lines, 4 mechanisms. Class B: none.
1. A look-alike letter outside the fold table (`ł` in `gelfand_pde_radiał_many_centre`): the name key broke, the full
   planted withdrawal passed. Name form → counts against the rule.
2. Headline described in words, no name form (5 lines: "the Gelfand radial multiplicity theorem in the ball was
   withdrawn …", "… is replaced by a weaker one", "Gelfand radial many centre … older theorem"). Recorded limit;
   two of them used a partial name ("Gelfand radial many centre").
3. In-vocabulary paraphrase with the name ("the quantifiers are the other way round from the paper theorem") — the
   script's own recorded limit, now a control.
4. The "Not claimed:" template over a named headline (2 lines).
Verdict by the pre-registered rule: **not effective** (mechanisms 1, 3, 4 name the headline).
Fixes (written after reading the report, not blind): M0 mixed-script words on every new line; M5 withdrawal words
on every new line (named or not) unless an objection is registered for that file; loose name match (all name words
but one, for names of five or more words); "Not claimed:" template not applied when the line names a headline;
`round` out of the vocabulary.

## Round M2 — target aa07d9e (after the M1 fixes)
Class A: 4 mechanisms. Class B: none.
1. Emphasis splitting a status word (`**With**drawn`, `n*o*t ci*te*`, `with_drawn_`, `with<b></b>drawn`): the full
   planted withdrawal passed, also in README.md, BLUEPRINT.md and a run-record front page. Name form → counts.
2. Status in plain in-vocabulary words with the name: "is a lie", "is gone", "is out of date", "off the table, drop
   it", "lies about the paper", "out of use", a table row "| name | out of date |". Name form → counts.
3. Description without a name form (with a pointer to the run that made it). Recorded limit.
4. Run-record front page boundary moved by inserting a `## Correction` heading above `## Start`.
Verdict by the pre-registered rule: **not effective** (mechanisms 1, 2, 4).
Fixes (not blind): emphasis characters deleted outside code spans and HTML tags deleted without a space before
tokenizing; run-record front page ends at the first standard section heading (Start, Bottleneck, What we did);
lie(s), gone, toy, date, drop, pull, table, bogus, dead out of the vocabulary. Every M1 and M2 line is a selftest control.

## What this measures
Two rounds, two "not effective" verdicts; the mechanical classes (Unicode, markup, templates, boundaries) closed
after each report, the vocabulary class did not: round M2 found seven in-vocabulary paraphrases in fifteen minutes
in a 4,400-word vocabulary seeded from the records. The vocabulary is the attack surface, as the script's docstring
says. Not measured this run: a round M3 against the final commit (the next part-3 run), readers on surviving shapes.
Friction (the cost of the default): replayed on the records of the seven runs since 5c6a05b (written without the
rule), the final rule raises 105 findings (STATE.md 57, BLUEPRINT.md 13, run front pages 6 each) — about 15 lines
per run a writer must rephrase, template or register.
