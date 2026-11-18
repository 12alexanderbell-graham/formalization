# Run 2026-11-18T1428Z (scheduled)

**THE RESULT:** part 3 by rotation (every link machine-checked, here the link from a hand-written record to what a
reader believes about a listed result) — a blocking check with the opposite default to every earlier prose rule:
`scripts/trust/check_headline_mentions.py` flags a new line of STATE.md, README.md, BLUEPRINT.md or a run-record front
page that is about a listed headline, in any name form, unless all its words are in a closed classified vocabulary,
any status it states sits in a CI-backed template, or an objection is registered for that file in
`scripts/trust/objections.txt` (then the generated pages print it). Attacked by two blind Sonnet red teams; both
rounds found class-A shapes (verdict: not effective), every shape found is now a control and fails the check.

**What can a scientist now trust without checking it themselves, that they could not before?** That a hand-written
sentence added to the records from now on, naming a listed result in any spelling, does not contradict its generated
Status line unless the objection is registered and printed on the generated claims pages — for the 22 shapes
two red teams found and every shape made only of words outside a closed 4,400-word vocabulary. Not yet: a status
written in ordinary words inside that vocabulary (red team M2 found seven in fifteen minutes) or a result described
without any form of its name.

**Weakest unchecked step:** the vocabulary itself (seeded from the records and reviewed once by a model): in-vocabulary
paraphrases of the planted status sentence W′. Next: shrink it to the words of the generated pages plus a reviewed technical list, and
run red team M3.

## Start
- 14:28Z. add_repo not exposed; checkout at d25cb3f = origin/main (`git checkout main`, fast-forward). No LOCK → taken
  (72b3cf9). No local Lean this run (no Lean file changed; Python only).
- CI at start: 44300401557 (a736a0b) checked job cancelled while pending (nanoda 0, 1, 3 green); 44316709810 (d25cb3f)
  pending; 44275141268 (7d5b41c) in progress. Nothing judged; the promotion of a736a0b is judged by d25cb3f's run.

## Bottleneck (and what a yes/no changes)
- Rotation: part 3 (STATE 1n → 1l). Runs 0228Z and 0828Z measured that one hand-written withdrawal sentence (W′)
  beats every generated line for 9/9 readers, and that a word rule against it (S3) fell ≈ 40 ways. Question: does a
  default-flag rule (closed vocabulary, templates, registry) hold against a blind red team? Yes → W′ cannot reach the
  records; no → measure which classes remain and whether they are mechanical (fixable) or semantic (vocabulary).

## What we did
1. Wrote `check_headline_mentions.py` (rules M0–M5, docstring) and `mention_vocab.txt` before any red team: name keys
   from `headlines.txt` and the modules on `CLAIMS_READER.md`, NFKC/fold/entity/tag normalization, letters-and-digits
   skeleton; a line is about a headline if a key occurs within two non-blank lines or in its heading chain. Vocabulary:
   the records' words minus the STATUS class minus 1,005 words held out by a Sonnet review
   (`vocab/held_out_by_review.txt`), plus a short list of process words put back by hand.
2. Pre-registered the red-team brief (06491e3), ran rounds M1 and M2 (`t5/REDTEAM.md`), fixed after each report (not
   blind) and turned every class-A line into a selftest control (22 defect controls, 2 correct-line controls, M3).
3. CI: frozen step runs `check_headline_mentions.py --base "$BASE"`; the rule binds from its introduction commit
   6f2918f, so older records are not new to it (records_check picks it up from lean.yml).
4. Annex LIV: PROMPT working note; LEDGER entry (vocabulary, rule, experiment).
