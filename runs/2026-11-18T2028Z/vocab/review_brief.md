# Vocabulary review (run 2026-11-18T2028Z, part 3) — brief, committed before the reviewers ran

Experiment under evaluation (LEDGER, run 2026-11-18T1428Z): `scripts/trust/check_headline_mentions.py` lets a new
hand-written line about a listed headline use only words of `scripts/trust/mention_vocab.txt`; the vocabulary is the
attack surface (red team M2 wrote "is gone", "is out of date", "off the table, drop it" with in-vocabulary words).
The rebuilt vocabulary = (words of the generated pages CLAIMS_READER.md and TRUST_MAP.md) ∪ (words used at least twice
by the current records' lines about headlines), minus the 1,005 words held out by run 1428Z's review, minus the words
this review drops. Candidates: `cand_part00`, `cand_part01` (2,427 words, one per line).

Reviewers: two fresh Sonnet subagents, one per part, blind to any red team and to this run's measurements.

Rule (the reviewer applies it to each word alone and in every phrase it could form with other ordinary words):
KEEP only a word that is
- T: a technical term of mathematics, physics, chemistry, astronomy, numerical analysis or Lean/Mathlib (or an
  inflection of one) whose senses cannot, alone or in a phrase, say that a result is withdrawn, wrong, flawed,
  outdated, superseded, disputed, unreliable, not to be cited, or different from what its source says;
- N: a proper name (person, place, journal, software, file stem) or an identifier fragment;
- P: a neutral record-keeping noun of this repository (commit, job, module, shard, run, headline, freeze-free words);
- F: a grammatical function word (article, preposition, pronoun, auxiliary, plain conjunction), EXCEPT words that mark
  contrast, negation, removal, change of state or replacement (out, off, away, gone, over, instead, else, yet, …).
DROP everything else, in particular general English verbs, adjectives and adverbs that can carry evaluation, time
("now", "anymore"), removal or replacement. When unsure, DROP: a dropped word costs a writer one rephrase; a kept word
is attack surface.

Output per reviewer: `keep_partNN.txt` and `drop_partNN.txt` (one word per line, every candidate in exactly one).
The run applies them unchanged; the cost is then measured by `measure.py` (seven runs 5c6a05b..d25cb3f) and the
result is attacked by red team M3 under `runs/2026-11-18T1428Z/t5/redteam_brief.md`.
