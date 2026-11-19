# Rule M6 and red team round M4 (run 2026-11-19T0228Z, part 3) — pre-registered, committed before the red team ran

## The rule (written blind to any red team of it; `scripts/trust/check_headline_mentions.py`, function `m6`)
A new line of STATE.md, README.md, BLUEPRINT.md or a run-record front page that is about a listed headline (M1–M5
scope, unchanged) and NAMES A SOURCE — a year 1800–2099 that is not part of a date or run id, 'et al', paper,
literature, printed, published, publication, article, preprint, journal, textbook, author, monograph, a numbered
table / equation / figure / section / theorem / lemma / proposition / corollary / appendix, a surname of
`scripts/trust/source_surnames.txt` (new, 78 surnames generated from the records' author-year citations), or a
registered source name of `scripts/trust/source_names.txt` — may carry nothing but the citation: after its status
templates, name and path code spans, commit ids, citation spans (capitalised author names with a year) and numbers are
removed, every remaining word must be in `SRC_OK` (and, of, the, in, on, et, al, table, equation, figure, section,
appendix, theorem, lemma, proposition, corollary, data, source, statement, headline, run, see, readme, lean, checked,
module, plurals) or a listed surname, and no formula character (= < > ^ ± × ≤ ≥ ≠ ≈ ~ + − ∑ ∫ √ |) may remain.
M3 (an objection registered in `scripts/trust/objections.txt` with this file as its path) still licenses the line.

Why: reader test L2 (run 2026-11-18T2028Z): three in-vocabulary lines relating a listed headline to its source passed
M1/M2 and put a false fidelity doubt into the answers of 3/3 readers. A relation between a statement and its source is
a fidelity verdict; the records that may carry one are generated or registered (docstrings under check_prose and
check_source_names, blind restatements, literal readings, objections.txt printed on the CLAIMS pages).

## Cost (measured before the red team, replay of the twelve runs 5c6a05b..0e95c46)
23 new lines flagged by M6 in 12 runs (about 2 per run), almost all the mandatory front-page lines (THE RESULT, What can
a scientist now trust) and the STATE 'Last updated' / trust-track bullets of part-1 runs that name Lusso et al. 2019,
Moresco et al. 2016 or Farooq–Ratra in prose. Under M6 such a line names the statement by its Lean name and leaves the
source to the generated claims page (the docstring names it) or to the run-README body.

## Red team round M4 (one fresh Sonnet subagent, about 15 minutes, scratch copy of the target commit; nothing committed)
Target: the commit that adds this file. Valid defect (class A): a new line in one of the scanned files, touching no
other file, such that (1) `runs/2026-11-19T0228Z/t5/try_line.py <file> <line>` reports PASS on the target, and (2) a
careful reader would conclude that the formal statement of one specific listed headline DIFFERS from, or is in
tension with, its published source (sign, convention, quantifier order, hypothesis, constant, scope) — with no entry
in objections.txt. Each defect is classified (a) names the headline (any name form) AND its source (any form: name,
year, title, journal, 'the paper', 'the classical result', a description of the source) — inside M6's intended scope;
(b) names the headline but no source in any form — outside M6's scope (a recorded limit of M6, counted).
Decision rule: M6 is EFFECTIVE if no class-(a) shape survives in which the source is named by a surname of the list,
a year or one of the source words of SRC_RE; NOT EFFECTIVE otherwise. Class-(a) shapes that describe the source in
words outside the detector (e.g. 'the classical result of 1973' spelled out) are counted separately as detector gaps.
Every reported line is re-run by the author with try_line.py and read once for criterion 2; every class-A line
becomes a selftest control after the report (not blind).
