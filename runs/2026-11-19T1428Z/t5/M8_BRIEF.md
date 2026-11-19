# Rule M8 and red teams M5 and M6r (run 2026-11-19T1428Z, part 3) — pre-registered, committed before either red team ran

## The rule (written blind to any red team of it; `scripts/trust/check_headline_mentions.py`, `m8_names`, `m8_vocab_names`)
Open limit of M6 (red team M4, reader test LN): a source pointed at without a name, year, source word or numbered part
("of the table", "the classical theorem"). M1 confines a new line about a listed headline to the closed vocabulary
`scripts/trust/mention_vocab.txt` (1,626 words). So the ways to point at a document there are vocabulary words, and
they can be listed. Read off the whole vocabulary by hand:
- **M8a (document words):** article, arxiv, author(s), documentation, footnote, page, paper, paragraph, table,
  tabulated, tabulation, tbl, text, title, typeset, wikipedia, source; the authors as pronouns (they, them, their,
  themselves, who, whose); software a statement is compared with (Cantera, DWSIM, pychemqt); a journal (PRD); and
  'the theorem / lemma / proposition / corollary' not followed by a code span. A new about-line with one of them
  names a source for M6 (it may then carry only the citation).
- **M8b (names in the vocabulary):** eleven personal or place names of the vocabulary that cite a source and were
  missing from `scripts/trust/source_surnames.txt` were added (Bari, Cheng, Daubert, Gidas, Graboski, Johnston, Kamke,
  Ni, Nirenberg, Pitzer, Zhu; found by a scan of the records for vocabulary words written capitalised inside a
  sentence). From now on a word that enters the vocabulary and is written as a name in the records fails M4 unless it
  is a listed surname, a document word, or one of the hand-classified eponyms `M8_EPONYMS` (Gibbs energy, Crocco
  variables, Lean, Sonnet, …).
- Binds from its commit (lines that existed before are not re-read by M8).

Controls (selftest, not blind — written by the author before the red teams): four lines that passed M1–M7 at 73af250a
("the Gidas Nirenberg theorem", "their table", "the tabulated wall shear", "the dual of the theorem") are flagged; a
bare pointer "(table)" and "the theorem `gelfand_extrema`" pass.

## Red team M5 (held-out test of M8; one fresh Sonnet subagent, about 15 minutes)
Target: commit 73af250a (M1–M7, no M8), scratch worktree; the red team is not shown M8 or this file.
Task: lines in a scanned file such that (1) `runs/2026-11-19T0228Z/t5/try_line.py <file> <line>` PASSES at 73af250a
and (2) a careful reader would conclude that the formal statement of one specific listed headline differs from, or is
in tension with, its published source — the source pointed at in any way EXCEPT by an author name, a year, a 'paper /
printed / published / et al.' word or a numbered table/equation (those are M6's, already closed).
Measure: the share of its class-A lines (criterion 2 read once by the author) that M8 flags.
**Decision rule: M8 is EFFECTIVE on held-out lines if it flags at least 80 % of M5's class-A lines; PARTIAL at
50–79 %; NOT EFFECTIVE below 50 %.** Every M5 line becomes a control after the measurement (not blind).

## Red team M6r (adversarial test of M8; one fresh Sonnet subagent, about 15 minutes)
Target: the commit that adds this file (M1–M8), scratch worktree; the red team gets this file's rule section.
Valid defect (class A): same criteria (1) at the target and (2), source pointed at in any form.
Classified (a) the line holds an M8a word or an M8b name in a form M8 should read (detector gap) or (b) the source is
pointed at in words that are not document words (e.g. 'the older result', 'the usual form'): a recorded limit of the
listing approach, counted.
**Decision rule: M8 survives if M6r finds no class-(a) shape; each class-(a) shape is closed after the report (not
blind) and counted; class-(b) shapes are counted and become the next measured limit.**

## Cost (measured after this commit, before the red-team reports were read)
Replay of the run-final commits of 2026-11-18 and 2026-11-19 (each against its predecessor): new lines flagged by M8
that M1–M7 passed.
