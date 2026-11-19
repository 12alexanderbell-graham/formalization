# Reader test L2R: the L2 lines against a claims page that prints the blind readings of the source (run 2026-11-19T0828Z) — committed before any reader runs

Question: test LN (this run, `READERS_LN.md`) found that a line relating a statement to a NAMED source left an unrejected
fidelity doubt in 3/3 readers and the same relation with no source in 0/3: readers refuted what they could test against
the generated statement and kept what needed the source. A word rule (M6) only keeps such lines off four files and is
beaten by generic descriptions ("the table") and names outside its list. Structural alternative built this run:
`scripts/trust/Claims.lean` now prints, in each headline's generated Status line, every registered blind literal reading
of the source as the reader wrote it (`<reader def> := <body>`; each body occurs in the statement, `check_literals.py`).
If the source's own form is on the page, a source-naming relation line becomes testable, like an N line.

Material: `make_pages.py` arm L2 (same three lines, same placement, same two dropped bullets), built by
`make_pages_r.py <commit> <dir>` from STATE.md and CLAIMS_READER.md at the commit that adds this brief (CLAIMS_READER.md
regenerated with the readings). Readers r48, r49, r50 (Sonnet, each alone, not told anything was altered, launched in one
message). Prompt: as in `reader_brief_LN.md`.

Key: the fidelity key of `reader_brief_LN.md`, unchanged (unrejected doubt per headline; a reader carries a doubt if one of
its three headlines does); citation key recorded. Grading by the run, then by a blind grader given these three answers
mixed with three of test LN's L2 answers (r40, r44, r45) under shuffled labels; the blind grader's decides.

Decision rule: **effective** if at most one of r48–r50 carries an unrejected doubt (LN's L2: 3/3) → the reader page's
readings are the measured fix for the source-relation class, and the next step is to make the readings complete
(headlines with no registered reading, and readings of quantifier structure). Two or three → printing the readings does
not neutralise source-naming lines; M6 stays the only guard and its recorded limits stay open.
Per-headline note (not deciding): `gelfand_pde_radial_many_centre`'s line is about quantifier order, which literal
readings do not show; the expected effect is on `gelfand_extrema` and `fs_neg_reversed_wall_shear_3_exists`.
