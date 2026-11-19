# Reader test L2S: the blind readings of the source at the head of the Status line (run 2026-11-19T0828Z) — committed before any reader runs

Question: in test L2R (`READERS_L2R.md`) the blind readings of the source, printed at the END of each generated Status
line, were seen by no reader and 3/3 kept the doubt of a source-naming line. Every reader quotes the head of the Status
line ("proved in module …"). `scripts/trust/Claims.lean` now opens the Status line of every headline with registered
readings with "**The source's own form, as a blind reader wrote it from the source without seeing this statement (each
body occurs in the statement below, `check_literals.py`):** <reader def> := <body>; …", then the kernel status. Does the
doubt go when the source's form is where readers look?

Material, readers, prompt, key, grading: as in `reader_brief_L2R.md` (arm L2 lines; `make_pages_s.py <commit> <dir>`
builds r51, r52, r53 from the commit that adds this brief); the blind grader gets these three answers mixed with r48–r50
under shuffled labels.

Decision rule: **effective** if at most one of r51–r53 carries an unrejected doubt → the readings at the head of the
Status line are the measured fix for the source-relation class (next: make them complete — headlines with no registered
reading, quantifier structure). Two or three → placement on the page does not neutralise source-naming lines; M6 stays
the only guard and part 3 turns to closing M6's open limits structurally.
