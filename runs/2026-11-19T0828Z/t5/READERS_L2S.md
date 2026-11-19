# Reader test L2S — results (run 2026-11-19T0828Z; brief `reader_brief_L2S.md`, committed 834585a before the readers ran)

Material: `make_pages_s.py 834585a <dir>`: the L2 lines in STATE.md; CLAIMS_READER.md at 834585a, whose Status line now
OPENS with "**The source's own form, as a blind reader wrote it from the source without seeing this statement (each body
occurs in the statement below, `check_literals.py`):** …" (for `gelfand_extrema`: `gelfandRhs := fun s w φ => -(2 / s *
φ s) - Real.exp (w s)`, …). Readers r51, r52, r53 (Sonnet, one message, ≈ 50–56 s; answers verbatim in `answers/`).
Blind grader (Sonnet) given them mixed with r48–r50 under shuffled labels (`answers/grader3_labels.txt`).

| reader | many_centre | extrema | fs −0.03 | doubt (run) | doubt (blind grader) | mentions the printed reading |
|---|---|---|---|---|---|---|
| r51 | "Caveat: STATE.md has an unchecked bullet saying it is 'the dual …'" | "not as Joseph-Lundgren's theorem verbatim" | "Check the sign convention against the source before citing it as Ganapol's row." | **yes** | **yes** | no (quotes STATE's "read blind", calls the two in conflict) |
| r52 | — | "Mind the convention when comparing to the literature." | "not the same sign convention as the source table. Check this" | **yes** | **yes** | no |
| r53 | — | generic (borderline, no) | "a possible sign-convention mismatch with the source, and no objection is registered for it" | **yes** | **yes** | no |

Second grading of r48–r50 in this mix: 3/3 again (r48, r49, r50 yes). Citation 0/9 misled across L2R and L2S.

**Decision (registered rule): NOT EFFECTIVE** — 3/3 carry an unrejected doubt. Not one of six readers in L2R/L2S used the
printed readings, at the end or at the head of the Status line; each compared the line with the Lean statement, found
nothing to refute there (the line is about a source), and kept the doubt. Page-side evidence does not neutralise a
hand-written line relating a statement to a named source: across L2, L2R, L2S 9/9 readers carried such a doubt; across N
0/3. The guard against the class is keeping such lines off the reader's material: M6. The printed readings stay on the
page as evidence for a reader who looks for the source's form (nothing weakened; citation unmoved), recorded as not
effective against this class.

Next (part 3): close M6's two open limits by construction, not by more words — (i) names outside the surname list: make
`source_surnames.txt` the closure of every source a record can cite (`citations.txt`, `literal_readings.txt` source=
names, the briefs of the blind readers) and fail CI when a cited author is missing; (ii) generic descriptions ("of the
table", "the classical theorem"): a definite reference to a document in an about-line is a source mention (red team
first, then cost on the replayed runs).
