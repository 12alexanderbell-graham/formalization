# Run 2026-10-31T1028Z (scheduled)

Environment: add_repo not exposed; repo pre-cloned, fast-forwarded to 941db96; no LOCK. Local Lean via elan + `lake exe cache get` + Checked build (~12 min). Previous run's CI green. PROMPT, operative core, STATE, last CHANGELOG read.

**THE RESULT:** part 3 (measured trust) moves: the class of wrong claims that every check accepted after run 0228Z ("meaning carried by prose or names": A04, A05, B04, D04) is now rejected by a blocking mechanical check, and a fresh red team of a different model (E, Sonnet) was aimed at that check and judged. Part 1 moves with it: the plain-words layer a scientist reads is now a checked link, not free prose.

**WHAT CAN A SCIENTIST NOW TRUST WITHOUT CHECKING IT THEMSELVES?** That a headline's plain-words claim does not name a physical quantity (luminosity or angular-diameter distance, ΛCDM, CPL, redshift, curvature, critical point, …) unless its Lean statement actually contains the pinned definition of that quantity or writes out its defining law; that an existence theorem or a refutation says so; that a claim about fixed objects does not say "every"; that a certified number goes through a pinned or transcribed definition; and that the plain-words claim of any headline or pinned definition cannot be changed without a LEDGER line. Before this run all of that was the author's say-so (four seeded wrong claims of this kind passed every check).

**WEAKEST UNCHECKED STEP NOW:** paraphrase. The vocabulary rule knows 14 terms; a wrong claim worded outside the glossary (red team E: "angular-size distance", "flux distance", an equation-of-state name the glossary lacks) is not read. Also: the docstring of a *new* headline is checked only for vocabulary and shape, not for polarity or scope (E04/E06 analogues on new constants), and prose labels next to certified numbers in FINDINGS (D01) and scope prose in STATE (A03) are unchecked.

**BOTTLENECK AND WHY:** part rotation: part 3 had not moved since 0228Z (4th run). STATE's queue named exactly this: re-judge the open T5 holes and add the prose classes. Yes = the open class closes and the residue is measured; no = prose stays an unmeasured channel for wrong science. It was yes for the targeted defects.

**WHAT WE DID:**
1. `scripts/trust/StatementDeps.lean` writes `.lake/meaning.jsonl`: per headline its docstring, its logical shape after unfolding the program's own non-pinned definitions (`Meta.deltaExpand`) and one library unfolding step, the pinned definitions it reaches, the pinned predicates whose defining equation it writes out (skeleton match), the conjuncts asserting numbers that reach nothing pinned or transcribed; per reached definition its kind, docstring and reach.
2. `scripts/trust/check_prose.py` + `glossary.txt` (blocking in CI): vocabulary, names, shape and record rules (module docstring). Known gaps in `prose_baseline.txt` (32 at introduction, 25 after law matching; shrink-only, growth only with a LEDGER line naming the keys); glossary grow-only.
3. Docstrings of headlines and pinned definitions added to the frozen fingerprints (relock; LEDGER names all 128 changed entries; statements and bodies unchanged).
4. T5: judge v6 (= v5 + prose check + packet regeneration) in a second worktree; control and old defects judged; red team E (Sonnet, 8 defects aimed at the new check) written and judged; results `t5/RESULTS.md`.
5. Found in our own records by the new check: 8 records certify numbers of free formulas (F1/F2 records copy the printed formulas as `local notation`, untied to the claim definitions, the same mechanism red team E used in E07); the F(R) refutations say "ΛCDM" without reaching `IsFlatLCDM` or its law.

**RESULT:** see `t5/RESULTS.md`. No status change of any physics or chemistry headline (statements untouched).

**WHAT COULD STILL BE WRONG:** the glossary and the word lists are heuristics, measured by red teams, not proofs; skeleton matching erases which variable is which (a law written with mismatched variables would pass); the model-written docstrings of the 127 existing headlines were not re-read for paraphrased overclaims.

**NEXT:** STATE "Exact next step".
