# Run 2026-11-04T1428Z (scheduled)

Environment: add_repo not exposed; repo pre-cloned (detached HEAD, stale local `main` reset to origin/main). No LOCK (run 1228Z closed). **Local Lean available** (elan installer accepted; Mathlib cache; `lake build Checked` ≈ 20 min, trust step ≈ 3 min). Previous CI: T3 commit af31452 **41839154897 green**; 1228Z closing commit 1c9ca73 **41846160247 green**; this run's LOCK d714f04 41848308199 green. This run's later commits: STATE "Environment".

**THE RESULT:** part 3 (measured trust) moves: the third blind measurement of the pipeline, and the first check in the series measured blind on its own target class.

**WHAT CAN A SCIENTIST NOW TRUST WITHOUT CHECKING IT THEMSELVES?** The parameters each headline statement fixes, generated from the statement and shown in TRUST_MAP.md and the packet beside the docstring (so a docstring that generalises past them is visibly contradicted); that a docstring using one of the generalising words rule 6 lists ("every", "any", "whatever", "independent of", …) generalises only over data the statement binds (round I showed other wordings pass); that an unsigned number in a docstring is not the negative of the certified one; that a citation-shaped number in a new headline is a citation registered for that headline; that numbers in the module doc of a Checked file are literals of that file's headlines.

**WEAKEST UNCHECKED STEP NOW:** hand-written prose that no script reads: README.md and STATE.md (now marked as unchecked by a CI-guarded banner, but a reader can still be misled: H07), and generality expressed without a generalising word ("amplitude-independent", "isochronous").

**BOTTLENECK AND WHY:** STATE next step 2 and part rotation (part 3 due). Two blind red teams in a row passed 8/8; the open class (prose that generalises over a parameter the statement fixes, G02/E08) had no check. Yes (the rule catches a blind red team's generality defects) = prose can be checked against the statement's quantifier structure mechanically; no = the docstring must be generated from the statement.

**WHAT WE DID:**
1. Blind red team H (Sonnet; brief `t5/briefH.md`; ≥ 3 generality defects on new correct wrapper headlines) wrote against a read-only snapshot of d714f04, while a separate agent, told not to read H, implemented rule 6 from G02 alone.
2. Rule 6 of `scripts/trust/check_prose.py` (blocking): StatementDeps writes `bound`, `roles`, `fixed` per headline; every generalising phrase must name a bound variable or a registered noun (`scripts/trust/param_nouns.txt`) for a role a bound variable fills; fixed parameters are reported with their values. TRUST_MAP.md gains a generated "Fixed by the statement" column, the packet a "Parameters the statement fixes" line.
3. Judged all 8 H defects combined (`t5/judge_v10.sh`; Checked built, all compile): **before 8/8 accepted; rule 6 blind: H01–H03 rejected, H04 accepted.** After reading H: equation-fixed parameters (H04), sign rule (H05), per-headline citations `citation_owners.txt` (H08), module-doc number rule 7 (H06), guarded unchecked-prose banner in README/STATE (H07 still accepted). Final: **1/8 accepted** (`t5/RESULTS.md`).

**RESULT:** blind false acceptance on main 8/8 (third in a row); rule 6 blind on its class 3/4 rejected; after all fixes 1/8 (not blind). **Fourth blind round (red team I, same run, against all the new checks at f73ba92): 8/8 accepted** — generality written outside rule 6's word list passes; the plain-words claim has to be generated from the statement (next part-3 step). No statement, proof or frozen entry changed (LEDGER integrity event; baseline +10 rule-6 keys and +292 module-doc numbers, named).

**WHAT COULD STILL BE WRONG:** rule 6 is a grammar of generalising words, not semantics (round I beat it 6/6); the noun registry is hand-written (growth disclosed, not prevented); fixes after reading H are not a blind number; README/STATE prose remains unread by any script.

**NEXT:** STATE "Exact next step".
