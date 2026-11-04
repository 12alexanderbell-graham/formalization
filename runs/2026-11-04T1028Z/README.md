# Run 2026-11-04T1028Z (scheduled)

Environment: add_repo not exposed; repo pre-cloned (stale local `main` reset to origin/main). No LOCK (run 0828Z closed). **Local Lean available** (elan installer accepted; Mathlib cache). Previous CI: Michaelis–Menten promotion **41813186514 green on main**, so `mm_half_conversion` and `mm_solution_exists` are **PROVED**; branch `wip/prose-numbers` 41809849356 green (its report: 81 docstring numbers). This run: STATE "Environment".

**THE RESULT:** part 3 (measured trust) moves: the second blind measurement of the whole pipeline, and five checks that close what it found.

**WHAT CAN A SCIENTIST NOW TRUST WITHOUT CHECKING IT THEMSELVES?** That every docstring of a Checked declaration they read (pin theorems and lemmas included, not only headlines) is the one that was audited, or a LEDGER line names the change; that numbers in headline docstrings, units included, are literals of the statement or registered citations; that every TRUSTED_DEFINITIONS.md line was either there before or is disclosed; and that the 418 audit theorems the records call closed are still sorry-free.

**WEAKEST UNCHECKED STEP NOW:** prose that generalises over a parameter the statement fixes (G02: "the bracket holds for every amplitude" on a theorem about x(0) = 1). No check reads which parameters a sentence quantifies over. Next: STATE.md numbers (F03).

**BOTTLENECK AND WHY:** STATE next step 3 and part rotation (part 3 due). The number rule existed only as a report; the pipeline's false-acceptance rate had one blind measurement (8/8, F). Yes (G mostly caught) = the reader-facing layer is converging; no = every new artefact type opens a new unread layer, and the fix must be structural.

**WHAT WE DID:**
1. Merged the number rule, read its first CI report (81 items, 54 of them equation numbers), exempted citations, recorded negated literals with their sign (`StatementDeps.statementNums`), baselined the 16 old derived numbers per number, made it blocking (ad62b38, CI 41817469631 green).
2. Blind red team G (Sonnet; brief `t5/briefG.md`; ≥ 3 defects on the new simulations) against ad62b38: judged with judge v8 (CI-equivalent, Checked and Work built) before any fix: **8/8 accepted** (`t5/RESULTS.md`).
3. Five strengthenings (7d4553b; LEDGER integrity event): units glued to numbers read (G01); citation registry `scripts/trust/citations.txt`, shared with `check_numbers.py` (G08); every Checked docstring frozen, +546 `doc:` entries, none changed (G05, G06); `check_trusted_defs.py --base` (G04, G07); `scripts/trust/AuditClosed.lean` in the CI work job with `audits.txt` (418 closed audit theorems) and `check_audits.py` (G03). Tested on the defects: after = **1/8 accepted** (G02).

**RESULT:** blind false acceptance 8/8 at ad62b38 (second blind 8/8 in a row); 1/8 after the fixes (not blind). Michaelis–Menten headlines PROVED.

**WHAT COULD STILL BE WRONG:** the after-number is measured on the defects the fixes were designed from; only red team H will say whether the layer is closed. Freezing is disclosure, not prevention. A registered citation can still sit next to a false sentence.

**NEXT:** STATE "Exact next step" (part 2 is due).
