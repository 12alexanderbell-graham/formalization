# Blind red team AF — hypothesis necessity (T2b), judged run 2026-11-11T0428Z

Red team: Sonnet, brief `briefAF.md` (commit 9be5ce1, before the red team started), snapshot 7d4c53f (read-only;
told not to read runs/2026-11-11T0028Z, the adversary report on the first draft of `check_necessity.py`). Output
`redteamAF/` committed unchanged (e0ecabc) before any judging or fix. Six defects, all new toy headlines in
`Checked.Toy` with witness modules; no existing Checked file edited.

Judge: `judge_AF.sh` (CI trust and frozen steps of `.github/workflows/lean.yml` after the author steps: relock,
Claims, FINDINGS blocks, packet), all six defects combined in one tree (worktree + copy of `.lake/build` of the full
local build of 7d4c53f). Each defect's modules were first compiled alone (scratch concatenations: all six compile).
BEFORE = scripts of 7d4c53f, `--base 7d4c53f` (`judgeAF_before.out`). AFTER = the fix of this run (commit of
`StatementDeps.lean` `necShape` + `check_necessity.py` N4 + shape baseline of the clean tree), `--base` = that commit
(`judgeAF_after.out`). The AFTER column is **not blind**: the fix was written after reading the report.

| d | weakness (generated line a reader misreads) | BEFORE (blind) | AFTER (not blind) |
|---|---|---|---|
| d01 | conjunction hidden behind a CLAIM definition in one hypothesis (`Window a b c d` = a ≤ b ∧ c ≤ d, conclusion a ≤ b): "needed 1" though c ≤ d is decorative | ACCEPTED | REJECTED (N4 `bundled 1`) |
| d02 | two disguised copies (a ≤ b, ¬ b < a), each redundant alone, false if both dropped: "redundant 1, 2" | ACCEPTED (generic caveat in the section header only) | passes; generated line now reads "redundant (each alone, not together) 1, 2" — misleading reading removed at the line |
| d03 | `let c := b; c ≤ c → a ≤ c` as conclusion: the assumption after the `let` is never numbered | ACCEPTED | REJECTED (N4 `conclusion`) |
| d04 | assumption in a subtype binder `b : {x // a ≤ x}` | caught incidentally (check_literals rule 1 reads the `1` of `b.1`; formality: `b.val` passes) — repaired: ACCEPTED | REJECTED (N4 `subtype`) |
| d05 | conclusion `Guarded a b` (CLAIM def = b ≤ a → a = b) hides an assumption | ACCEPTED | REJECTED (N4 `conclusion`) |
| d06 | conclusion repeats hypothesis 2 as a conjunct: "needed 2" only because of the echo | ACCEPTED | REJECTED (N4 `restated 2`) |

**Blind: 5/6 valid defects accepted as submitted, 6/6 with the trivial repair of d04.** All six also raised the
generated tally "headlines with every hypothesis classified" (22 → 28 of 156 in the judged tree). Every other
check (build, axioms, StatementDeps incl. non-vacuity and unused hypotheses, Claims, 33 Python checks) passed.
**After (not blind): 0/6 misleading lines accepted** (5 rejected by N4, d02's line corrected by generation).

Root cause: necessity was computed on the binders *as written* (to match CLAIMS.md's numbering), while a reader
takes "every hypothesis classified" to mean every assumption of the claim. Assumptions can sit where the numbering
does not look (behind a definition, after a `let`, in a subtype, in the conclusion) or be classified only formally
(a bundle, an echo). The fix keeps the numbering and adds a generated `shape:` entry per headline (StatementDeps
`necShape`), excludes such headlines from the fully-classified tally, and blocks new ones (N4, shrink-only baseline,
no disclosure route). On main it re-labels 26 existing headlines `bundled` (model predicates such as "x solves the
IVP" or the cubic critical-point predicate are conjunctions behind pinned definitions: necessity was shown for the
bundle, not for each part) and lowers the honest fully-classified count from 22 to 14 of 150.

Open: per-conjunct necessity for the 26 bundled headlines (a witness meeting every other conjunct, or a split of
the predicate into numbered hypotheses); joint redundancy (d02) is labelled, not proved; restated hypotheses are
detected only syntactically (a restatement up to definitional unfolding or logical equivalence passes).
