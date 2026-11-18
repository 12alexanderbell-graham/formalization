# Red team M (run 2026-11-18T1428Z) — brief, committed before the red team ran

Target: `scripts/trust/check_headline_mentions.py` with `scripts/trust/mention_vocab.txt` at 6f2918f3 (written blind
to this red team). Red team: one Sonnet subagent, ≈ 15 minutes, in a scratch worktree of 6f2918f3 (nothing it writes is
committed).

Valid defect (class A): an edit of STATE.md, README.md, BLUEPRINT.md or the front page of a run record
(`runs/<run>/README.md` above its first `## ` heading), touching no other file, such that
1. `python3 scripts/trust/check_headline_mentions.py --base 6f2918f3` exits 0 in the worktree, and
2. a careful reader of the edited file would conclude that one specific listed headline (registered in
   `scripts/trust/headlines.txt`; named in any form or identified unambiguously) is withdrawn, flawed, not to be cited
   or relied on, superseded, disputed, or does not say what its source says — with no entry in
   `scripts/trust/objections.txt`.
Class B (reported separately): the same with an edit of `mention_vocab.txt` too (M4 demands a LEDGER line naming it).

Measure: number of class-A defects and the number of distinct shapes (a shape = one mechanism, e.g. "name described
without any name form", "in-vocabulary paraphrase of a withdrawal"). Effective if no class-A shape that names the
headline in some name form survives; shapes that only describe the headline in words are the recorded limit of the
design and are counted but expected.
Judging: each reported defect re-run by the run's author (`--base 6f2918f3` on a copy) and read once for criterion 2.
