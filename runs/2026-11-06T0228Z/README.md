# Run 2026-11-06T0228Z (scheduled)

**THE RESULT:** part 3 (the trust system measured and hardened) by rotation: judge blind red team M (six defects aimed at the open limits of round L: forged reader files, narrowed claim hypotheses, source coefficients entered as statement literals, model names in prose) against the checks on main, and close what it accepts.

**What can a scientist now trust without checking it themselves, that they could not before?** That a numeric literal in a headline statement — a correlation coefficient, a "printed" formula, a reduced temperature — is either the certified target of the conclusion, a pinned slot, a value read a second time by a blind reader from a source, or listed as unread in `scripts/trust/literal_baseline.txt`; and that a model or source name in a headline's prose (Soave, Peng–Robinson, "printed", "Eq. (n)") is backed by what the statement reaches. The κ(ω) coefficients of the PR 1976, PR 1978 and SRK ω = 1 results are now read twice (blind reader, `Checked/Trust/SecondReadingKappa.lean`).

**Measure:** blind round M, six valid defects: checks on main accepted **6/6**; the four new checks, written blind to M, accept **0/6** (4/6 rejected on the merits; RESULTS.md).

**Weakest unchecked step:** whether a reader was blind (a forged reading with its own brief committed first in the same folder passes), and paraphrases that drop a restricting hypothesis (round M d06, caught only incidentally).


## Start
- 02:27Z: no LOCK; pre-cloned checkout detached; `git checkout main` + pull = origin/main 8971901 (CI 42145695264 green: SRK promotion PROVED).
- 02:28Z: **elan installer worked this run** (local Lean 4.35.0); `lake exe cache get` running.
- 03:25Z: build done (≈ 37 min). Judge `t5/judge_M.sh` in worktree ../fz2: before 6/6 accepted, after (blind) 0/6 (`t5/RESULTS.md`).

## Work
1. Check writer (Opus subagent, blind to M; `t5/brief_checks.md`, `t5/new_checks.md`): four new blocking scripts (LEDGER).
2. Blind literal reader (Sonnet; `kappa_reader/`): brief committed alone (5fd0bce), reading alone (46fe1de), then the Checked copy and registration — the first genuine use of the new route.
3. Judge of round M (`t5/RESULTS.md`), fixes after reading it (check_blind_route brief directory; check_literals parsing and partial shrink).
4. Main tree after the changes: StatementDeps (relock: four new `doc:`/`moduledoc:` entries of the reading module only), Claims.lean, packet unchanged; every check and `--base` check green locally (169/169 headlines on pinned definitions, NV 110/110).

## End
- Pushed; CI of the pushes: read next run (STATE "Exact next step" 1).
