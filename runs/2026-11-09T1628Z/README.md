# Run 2026-11-09T1628Z (scheduled)

**THE RESULT:** parts 2 and 5 — the Falkner–Skan β = −1/10 **reversed-flow solution (−0.1405462131 < f''(0) < −0.1405462129), the two solutions in the decay class, and the ten-decimal wall shear of the attached solution (0.3192697598 < f''(0) < 0.3192697599) promoted to Checked**: four new headlines (228 → 232), NV 154/154, and the positivity hypothesis f'' > 0 of the β < 0 uniqueness and largest-shear theorems is now **machine-shown needed** (needed hypotheses 158 → 161). Promoted entirely through CI (the environment refused the local Lean installer); PROVED once a main run is green on every job.

**What can a scientist now trust without checking it themselves, that they could not before?** That at β = −1/10 the Falkner–Skan problem has, in the strict checked layer and with every literal read blind, a reversed-flow solution approaching the edge faster than every exponential with f''(0) = −0.14054621… (ten decimals), that the attached solution's wall shear is 0.31926975… (ten decimals) and bounds every solution with f'' > 0, and that dropping f'' > 0 from the β < 0 uniqueness theorem makes it false (kernel-checked counterexample).

**Measure:** headlines 228 → 232; NV 152 → 154 (154/154); hypotheses shown NEEDED 158 → 161 (`fs_neg_decay_equal` 8 and 16, `fs_neg_decay_max_shear` 8); every Python trust check (incl. `--base 8c80eb9`) green locally on the CI author files; Checked build green twice in CI (42655917163, 42656137172).

**Weakest unchecked step:** the main run of c143ec5 must be green on every job (checked job and the nanoda shards on the 12 new modules) before the four headlines are PROVED; the window ends are certified targets, not compared with a printed attached-branch value (none found).

## Start
- 16:28Z. add_repo not exposed; pre-cloned shallow checkout detached at 8c80eb9 with a stale diverged local main; `git fetch --unshallow`, `git checkout main && git reset --hard origin/main` = 8c80eb9 (local branch only). No LOCK; taken f86992b, heartbeat c7e1ad9 (17:13Z).
- Environment: repo reachable (push). **Local Lean: the environment refused the elan installer** (permission denied by the session's action classifier); per PROMPT instruction 4 no workaround — Lean judged by CI (PROMPT note "No local Lean? Promote through CI"). Python checks local.
- CI at start: 8c80eb9 (42649787950) in progress (run 1428Z's records).

## Bottleneck
STATE exact next step 2 (parts 2/5 by rotation): run 1228Z's four β = −1/10 theorems were PROVED in Work only. Yes: they enter Checked with every trust check; no: a literal or a word no blind route carries.

## Work
1. Literal audit before promoting: β (`fsnWedgeRhs`), the decay condition (`fsnDefectBelow`), the bounded class (`stagSpeedBounded`), the wall value (`fsnWallValue`), half-line/wall/edge readings — all existing blind readings; the four decimal window ends are one-number certified targets of the conclusions (check_literals a2, check_literal_targets T1), i.e. what the proofs certify, not source data, so no new reading was needed (STATE had planned one).
2. Promotion by `scripts/promote_fsneg_tenth.py` (run 1028Z's copy rules imported): `Checked/FSNeg/{NWinLo,NWinHi,NWindow,LCell,LInv,LUnclamp,LAssemble,LOver,LSlow,LTube}`, `Checked/FalknerSkan/{NegWindow,NegReversed}`; docstrings in the claim's words (`scripts/fix_docs.py`); NV witnesses (2); necessity witnesses (3: the reversed-flow solution is the counterexample to dropping f'' > 0); Work `NAssemble` module doc fixed (referee defect 1 of run 1228Z: the scaling is f(η) = √10 F(η/√10); also the sign of the scaled equation).
3. Branch `wip/fsneg-tenth-promo`: 144c814 → CI 42655917163 (build 16:35–17:16Z green; trust step failed as expected on stale registries and on two STATE citations of helpers that are now Checked constants), 34b4d9d (necessity witnesses) → CI 42656137172 (build green, author files 18:13Z).
4. From the author files: CLAIMS.md, TRUST_MAP.md, relocked frozen.txt, packet, meaning.jsonl copied in; local checks found V13 (`lt`, and `reversed` from the module name on both NegReversed headlines) → prose_vocab `reversed`, `lt` (LEDGER) and one shrink of claim_vocab_baseline (a baselined `lt` no longer fires); STATE cites the helpers by file path. Every Python trust check and `--base 8c80eb9` green, packet current, goal guard green.
5. Merge c143ec5 pushed 18:18Z (remote head confirmed).
6. CI convenience (39.5, LEDGER): author-files tarball also carries `.lake/phrases.jsonl` (check_claims could not run locally).

## CI
- Branch runs above (build green twice). Main: c143ec5 queued/running at 18:18Z — read next run.

## Lessons
- A promotion without local Lean takes two CI rounds of ≈ 50 min; everything must go into the first push (a second push queued behind the running checked job), and the two failures this run hit (STATE citing helpers that become Checked constants; module names contributing name words) are checkable before the first push (PROMPT working note).
- Window ends are certified targets: a blind reading is needed for the data a statement assumes, not for the numbers it proves.
