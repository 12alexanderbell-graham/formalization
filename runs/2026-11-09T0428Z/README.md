# Run 2026-11-09T0428Z (scheduled)

**THE RESULT:** parts 2 and 5 — the classical Falkner–Skan theorem "for every 0 < β ≤ 1, every solution of the boundary-value problem has f'' > 0" is now a **registered headline** (its β-form equation read blind for general β), and the **β = 1/10 row is in Checked** (ten-decimal window 0.5870352191 < f''(0) < 0.5870352193, equality, existence; with and without the class −1 ≤ f' ≤ 1). Promoted to Checked + AUDITED; PROVED once a main CI run is green on every job.

**What can a scientist now trust without checking it themselves, that they could not before?** That for every pressure-gradient parameter 0 < β ≤ 1 (accelerating wedge flows up to the plane stagnation point) every solution of the Falkner–Skan boundary-value problem has positive wall-normal shear gradient f'' everywhere — stated for general β, the equation read blind from the wedge-flow similarity variables — and that the β = 0.1 table value is 0.587035219(2) to ten decimals for every solution, unique, existing.

**Measure:** headlines 218 → 224 (CLAIMS.md), NV 145 → 150; blind restatement 2/2 closed (no-bound β = 1/10 pair); blind literal reading of the general-β right-hand side (β = 2m/(m+1), sympy residual 0).

**Weakest unchecked step:** for these headlines, the fidelity of the transcribed equation rests on blind readings (now including the general-β form); outside them, β < 0 is not covered, and there the research note shows that uniqueness in the class 0 ≤ f' ≤ 1 is **false** (a continuum of slowly decaying solutions at β = −0.1, re-checked here by an independent integration) — any β < 0 statement must carry a decay condition.

## Start
- 04:28Z. add_repo not exposed; pre-cloned checkout detached with a stale diverged local main; `git checkout -B main origin/main` (local branch only) = 0c7da92. No LOCK; taken in 64f429d.
- Environment: repo reachable (push); local Lean: elan + toolchain v4.35.0 + Mathlib cache ≈ 3 min; full `lake build Checked` 04:31–05:57Z.
- CI read: 0c7da92 (42560201836; run 0228Z's final records, contains a98a677) **green**.

## Bottleneck
STATE exact next step 2 (a), (b) (parts 2/5; rotation after 0228Z's part 3): the β = 1/10 row was proved in Work but not in Checked, and the general-β monotonicity theorem — the classical result the eight `_limit_` headlines rest on — was not a headline for want of a blind reading. A yes puts the row and the general theorem in the strict library; a no would show a fidelity gap in the β-form equation.

## Work
1. Promotion script `scripts/promote_fst.py` (copy of `promote_fsf.py`, 5 → 10; module docs number-free): `Checked/FSTenth/` (14 modules), `Checked/FalknerSkan/TenthBounded.lean`; new `Checked/FalknerSkan/LimitTenth.lean` (no-bound pair).
2. Brief e44788a (committed alone) → blind reader (Sonnet) and blind restater (Sonnet, words only) in ONE message → b7ad60e (reading + restatement committed before any copy). Reader: β = 2m/(m+1), A = 1, C = 2; sympy residual of the boundary-layer momentum equation 0 for general m; 0 < β ≤ 1 iff 0 < m ≤ 1 (flat plate, Hiemenz at the ends). Copy `Checked/Trust/SecondReadingFSBeta.lean`; the run-2028Z β = 1/10 reading copied to `Checked/Trust/SecondReadingFSTenth.lean`.
3. Blind restatement closed in `Work/FalknerSkan/FTLBlindClosed.lean` (statements byte-identical to the restater's; axioms standard).
4. Registries: six headlines, six literal-reading lines, six NV witnesses (β = 1/2 solution for the general theorem); prose_vocab `tenth`, `pressure`, `gradient` (V13/V1, LEDGER); check_formulas needed the readers' bare names in the LEDGER (second line).
5. Research subagent (Opus, during the build) on β < 0: `research/fs_negative_beta.md`. Main-session check `research/check_continuum.py` (scipy, rtol 1e-11): f''(0) = 0.1, 0.2, 0.3 all give 0 ≤ f' < 1, f'' > 0, f' creeping to 1 (1 − f' ratio 0.86 between η = 100 and 200 at f''(0) = 0.2, i.e. ~η^(−0.2)); f''(0) = 0.3192697598 decays fast; 0.35 overshoots. Classical uniqueness for β < 0 therefore needs a decay condition.

## Audit
- β = 1/10 trio: audited in run 2028Z (frozen 1ebeba5, referee STANDS, blind restatement closed, blind literal reading). Promotion byte-identical to Work apart from names, imports and module docs.
- No-bound pair: statements = the trio's with `hb` removed (as the fifth pair, referee §1 of run 0028Z); blind restatement closed.
- General-β theorem: blind restatement closed in run 0028Z (`UBlindClosed.positivity`); β-form literal now read blind.

## Local checks
Full `lake build Checked` green incl. Witnesses; StatementDeps with relock (224 headlines, NV 150/150); Claims (224) + check_claims; every Python trust check, and every `--base 0c7da92` check; `make_packet --check`; goal guard; check_status_lines.

## CI
- 0c7da92 (42560201836): green. f3c1e10 (42565402396, heartbeat + research note): green. 64f429d, e44788a, b7ad60e: cancelled by coalescing.
- Promotion ed98bf4 + 1df8963 (42571761542) and the records commit: read next run.

## Commits
64f429d LOCK + stub · e44788a brief · b7ad60e reading + blind restatement · f3c1e10 heartbeat + research note · ed98bf4 promotion · 1df8963 LEDGER disclosure · records (LOCK removed).
