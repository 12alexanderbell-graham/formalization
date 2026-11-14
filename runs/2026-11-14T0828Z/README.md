# Run 2026-11-14T0828Z (scheduled)

**THE RESULT:** part 1 by rotation (part 3 moved at 0628Z, parts 2/5 at 0428Z, part 1 last at 0228Z) — the smoothness hypothesis of the eleven past-only printed-coefficient cosmography headlines and of `lookback_second_order_bigO` is NEEDED (`Checked/Trust/NecessityAD.lean`): and both derivative hypotheses of the `decel` pin `Fidelity.decelSpec_pins`: hypotheses NEEDED 582 → 596, open 235 → 221, headlines with every hypothesis classified 65 → 78 of 166.

**What can a scientist now trust without checking it themselves, that they could not before?** That in twelve more theorems every assumption carries weight: for the eleven past-only "printed coefficient fails" statements and the O(z³) lookback series, a machine-checked counterexample shows the smoothness assumption cannot be dropped (without it a scale factor with one derivative too few makes the printed formula pass, through Lean's junk derivative), so these statements are fully classified.

**Weakest unchecked step:** 221 hypotheses are still neither shown needed nor redundant (among them hypothesis 1 of the six two-sided companions, which needs an oscillating witness); the final push c3ca8a4's CI run (queued at the end of the run).

## Start
- 08:28Z. add_repo not exposed; pre-cloned checkout detached with a stale local main (3 unpushed commits of run 2026-11-09T2228Z, kept on local branch only); `git fetch --unshallow origin && git checkout -B main origin/main` = aaa5d26. No LOCK → taken.
- 08:30–08:45Z. Local Lean: elan + Mathlib cache ≈ 2 min; `checked-build` of 43551580603 (0935097) restored (the restore script hit the disk allowance on its first try because the zip was kept twice; second try with the URL streamed directly: lib complete, `ir` complete but for the top-level `Checked.ilean`).
- CI at start: 43563791919 (96643b0, `bonnor_ebert_min`) in progress (checked job from 07:05Z); 43572789731 (cb49239, run 0628Z's final) pending.
- Bottleneck chosen (part 1 by rotation): the 18 cosmography headlines whose only open hypothesis is smoothness (hypothesis 1, `ContDiffAt`). A yes (needed) closes them; the past-only ones (11) fall to a kinked scale factor whose past branch is a polynomial: Lean's junk top derivative at the kink is 0, and the polynomial's own top coefficient can be chosen so that the correct series at that value equals the printed one at 0. The two-sided ones (6 + `lookback_second_order_bigO`) need a non-smooth scale factor with a full Taylor expansion (oscillating term): not attempted.
- 08:52Z. Scratch `runs/2026-11-14T0828Z/lean/NecessityAD.lean`: all 11 witnesses compile (`lake env lean`).
- 08:56Z. Promoted to `Checked/Trust/NecessityAD.lean` (module doc, `ring_nf` where `ring` only normalised); added `lookback_second_order_bigO_h1` (two-sided, `O(z³)`: its only other hypotheses are `a(t₀) ≠ 0` and `ȧ(t₀) ≠ 0`, so `NCD.kink 0 = 1 + t + t|t|` works there); `necessity_open_baseline.txt` −12 lines; `lake build Checked` green.
- 09:08Z. StatementDeps relock exit 0: needed 582 → 594, redundant 155, open 235 → 223, fully classified 65 → 77 of 166; NV 170/170 (first push 4a73412).
- `scripts/restore_checked_build.sh`: streams the tarball out of the zip and reads a local zip in place (LEDGER experiment; tested on a synthetic artifact).

## Work
- Witness family: `G α β γ ε δ n = α + βx + γx² + εx³ + δ xⁿ⁺¹|x|` (derivative again of that form, `G_deriv_succ`; at n = 0 a polynomial plus a multiple of |x|, whose Lean derivative at 0 is the junk 0, `junk`), past branch `PQ` (quintic). Constants (a(0) = 1, H₀ = 1): D4 lookback b = −1/2, c = 21/8 (l₀ of the branch −315); D2y c = −11/3 (j₀ 22); Q2 c = −1/24 (j₀ 1/4); D3y K = 1, c = −1/3 (s₀ 8); D4y, DA4, DL4z, DA4z K = 1, c = −1/120 (l₀ 1); DA3 K = 1, b = −1/2, c = 1/4 (s₀ −6); demDL4 b = −1/2, c = −7/4 (l₀ 210); demDA4 d = 1/6, c = 137/60 (l₀ −274). One arithmetic sign slip (Q2) caught by Lean on the first compile.
- Not attempted: the two-sided companions (STATE 0p (a) gives the route: oscillating ε = o(t⁵) plus a series theorem stated from the Taylor remainder).

## Lessons
- Junk derivatives are a witness tool, not only a hazard: when a hypothesis is smoothness and the conclusion denies a formula written in derivative-defined coefficients, a kink at the top order sets that coefficient to Lean's 0 while a one-sided polynomial branch keeps the true expansion; one-sided (past) statements fall at once.
- Disk: the Mathlib cache (7.3 GB) plus the restored build (14.6 GB) leave little room; never keep the artifact zip beside the restore (fixed in the script).

## Local checks (before the final push)
- `lake build Checked` green; StatementDeps relock exit 0 (NV 170/170); Claims exit 0 (CLAIMS.md, PHRASE_LINES.md unchanged); `records_check.py` vs 0935097: 41/41 (one first failure: a STATE citation of a non-headline lemma name, reworded).
- CI read at the end: 43563791919 (96643b0) still in its checked job; nothing new to read. This push replaces the pending 43572789731 (cb49239), whose content it contains.
- 09:21Z. Also `Fidelity.decelSpec_pins` 2 and 3 NEEDED (scratch `lean/DecelPin.lean`, `DecelPin3.lean`, merged into `Checked/Trust/NecessityAD.lean`): `decelDiff` (decel where a is differentiable at t, decel + 1 elsewhere) and `decelDiff2` (the same with ȧ) meet `DecelSpec` — each clause either gives the derivatives or assumes ȧ ≠ 0, which makes a differentiable; for `decelDiff2` the invariance clauses need differentiability of ȧ to be invariant under c·, translation and reflection (`dmul_iff`, `dadd_iff`, `dneg_iff`) — and they differ from `decel` at `1 + |s|` (hypothesis 2 dropped, a' = 1) and at `1 + s + s|s|` (hypothesis 3 dropped). The pin is now fully classified: it pins `decel` exactly on twice-differentiable scale factors. Second relock 09:32Z: needed 596, open 221, fully classified 78/166.

## CI read at the end
- 10:07Z: 43563791919 (96643b0) green on every job — checked job (build 07:08–09:42Z, trust step, frozen registry, author files, build artifact) and nanoda 4/4 → **`Checked.Math.BonnorEbertMin.bonnor_ebert_min` PROVED** (frozen, AUDITED, referee STANDS in run 0428Z). Alexander told (L.2: major result). This run's final push c3ca8a4 has its own run queued; the next run reads it.
