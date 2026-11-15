# Run 2026-11-15T1228Z (scheduled)

**THE RESULT:** parts 2/5 (new certified science, new field coverage) — every turning point of the radial Gelfand branch in the three-dimensional ball is now one Checked headline (`Checked.Math.GelfandExtrema.gelfand_extrema`), derived from two existing Checked headlines and a Lyapunov function with no new certificates; frozen, proved, blind restatement closed, referee STANDS, promoted with a blind literal reading, NV and fully classified hypotheses.

**What can a scientist now trust without checking it themselves, that they could not before?** That the radial solution branch λ(s) = s² e^{w(s)} of Δu + λe^u = 0 in the unit ball of ℝ³ has exactly the turning points of one infinite sequence ζ(0) < ζ(1) < … → ∞: λ strictly increasing up to ζ(0) (λ* in [3.321992118, 3.321992119]), strictly monotone between consecutive turning points, maxima strictly above 2 and decreasing, minima strictly below 2 and increasing, λ → 2 — for every solution satisfying the stated equation and initial conditions, not only the first turning point (`gelfand_ball_critical`) as before.

**Measure:** certified turning points of the Gelfand branch: 1 → all (Checked; PROVED once CI is green on every job). Necessity: needed 636 → 639, redundant 163 → 164 (293 headlines, NV 176/176).

**Weakest unchecked step:** CI has not yet judged this run's promotion (nor 0a52be0's `bonnor_ebert_extrema_monotone`). Prior art was not read (the referee's web search was denied): the classical qualitative statement (Joseph–Lundgren 1973) is quoted from memory, UNVERIFIED.

## Start
- 12:28Z. add_repo not exposed; pre-cloned checkout detached at 0a52be0 (= origin/main) with a stale local `main`; `git checkout -B main origin/main`, `git fetch --unshallow origin`. No LOCK → taken (06d8b5d).
- Local Lean: elan (authorized), `lake exe cache get`; `checked-build` of 43691560009 (813805f) restored (first download reset by peer; second URL to the scratchpad, `DELETE_ZIP=1`); `lake build Checked` ≈ 5 min.
- CI at start: 43691560009 (813805f) green on every job; 43701382621 (ece084b) cancelled (superseded); 43709741164 (0a52be0) checked job in its Lean step, nanoda shard 2 running.

## Bottleneck (and what a yes/no changes)
- Rotation: parts 2/5 (STATE 1c: Gelfand turning points λ = uv, zeros of v − 2). STATE planned new certified chains reporting the sign of v − 2 between new brackets (several runs, as for Bonnor–Ebert). Question: do the proved Bonnor–Ebert extrema plus a Lyapunov function already force the whole zero structure of v − 2? Yes → every turning point at once, no certificates; no → the chain route.

## What we did
1. Float study (turning points 4.07, 37.5, 429, 4532, 48976, 525617; λ 3.32, 1.66, 2.11, 1.97, 2.01, 2.00). Freeze `Work/Math/GelfandExtrema.lean` (ffe23e2): the conclusion of `bonnor_ebert_extrema_monotone` transferred to λ, plus the λ* window.
2. In ONE message: blind restater (Sonnet), referee (Opus), proof fork. The fork proved the freeze in ≈ 20 min (`Work/Math/GelfandExtremaMain.lean`, 825 lines; 73f3a29). Referee: statement STANDS; route STANDS-WITH-CORRECTIONS (claimed gap at the equilibrium; it is closed by the Volterra argument the proof uses — note in `referee/REPORT.md`); two independent computations of the first six turning points agree.
3. Blind restatement (C² via `ContDiffOn`, the equation with `deriv (deriv w)`) committed verbatim (638f124), closed in `Work/Math/GelfandExtremaBlindClosed.lean` (b633516).
4. Blind literal reader for the singular value (brief 2926b62 → reading 4dde586: `gelfandSingularLambda := 2`, from u = −2 log r). A second reader for the limit conjunct (brief e872ac8 → reading 3c6596e8: `gelfandBranchLimit`, `Tendsto … (𝓝 2)`): check_literal_targets T2 counts a closed reading only at a registered slot, and `𝓝 2` is none — found by `records_check.py` before pushing.
5. Promotion by `scripts/promote_gelfand_extrema.py` (no `import Mathlib` needed: the Checked imports suffice), NV, `Checked/Trust/NecessityAO.lean` (1, 3, 4 NEEDED; 2 REDUNDANT), relock, TRUST_MAP, CLAIMS, packet; headline docstring without "three-dimensional" (check_claim_vocab V10); prose_vocab `ball`, `turning`, `branch`.

## Next
- STATE 1d: CI read (0a52be0 → `bonnor_ebert_extrema_monotone`; this run's push → `gelfand_extrema`); then part 1 by rotation.
