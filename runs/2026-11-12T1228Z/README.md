# Run 2026-11-12T1228Z (scheduled)

**THE RESULT:** part 1 by rotation (parts 2/5 were moved by run 1028Z) — hypothesis necessity: 44 hypotheses of eleven headlines classified by machine-checked witnesses (chemistry acentric factors RK/SRK/PR/PR78, Farooq–Ratra transition redshift, f(R) ratios), and one recorded referee statement ("`b < v_l` is essential") shown false in Lean: every Maxwell coexistence state of a subcritical RK-form isotherm lies right of the co-volume.

**What can a scientist now trust without checking it themselves, that they could not before?** For the eight certified acentric-factor claims, which assumptions carry weight: each hypothesis of the SRK/PR/PR78 existence claims and of the RK/SRK uniqueness claims is now shown needed (a machine-checked counterexample without it) or redundant (the claim proved without it), instead of a referee's prose opinion — which was wrong for `b < v_l`.

**Weakest unchecked step:** the `b < v_l` hypothesis of the PR/PR78 uniqueness claims and `b > 0` of RK existence are still open; and the bundled critical-point/coexistence predicates are classified as wholes, not part by part.

## Start
- 12:28Z. add_repo not exposed; pre-cloned checkout detached; `git fetch --unshallow` + `git checkout -B main origin/main`. LOCK of run 1028Z alive at 12:28Z (heartbeat 12:01Z, task: FS findings) → auditor role (planning the chemistry witnesses, disjoint from its task) until it released the LOCK at 4c7b118 (≈ 12:30Z); LOCK taken 7c47c3b.
- Local Lean: elan installer accepted; `lake exe cache get`; CI artifact `checked-build` of run 43205202447 (12c6f6e, wip/fs-findings) restored by hand (unzip, Python zstandard; the script's copy of the 1.9 GB zip into `mktemp` would have run the disk out: 8.9 GB free after unpacking) → `lake build Checked` incremental ≈ 3 min.
- CI: main's runs 43218463622 (4c7b118, run 1028Z's final) and 43196172253 (0e262e6) pending/in progress at 12:35Z; this run's pushes carry `[skip ci]` until the final records commit.

## Bottleneck
- 349 → 363 open hypotheses (run 1028Z added records) in `scripts/trust/necessity_open_baseline.txt`; the chemistry acentric family (40) had a uniform route. Yes → most classified and the reader sees which of R > 0, A > 0, b > 0, T_c > 0, v_c > b, the critical-point and b < v_l conditions matter; no → the junk-integral route fails and the hypotheses need genuine Maxwell constructions.

## What we did
1. `Checked/Trust/NecessityO.lean` (35): generic lemmas — `not_ii_of_pole` (a k/((x − c) m(x)) pole is not interval integrable, from Mathlib's `not_intervalIntegrable_of_sub_inv_isBigO_punctured`), `maxwell_zero_of_pole` (two zeros of an isotherm around such a pole are a Maxwell state at pressure 0: Lean's integral is 0), `crit_RT_pos` (a genuine critical point has R T > 0 and P_c > 0, from `CubicEOS.reduced`), `big_pressure`. SRK section written by hand, PR/PR78 emitted by `scripts/gen_pr.py` (b = −1 witnesses with roots 1 ± √2 hand-written), RK by hand. Needed 31, redundant 4 (RK R > 0 and A > 0, existence and uniqueness).
2. `Checked/Trust/MaxwellRight.lean`: `maxwell_right` — for p = RT/(v − b) − a/(v² + bv), RT > 0, a, b > 0, RTb < a, every Maxwell state has v_l > b (poles → junk integral 0 → p_s = 0, but `p_ne_zero`; pole-free components: p'' < 0 on (−∞, −b) and (0, b), p'' > 0 on (−b, 0) when RTb < 16a; strict concavity/convexity contradicts equal areas). With the θ bounds of the existence modules: `srk_omega1_unique_r5`, `rk_coexistence_unique_r7`. The RK module doc's referee sentence corrected.
3. `Checked/Trust/NecessityP.lean`: FR13 transition redshift 3, 5 needed, 4 redundant (both priors); `FREta.eta_ratios` 2 redundant (confirms its referee note).
- Tally: open 363 → 319; needed 425 → 460; redundant 118 → 127 (TRUST_MAP.md, generated).
- Local: `lake build Checked` green; StatementDeps with relock; `local_frozen_step.py --trust 37b67ea` (see below); every new theorem on standard axioms (`#print axioms`).

## Not done / next
- PR/PR78 `b < v_l` (plan, worked out on paper this run): p'' = 2c/(v − b)³ − 2a(3(v + b)² + 2b²)/D³ with D = v² + 2bv − b², roots r₁ = −b(1 + √2), r₂ = b(√2 − 1). Concave on (−∞, r₁) and (r₂, b) (both terms negative). Convex on (r₁, r₂) by splitting at 0: for v ≤ 0, |D| ≤ 2b² and 3(v + b)² + 2b² ≥ 2b² give the second term ≥ a/(2b⁴) while b − v ≥ b bounds the first by 2c/b³ (needs θ = cb/a < 1/4); for 0 < v < r₂, |D| < b² and 3(v + b)² + 2b² ≥ 5b² give ≥ 10a/b⁴ against 2c/((2 − √2)b)³ < 10c/b³ (needs θ < 1). No zero left of b: c D = a(v − b) needs D < 0; on (r₁, 0] c D + a(b − v) ≥ b(a − 2cb) > 0, on (0, r₂) ≥ ab(2 − √2) − cb² > 0; junk values at r₁, r₂, b are nonzero. Poles r₁, r₂ via `not_ii_of_pole` with m(x) = x − r_other (as in `pr_junk_maxwell`). θ ≤ 0.074 from `PRExists.theta_bounds`-style lemmas (check the PR/PR78 modules for the exact name).
- RK existence `b > 0` (3): no junk route found (with b < 0 the isotherm may have genuine Maxwell states right of the junk critical point).
- vdW uniqueness 3, 4 (same questions for u = w = 0).
- FR13 1, 2 (Ω outside [0, 1] satisfying the minimiser inequality: needs the χ² outside the unit interval).
