# Run 2026-11-19T1228Z

**THE RESULT:** part 1 by rotation (STATE 1y → part 1 as in section Next of `runs/2026-11-19T0628Z/README.md`). Five hypotheses of listed statements are shown REDUNDANT by Lean theorems (section What we did).

**What can a scientist now trust without checking it themselves, that they could not before?** For five more hypotheses, a Lean theorem that the statement holds without each of them (section What we did).

**Weakest unchecked step:** the hypotheses still listed open in `TRUST_MAP.md` (section Next).

## Start
- 12:28Z. Local main was a stale divergent clone; `git checkout -B main origin/main` at 68c077a. No LOCK → taken (8d51af7).
- Local Lean: elan + `lake exe cache get` ≈ 3 min; `checked-build` of 44502936666 (a5b8314, 2.7 GB) restored (zstandard installed by the script); `lake build Checked` ≈ 10 min (the LE32 modules of 68c077a rebuilt). Disk: 3.5 GB free after the restore and deleting the zip; delete the zip first next time (DELETE_ZIP=1).
- CI at start: 44521044439 (68c077a, promotion of `laneEmden32_constants`): checked job past the build and the trust step at 12:41Z, kernel shards running. 44502936666 (a5b8314) running.

## Bottleneck (and what a yes/no changes)
- Part 1 (T2b, hypothesis necessity). Open since run 2026-11-19T0028Z: the upper density bound of `printedF0Mul_false_at` and `printedF0_false_at` and the printed-curvature condition of the latter. At density two every flat model with matter and a cosmological constant satisfies the printed relation (F at today's curvature is zero there), so those models cannot decide it. Question: does a non-ΛCDM model of `IsFRCosmo` exist in closed form? Yes → the hypotheses are classified and the repository gains a model family for the other open F(R) hypotheses. No → they need ODE existence for the fourth-order master equation.

## What we did
- **A closed-form F(R) model** (`Checked/Trust/NecessityAY.lean`). Writing φ(t) = F′(R(t)), the master equation is linear in φ: φ″ − Hφ′ + 2Ḣφ + ρ = 0. For a = t² (H = 2/t, R = −36/t²) its solutions are −(Ω/2) t⁻⁴ (the matter term) plus A t⁻¹ + B t⁴; in u = √(−R/36) = 1/t this is F′ = −(Ω/2)u⁴ + A u + B u⁻⁴, so F = C + 6Ω u⁶ − 24A u³ + 36B u⁻². Newton's constant today and F⁗(R₀) = 0 fix A = (32Ω + 64)/65, B = (Ω + 2)/130 (A = 64B); the expansion-rate equation fixes F(R₀) = −12(6Ω + 25)/13. Away from the model's curvatures F is continued by `Real.smoothTransition` (u = √(g(−R/36)), g smooth, positive, equal to its argument above one half), so F is C⁴ on ℝ. The four derivatives of F at the curvatures are Laurent polynomials in u (`L0`–`L4`, one `HasDerivAt` lemma each, transported by `Set.EqOn.deriv` on the open half-line R < −18). The master equation on (1/2, 4/3) is then a rational identity in t.
- Deceleration −1/2, jerk, snap and lerk 0 (the scale factor is a polynomial); the corrected curvature quantity −351/16 and the printed one 353/16, so in the model the multiplied form reduces to (6Ω + 25) = 0, i.e. it holds only at Ω = −25/6 (`pl_mul_false`), and the division form likewise (`pl_div_false`).
- `printedF0Mul_false_at_r2`, `printedF0_false_at_r2`, `printedF0_false_at_r3`: REDUNDANT (each alone). With run 0028Z's `_r1` theorems every hypothesis of both refutations is now classified. Axioms: propext, Classical.choice, Quot.sound.
- **Thomas–Fermi positivity** (`Checked/Trust/NecessityAZ.lean`, `tf_pos`, `tf_initial_slope_r5`): REDUNDANT. Mathlib's `x ^ (3/2 : ℝ)` is zero for x < 0 (`Real.rpow_def_of_neg`, cos(3π/2) = 0), so φ is nondecreasing; φ(b) > 0 would make y ≥ y(b) + φ(b)(x − b), against y → 0; so y is nonincreasing and y ≥ 0 (`le_of_tendsto`). A zero z > 0 is an interior minimum, so φ(z) = 0; with M = y(w), w = max(0, z − 1/2): φ ≥ −(3/2)M^{3/2} on [w, z] (φ − 2M^{3/2}√x is nonincreasing; √z − √s ≤ 3/4), then M ≤ (3/4)M^{3/2} ≤ (3/4)M, so M = 0; induction half a unit at a time reaches y(0) = 0 ≠ 1. No ODE uniqueness theorem is used. Compiled after five small fixes (≈ 15 min).
- **Thomas–Fermi limit at infinity** (`tf_lim`, `tf_initial_slope_r6`): REDUNDANT. If φ ≤ 0 everywhere, y decreases to a limit L, and L > 0 would give φ(x) ≥ φ(1) + 2L^{3/2}(√x − 1) → ∞ (`tf_lim_of_nonpos`). If φ(b) = v > 0 (`tf_no_pos_slope`): on [X, 2X] with X = max(2, b + 1, 160 w²), w = v^{−1/4}, the energy φ² − K y^{5/2}, K = 4/(5√(2X)), is nondecreasing (its derivative is φ y^{3/2}(2/√x − 2/√(2X)) ≥ 0); with (y − Y)^{5/2} ≤ y^{5/2} − Y^{5/2} (`pow52_sub`) this gives φ ≥ √K (y − Y)^{5/4}, so (y − Y)^{−1/4} + (√K/4)x is nonincreasing on [X + 1, 2X]; at X + 1 the first term is at most w (y − Y ≥ v), and √K(X − 1)/4 ≥ w (`big_X`), so it would be ≤ 0 at 2X, but it is positive. The first version timed out (200000 heartbeats per declaration): split into four lemmas, no option raised.
- Sanity check first (sympy, before any Lean): the relation `fR_values` of `FRCosmo` holds in the model for every Ω (`correctR · F(R₀) + 6H²(P₀Ω + Q₀) = 0` identically), so the model and the derivation agree.

## Measure
- Necessity: REDUNDANT 211 → 216, open 94 → 89 (StatementDeps relock below). Every hypothesis of `tf_initial_slope` is now classified (1, 2, 4 NEEDED; 3, 5, 6 REDUNDANT).

## CI read
- See Start.

## Next
- CI read first: 44521044439 (68c077a, promotion of `laneEmden32_constants`) and the run of this run's final push (new Checked module `NecessityAY`, ≈ 15 s locally). Green on every job for 68c077a or a descendant → `laneEmden32_constants` PROVED: the judged template in its STATE.md heading (`check_stale_status.py`) and one L.2 line to Alexander.
- Part 1 later: `FREta.eta_ratios` 3 (the corrected curvature quantity): in the power-law family a = (−t)^p (t < 0, p < 0, expanding) it vanishes alone at p = −5 ± √10 (the jerk combination is −2(2p − 1)/p² ≠ 0 there), and `fR_values` then forces Ω = −208/2889 ∓ 346√10/14445 (the three ratios of `P₀…Q₃` agree, checked in sympy); F′ is a combination of three real powers of R/R₀ with irrational exponents, so this needs rpow derivative lemmas (iterate `Real.hasDerivAt_rpow_const`) and the same smooth continuation. `eta_ratios` 4 (the jerk combination alone) has no power-law witness (it vanishes only at p = 1/2, together with the curvature quantity); a witness needs another closed form or ODE existence for the master equation. The same junk-value and energy arguments may classify the positivity and limit hypotheses of other boundary-value headlines with a power nonlinearity (scan TRUST_MAP's open list for `hpos`/`hlim` pairs).
