# Run 2026-11-20T0628Z

**THE RESULT:** part 1 by rotation (STATE 2h → part 1 as in section Next of `runs/2026-11-20T0028Z/README.md`, trust track T2b). One more hypothesis of a listed statement is shown NEEDED by a Lean theorem with a counter-example (section What we did): the first equation of the boundary-layer system in a monotone statement.

**What can a scientist now trust without checking it themselves, that they could not before?** For one more hypothesis (f has derivative p, in the monotone statement of the Falkner–Skan class with β in (0, 1]), a Lean theorem that the statement fails without it; that statement now has three open hypotheses, each needing a solution of the full system (section Next).

**Weakest unchecked step:** the hypotheses still listed open in `TRUST_MAP.md` (section Next); the judge's slowest job is still nanoda shard 1 (section Next).

## Start
- 06:28Z. Local main was a stale divergent shallow clone; unshallowed and reset to origin/main 6b8fc4c. No LOCK → taken (4f18369).
- CI at start: 44682554465 (6b8fc4c, promotion of `laneEmden92_constants`) running; read in section CI read.
- Local Lean: elan + Mathlib cache ≈ 2 min; `checked-build` of 44667501738 (fc55e07) restored (the restore script installed `zstandard` itself); `lake build Checked` rebuilt the index-nine-halves modules and their dependants (≈ 15 min).

## Bottleneck (and what a yes/no changes)
- Part 1: `fs_monotone_of_limit` had four open hypotheses (2, 3, 6, 8). Hypothesis 3 (f' = p) is the only one whose obligation leaves a function free: does the third equation alone, with f(0) = 0, f free, p(0) = 0 and p → 1, force a positive shear? Yes → the hypothesis is redundant (a new proof); no → a witness in one module.

## What we did
- **Witness by a free function** (`Checked/Trust/NecessityBC.lean`, `fs_monotone_of_limit_h3`; scratch `runs/2026-11-20T0628Z/lean/FreeF.lean`, compiled locally first): without f' = p, the third equation q' = −f q − β(1 − p²) only constrains f where q ≠ 0 (f = −(q' + β(1 − p²))/q there); at a zero of q it asks q' = β(p² − 1), and f(0) = 0 asks q'(0) = −β. Witness β = 1, p(η) = Φ(1 − 1/(1 + η)) with Φ(x) = 132x⁶ − 386x⁵ + 381x⁴ − 251x³/2 − x²/2, Φ'(x) = x(x − 1/2)L(x), L(x) = 792x³ − 1534x² + 757x + 2 > 0 for x ≥ 0 (`ncbcL_pos`, nlinarith; L has one real root, in (−1, 0)). Φ(0) = 0, Φ(1/2) = −2, Φ(1) = 1: the profile starts with zero shear and second derivative −1 = −β, dips to −2 at η = 1 where q = 0 and q' = Φ''(1/2)/16 = 3 = β(p² − 1), and tends to 1; q vanishes only at η = 0 and η = 1 (`ncbcQ_zero`), and f is read off the equation elsewhere (Lean's x/0 = 0 gives f(0) = 0). The wall shear is 0, so the conclusion 0 < q(0) fails. Design: sympy, three linear conditions on the cubic L for a chosen dip value m = −2 (Φ(1) = 1, Φ(1/2) = m, L(1/2)/32 = m² − 1) with L(0) = 2β; m = −3/2, −3, −4 give an L with a sign change on [0, 1].
- **Float scan, negative** (`runs/2026-11-20T0628Z/scripts/scan/scan_f0.py`, not evidence): for hypothesis 6 (f(0) free), shooting over f(0) ∈ [−4, 4] and q(0) ∈ [−6, 6] at β = 1 found sign changes of p(8) − 1 on solutions that dip below −1, but one of them sits at f(0) = 0, where the listed statement rules such a solution out: these are crossings of p(8) through 1, not solutions tending to 1. A witness for 6 or 8 needs a solution of the full system on the whole half-line (section Next).
- Axioms of every new theorem: propext, Classical.choice, Quot.sound (StatementDeps).

## Measure
- Necessity: NEEDED 743 → 744, open 61 → 60 (StatementDeps of the final tree).

## CI read
- (pending)

## End
- (pending)

## Next
- (pending)
