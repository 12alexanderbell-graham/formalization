# Run 2026-11-07T1228Z (scheduled)

**THE RESULT:** parts 2 and 5 (new certified answers; breadth: fluid mechanics) — the wall shear constant of the Blasius boundary layer, f''(0) of f''' + f f''/2 = 0, f(0) = f'(0) = 0, f' → 1, is certified to fourteen significant digits for *every* solution, f''(0) ∈ [0.33205733621519, 0.33205733621520], and a solution is proved to exist; the best rigorous enclosure the prior-art screen found in print has about five digits (Costin and Tanveer, arXiv:1303.1416: 0.3320574 ± 1.6·10⁻⁵), and no machine-checked result was found.

**What can a scientist now trust without checking it themselves, that they could not before?** The skin-friction constant of the laminar flat-plate boundary layer (the number behind the Blasius drag law c_f = 0.664/√Re) to fourteen digits, as a theorem about every solution of the boundary-value problem, with existence, stated with Mathlib definitions only and with the blind restatements (C³, `derivWithin`) of both closed from them. Status: proved in Work + AUDITED (blind restatement, referee STANDS); not yet in Checked.

**Measure:** certified answers not in print as rigorous values +1 (rigorous digits of the Blasius constant: ≈ 5 in print → 14); the validated simulator handles a third-order system for the first time (288 kernel-evaluated cells of degree 18 on [0, 9], enclosure radius 1.6·10⁻¹⁵, analytic tail bound 1.4·10⁻¹⁵). Freeze to both proofs in Work: 4db71de (12:38Z) → f892958 (13:24Z, bound) → 56ce5fc (13:37Z, existence).

**Weakest unchecked step:** the CI judge has not yet read the Work proofs (work job of 56ce5fc running when the run closed; local builds green with standard axioms); T5 round R is still not judged (the local full Checked build for it was stopped to free the machine for the Blasius certificate).

## Start
- 12:28Z: pre-cloned checkout detached; `git checkout -B main origin/main` (2e18495). add_repo not exposed. No LOCK (released by run 1028Z in 962b677); LOCK taken 12:31Z (5339bf0), heartbeat 13:17Z (cf13b32).
- Environment: elan installer worked (local Lean + Mathlib cache in ≈ 3 min). CI read at start: main run 42371257613 (962b677) — goal guard, packet, changes, work green; its checked job and shards 0/3 cancelled by coalescing behind 42371284272 (2e18495, pending); shards 1/2 running.

## Bottleneck
STATE next step 0: part 2/5 or 3. Part 2 had not moved since 0828Z. Question chosen: a famous physical constant whose rigorous enclosure in print is short (Blasius f''(0)), in a field the program had not touched (fluid mechanics), reachable with the kernel-evaluated simulator if it can carry a third-order system to a horizon where an analytic tail closes the infinite interval. Yes → a 14-digit certified constant where ≈ 5 digits were rigorous; no → the simulator's limits (Grönwall amplification without a contracting norm) are measured.

## Work
1. **Screen** (Sonnet, `prior_art_blasius.md`): rigorous enclosure in print ≈ 5 digits (Costin–Tanveer 2013), floats to 17 digits (Boyd 1999), no machine-checked result; the qualitative answer (existence, uniqueness, σ ≈ 0.332) is classical. Kind: **not in print as a rigorous value beyond ≈ 5 digits**.
2. **Float study and generator** (`scripts/blasius_float.py`, `gen_blasius.py`): scaling g''(0) = 1, σ = g'(∞)^{-3/2}; tail bound from p + (2/m) q non-increasing; sup-norm Grönwall amplification ≈ e^{∫(g+q)/2} ≈ 10¹⁷ over [0, 9] forces 10⁻³² coefficients (10⁻²⁶ gives radius 1.5·10⁻⁹).
3. **Freeze** 4db71de: `Work.Blasius.blasius_wall_shear`, `Work.Blasius.blasius_exists`. Blind restater (Sonnet, `blind/BlasiusBlind.lean`: C³ on [0, ∞), `derivWithin`) and referee (STANDS; margins 6.3·10⁻¹⁵ and 3.7·10⁻¹⁵; report saved by the run from the hand-back, `referee_blasius.md`) launched in one message.
4. **Bound** (f892958): `BTail.lean` (q = f'' never vanishes by Mathlib ODE uniqueness, so q(0) > 0; scaling; tail), `BCell.lean` (3-D validated cell), `BCellQ.lean` (kernel-evaluated cells), `BQData.lean` (288 cells, 48 segments of 6; one 24-cell segment per declaration was OOM-killed at ≈ 3 GB next to the full build), `Blasius.lean` (assembly: s² α³ = 1 and two rational checks), `BlasiusBlindClosed.lean`. Final proof first checked against a stub of the chain while the certificates compiled.
5. **Existence** (56ce5fc): `BExBase.lean` (clamped field), `BExFlow.lean` (fork A, 3 min: Picard–Lindelöf on every [0, n], glued), `BExBounds.lean` (fork B, 7.5 min: clamps inactive, a-priori bound q t³ ≤ 12 ⇒ p ≤ 173/50; monotone limit α > 0), `BlasiusExists.lean` (rescale by √α). Both forks' files compiled first time.
6. **Blind existence closed** (`BlasiusExistsBlindClosed.lean`): the blind C³ existence statement from `blasius_exists` (iterated `derivWithin` agree with p, q on [0, ∞); C³ by `contDiffOn_succ_iff_derivWithin` three times).
7. Round R preparation: `t5/judge_R_main.sh` (judge on main's tree with the round-R scripts as the blind column) and `t5/d05m/apply.py` (d05 with its matched text moved to the bullet as it stands on main); worktree `../fzR` had all six defects applied. Not run: the full Checked build it needs was stopped at 13:14Z.

## Not done
Promotion of the Blasius pair to Checked (literal readings of 0.33205733621519/…520 and the 1/2 coefficient, NV witness from `blasius_exists`, glossary/vocabulary, export cost of the 65 MB data module); judge round R.
