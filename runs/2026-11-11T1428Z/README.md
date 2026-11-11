# Run 2026-11-11T1428Z (scheduled)

**THE RESULT:** part 1 (the trust system): hypotheses bundled behind a definition are now classified conjunct by conjunct (T2b item 3e from blind red team AF), machine-checked; and main's red checked job (run 1028Z's two promotions) repaired.

**What a scientist can now trust without checking it themselves:** for the van der Waals, Redlich–Kwong and Peng–Robinson critical constants, each of the two critical-point conditions (zero slope, zero curvature) is shown needed by a machine-checked counterexample — the three headlines now have every assumption classified (fully classified headlines 29 → 32 of 153, a CI-enforced ratchet). The trust map states which bundled assumptions are still classified only as a whole.
**Weakest unchecked step:** binder-nested parts of model predicates (the expansion law's `a > 0 ∧ differentiable ∧ law` under ∀ᶠ; IVP solutions' ODE conjunctions) are still classified only as bundles in 23 headlines.

## Results
- `Checked/Trust/NonVacuity.lean`: `hypConjuncts`, `necessity% thm i j`, `dropped% thm i j` (obligations computed from the statement).
- `scripts/trust/StatementDeps.lean`: `conjuncts of i (m)` parts; `bundled i` dropped only if every conjunct is classified and none hides a conjunction under a binder (`hidesAnd`).
- `scripts/trust/check_necessity.py`: parser for conjunct parts (partition, range, never next to `bundled i`), baseline lines may lose reasons, never gain; selftest 10 new controls.
- `Checked/Trust/NecessityF.lean`: 22 witnesses (static model / de Sitter for `0 < H₀` and the law in 7 cosmography headlines; T fixed by the other condition at R = a = b = 1, v = 2 for 3 cubic-EOS headlines; rest state / straight line for Duffing). Standard axioms only (`#print axioms` checked on three).
- Measure: fully classified 29 → 32 of 153; shape baseline 26 → 23. (First push said 40: corrected the same run, see LEDGER.)
- CI repair: LEDGER disclosure by TRUST_MAP name; `scripts/trust/local_frozen_step.py` (both CI trust steps from lean.yml; local run green, base 151807e).

## Start
- 14:28Z. Pre-cloned checkout detached; `git checkout main` + pull = a00b1b4. No LOCK (run 1028Z removed it; run 1228Z ended 13:20Z) → LOCK taken f70905f.
- **Local Lean available** (elan installer accepted; Mathlib cache ≈ 8 min; Checked built locally from scratch).
- CI of run 1028Z's final push a00b1b4 (run 43031110000): goal guard, changes, packet, work job, nanoda 0–3 (memoised passes) green; **checked job in progress** (started 14:19Z) at 14:40Z — read later this run.

## Plan (bottleneck; what a yes/no changes)
- STATE exact next step 0b (from blind red team AF): 26 headlines carry `shape: bundled i` — a hypothesis that is a conjunction behind a definition (IVP solution, critical point, expansion law), shown needed only as a bundle. Yes (a mechanical per-conjunct obligation + witnesses): `bundled i` disappears for every headline whose conjuncts are all witnessed, the count of fully classified headlines rises honestly, and the shape baseline shrinks. No: record what resists.

## Hand-off (kept current)
- 16:39Z: pushed to main (ea6f45c, e3337c7): per-conjunct obligations, StatementDeps/check_necessity, `Checked/Trust/NecessityF.lean` (22 witnesses), CI repair (LEDGER disclosure for N2), `scripts/trust/local_frozen_step.py`; local full build, trust step and frozen step (base 151807e) green. `wip.patch` superseded.
- 16:45Z: run 1628Z (auditor role) rightly points out that a conjunct under a binder (`∀ᶠ t, a > 0 ∧ differentiable ∧ law`; Duffing `∃ v, v 0 = 0 ∧ ODE`) still bundles parts. Adopted: StatementDeps keeps `bundled i` when a conjunct hides a conjunction under a binder (`hidesAnd`). Its *parts* design (monotone positions, part replaced by `True`) is the route to close those; this run does not duplicate it.

## End (17:15Z)
- Final push dc2f575 (CI run 43066009791 queued; not read this run — STATE exact next step 0a). LOCK removed; run 1628Z (auditor role, red team AG on necessity shapes) can take it.
- On AG d04 (fuel exhaustion): on main since afd1121, a conjunct left unsplit by `hypConjuncts` is still an `∧`, and `hidesAnd` returns true for it, so `bundled i` stays; making out-of-fuel an error (no obligation) is still the cleaner repair. d01–d03, d05, d06 are pre-existing shape-layer gaps (AG_FINDINGS.md in run 1628Z's folder).
