# Run 2026-11-11T0628Z (scheduled)

**THE RESULT:** part 1 (every link machine-checked; rotation: part 3 was run 0428Z, parts 2/5 run 0232Z) — T2b hypothesis necessity: 70 more hypotheses machine-classified (NEEDED 255 → 303, REDUNDANT 51 → 73, open 555 → 485; headlines with every hypothesis classified 14 → 29 of 151) across the cosmography series, the f(R) slow-roll ratios, the cubic equations of state, the records F1–F3 and the Falkner–Skan separation pair (`Checked/Trust/NecessityD.lean`).

**What a scientist can now trust without checking, that they could not before:** for each of these hypotheses, a Lean theorem shows either a concrete model meeting every other hypothesis where the claim is false (the hypothesis is doing work), or the claim proved without it. E.g. the printed-coefficient conditions of all 17 "printed coefficient fails" cosmography headlines are exactly what makes them true; the smoothness hypotheses of the distance series are needed (a scale factor with one derivative too few breaks every series); smoothness is automatic under the ΛCDM and CPL laws.

**Weakest unchecked step:** the 485 hypotheses still open (largest blocks: the B1 interval hypotheses, the Falkner–Skan boundary-value families, the smoothness hypothesis of the `_fails` headlines); and REDUNDANT here partly rests on Lean's `x / 0 = 0` (the `H₀ ≠ 0` cases say so in their docstrings).

## Start
- 06:28Z. LOCK held by run 0428Z (30 min since heartbeat, alive). Repo pre-cloned (detached HEAD); `git fetch --unshallow` + `git checkout -B main origin/main` = 0b5193d.
- Local Lean: elan installer accepted; Mathlib cache ≈ 3 min; full `lake build Checked` started 06:32Z (detached).

## Plan (bottleneck and what a yes/no changes)
- 539 hypotheses open (`scripts/trust/necessity_open_baseline.txt`). Cheapest large family: the cosmography `_fails` headlines (≈ 17 headlines, indices 3 and 4). Witnesses: a constant scale factor (Hubble rate 0, remainder ≡ 0, so the "fails" conclusion is false) for index 3 where the printed-condition does not itself force H ≠ 0 (else redundancy), and a smooth scale factor with the printed condition = 0 (printed coefficient = correct coefficient, so the correct-order theorem gives o(·)) for index 4.
- Yes: ≈ 30 hypotheses classified in one generic pattern; no: record which shape blocks it.

## Done so far
- 43 hypotheses classified, all compiled locally with standard axioms (`lean/NecessityD.lean`, `lean/LookbackJunk.lean`, `lean/LawSmooth.lean`; merged as `Checked/Trust/NecessityD.lean`, pushed to branch `wip/necessity-d` 7c720c0 with the updated `necessity_open_baseline.txt`):
  - printed-coefficient condition NEEDED in all 17 `_fails` headlines that had it open (models `1 + t + c t³` and zero curvature: printed = correct, the correct-order theorem gives the bound the headline denies);
  - `H₀ ≠ 0` NEEDED in 4 (static model `a = 1`), REDUNDANT in 12 (condition mentions q₀, j₀ or Ω₀ − 1; `x/0 = 0` makes them vanish when H₀ = 0);
  - `lookback_second_order`: differentiability of ȧ at t₀ NEEDED (`1 + t + t|t|`), eventual differentiability of a REDUNDANT; `CCS.lookback_fifth_order`: C⁵ NEEDED (`1 + t + t⁴|t|`, junk l₀ = 0, remainder `t⁴|t| − a z⁶`);
  - smoothness REDUNDANT under the flat ΛCDM and CPL laws (bootstrap `contDiffAt_of_law`): `Aviles.flatLCDM_coeffs`, `CPL.flatCPL_coeffs`, `CPL.printedL0_ne`, records F1_l0, F2_toy, F2_error, F3_D4_LCDM.

## Later in the run
- Added: smoothness NEEDED in the y- and z-distance series (5) and `dQ_y_third_order` (`compare_general`), `exists_local_model` (smoothness of the law), the f(R) slow-roll ranges (4), the printed l₀/m₀ conditions (3 needed, 2 redundant: a flat ΛCDM model for every Ω), the critical cubic (2) and all five hypotheses of `exists_unique_critical`. 70 theorems in `Checked/Trust/NecessityD.lean`.
- Integration: second `lake build Checked` (NecessityD + root) green 08:08Z; `TRUST_RELOCK=1` StatementDeps: needed 303, redundant 73, open 485, fully classified 29/151, NV 155/155; Claims; Python trust suite (see commit message).
- Integrity event: one force-push on this run's own branch `wip/necessity-d` (LEDGER); old head kept as `wip/necessity-d-first`.

## Next
- Read CI: run 42984797370 (96a1175, everything but NecessityD; first main run since 3e54961 not cancelled while pending — it also judges the separation promotion) and the run of this run's final push.
- T2b: 485 open. Largest blocks: B1 interval hypotheses (≈ 150), Falkner–Skan boundary-value families, the `_fails` smoothness hypothesis (index 1; needs a `C⁴` scale factor with the true fifth-order coefficient −315 q₀⁴ and a junk fifth derivative, e.g. `+ t⁹ sin(1/t)`), the 26 bundled predicates (item 0b).
