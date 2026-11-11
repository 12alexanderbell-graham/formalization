# Run 2026-11-11T0628Z (scheduled)

**THE RESULT:** part 1 (every link machine-checked; rotation: part 3 is being run by 0428Z, parts 2/5 by 0232Z) — T2b hypothesis necessity, cosmography families: the `_fails` headlines' hypotheses 3 (Hubble rate) and 4 (the printed-coefficient condition), and the smoothness hypothesis of the correct-order lookback series. Run 0428Z released the LOCK at 06:31Z (df2d22a); LOCK taken 06:36Z (8ce63fc).

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

## Next (written as the run goes)
- If this run is cut off: on a built tree, check out `wip/necessity-d`, `lake build Checked`, `TRUST_RELOCK=1 lake env lean scripts/trust/StatementDeps.lean` (detached), `lake env lean scripts/trust/Claims.lean`, the Python trust suite (`check_necessity.py`, `check_relock.py <base>`, `make_packet.py --check`), commit frozen.txt/TRUST_MAP/validation with a LEDGER line, fast-forward main.
