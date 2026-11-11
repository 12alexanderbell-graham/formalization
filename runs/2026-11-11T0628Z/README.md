# Run 2026-11-11T0628Z (scheduled)

**THE RESULT:** part 1 (every link machine-checked; rotation: part 3 is being run by 0428Z, parts 2/5 by 0232Z) — T2b hypothesis necessity, cosmography families: the `_fails` headlines' hypotheses 3 (Hubble rate) and 4 (the printed-coefficient condition), and the smoothness hypothesis of the correct-order lookback series. Auditor role: run 2026-11-11T0428Z holds the LOCK (heartbeat 05:58Z), so this run writes only in this folder until the LOCK is released (48.4; scratch Lean in `lean/`).

## Start
- 06:28Z. LOCK held by run 0428Z (30 min since heartbeat, alive). Repo pre-cloned (detached HEAD); `git fetch --unshallow` + `git checkout -B main origin/main` = 0b5193d.
- Local Lean: elan installer accepted; Mathlib cache ≈ 3 min; full `lake build Checked` started 06:32Z (detached).

## Plan (bottleneck and what a yes/no changes)
- 539 hypotheses open (`scripts/trust/necessity_open_baseline.txt`). Cheapest large family: the cosmography `_fails` headlines (≈ 17 headlines, indices 3 and 4). Witnesses: a constant scale factor (Hubble rate 0, remainder ≡ 0, so the "fails" conclusion is false) for index 3 where the printed-condition does not itself force H ≠ 0 (else redundancy), and a smooth scale factor with the printed condition = 0 (printed coefficient = correct coefficient, so the correct-order theorem gives o(·)) for index 4.
- Yes: ≈ 30 hypotheses classified in one generic pattern; no: record which shape blocks it.

## Next (written as the run goes)
