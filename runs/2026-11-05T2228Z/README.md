# Run 2026-11-05T2228Z (scheduled)

**THE RESULT:** part 3 (measured trust) by rotation (idle since 1628Z; STATE's next step): a blind red team aimed at run 2028Z's new evidence route (blind second readings substituted into claims by a generator) got **5 of 6 valid wrong claims accepted** by the checks on main; a new blocking check written blind to those defects, in parallel, **rejects all 5**.

**What can a scientist now trust without checking it themselves, that they could not before?** That a "read twice" or "second formulation" mark in CLAIMS.md / TRUST_MAP.md is not an alias of the program's own definition, not a claim reading typed into Checked by hand, not a generated claim whose quantifiers or hypotheses were changed during substitution, and not an agreement between two different false claims: each of these was accepted this morning and is now rejected by CI.

**Weakest unchecked step:** whether a reader file was written blind. A forged reading committed first under `runs/<run>/` next to a brief and routed through the generator passes every check (disclosure only). Second: a claim's quantifiers and hypotheses are the program's; a data reading does not cover them, and a closed blind restatement is not required for every headline.

## Start
- 22:28Z: no LOCK; pre-cloned checkout detached at 862bb00 (= origin/main); local main reset to origin/main. LOCK + stub efad54c.
- Local Lean: elan installer accepted; Mathlib cache; full `lake build Checked` 22:31–23:25Z (≈ 52 min).
- Bottleneck: part 3 by rotation; the 2028Z evidence route was guarded only by Lean equality and LEDGER disclosure. A yes (red team accepted) measures a structural gap; a no would let the route stand.

## Work
1. **Blind red team L** (Sonnet, `t5/briefL.md` = round K brief + 2028Z addendum; read-only snapshot of efad54c; disclosure of forged readings in the genuine form allowed). Six defects in ≈ 12 min (`t5/redteamL/`).
2. **Fork, same message, blind to the defects:** `scripts/trust/check_provenance.py` + stable generator copy `scripts/trust/gen_claim_readings.py` + `provenance_baseline.txt` (6 older modules whose reader copies live in Work/ or under other names) + CI step. Rules: reproducible generated modules; data-only token diff; independence (no subject, no alias, no unevidenced program helper; restricted imports); provenance (reader copy under runs/ with brief, committed before the Checked copy).
3. **Judge** (`t5/judge_L.sh`, combined, CI replica with author relock): all six valid. Before: 5/6 accepted (d05 caught only by the `6` of `ContDiffAt ℝ 6`). check_provenance (blind): rejects d01, d02, d03, d04, d06.
4. **After reading L:** StatementDeps rejects agreements of propositions proved with program theorems (equation lemmas and auxiliary proofs of definitions allowed; the generated (11.21) agreements use both) and asks a second reading for any CLAIM with inline arithmetic or a literal concluding value. Main passes unchanged (167/167, NV 108/108, map and frozen registry identical).

## CI
- Read: dd055a6 42113143146 green; 862bb00 42119105514 green. efad54c 42121729745, b45d334 42124275812, a8c9e61 (checks) and the records commit: read next run.

## Measurement
| | before | after |
|---|---|---|
| round L valid defects accepted (checks on main) | 5/6 | — |
| same, by check_provenance alone (blind) | — | 0/5 |
| evidence routes with a provenance check | 0 | 1 (readings, formulations, generated claims) |
