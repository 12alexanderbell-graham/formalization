# Run 2026-11-14T0628Z (scheduled)

**THE RESULT:** part 3 by rotation (parts 2/5 moved at 0428Z, part 1 at 0228Z, part 3 last at 0028Z) — every verified finding is now verified by a Lean record of its own: findings F4–F7 (the y-redshift series misprints of Bamba et al. 2012 / Capozziello & Salzano 2009 and Cattoën & Visser 2007) gained the records `Checked.Records.F4_values`, `F5_values`, `F6_third`, `F6_fourth`, `F7_third`, `F7_fourth`, so their headings, Printed and Correct lines and certified blocks in FINDINGS.md are generated from Lean like F1–F3 and F8–F14; the FB8 no-record baseline is empty.

**What can a scientist now trust without checking it themselves, that they could not before?** For F4–F7, what the finding says the printed coefficient is and how far it is from the corrected one is no longer an author sentence: it is a generated line backed by a kernel-checked evaluation of the PRINTED (blind-read) formula and of the correction through the pinned deceleration, cosmographic-coefficient and curvature definitions in de Sitter — e.g. the printed D²_{L,y} has the opposite sign of the corrected one (F4) and the printed d_Q y² coefficient is twice the corrected one (F5), each as a certified value in a named model.

**Weakest unchecked step:** the corrected formulas are FORMULA definitions whose correctness rests on the series theorems (`lumDist_y_third_order`, `dQ_y_third_order`, `lumDist_y_fifth_order`, `angDist_y_fifth_order`), which the records cite only in the unchecked notes; and the blind readings of the six printed formulas predate the blind route (no reader file describes their source, FB11).

## Start
- 06:28Z. add_repo not exposed; pre-cloned checkout detached with a stale local main; `git fetch --unshallow origin && git checkout -B main origin/main` = 96643b0. No LOCK → taken (7d1ada3).
- CI at start: 43551580603 (0935097) checked job building since 04:16Z (work, nanoda 4/4 green); 43563791919 (96643b0) pending.
- Local Lean: elan + Mathlib cache ≈ 2 min; `checked-build` of 43528111166 (8e3a22d) downloaded in 52 s, restored in 37 s (`pip install zstandard`); `lake build Checked` to 96643b0 ≈ 5 min (BEHChain the longest).

## Bottleneck (and what a yes/no changes)
- STATE 0l (c): F4–F7 were the four verified findings with no Lean record (`findings_norecord_baseline.txt`), so FB9–FB13 generated nothing for them: their headings and Correct lines were fixed no-record lines and every number was author prose. Yes (records reach PRINTED definitions and pinned ones, with no literal a blind reader would have to read): the four findings join the generated layer and the baseline empties. No: record which literal or prose rule blocks a hypothesis-free record.

## What we did
1. Records in `Checked/Records/Findings.lean` (scratch `runs/2026-11-14T0628Z/lean/RecordsY.lean`): the de Sitter scale factor `Real.exp` at time 0 (local lemmas: H = 1, q = −1, every cosmographic coefficient 1, Ω₀ = 1 + K), curvature constant K = 1 for F4–F6 and K = 5 for F7. Values: F4 printed −2.8333, corrected 2.8333, difference −5.6667; F5 0.4167, 0.2083, 0.2083; F6 D³ 4.1667, 3.3333, 0.8333 and D⁴ 3.75, 3.3417, 0.4083; F7 D³_A −0.4167, −1.6667, 1.25 and D⁴_A −0.2083, −2.2917, 2.0833 (exact rationals by Python Fractions first).
2. No hypotheses → no NV witness, no necessity obligation; every literal is a RoundsTo target (a1) or a numeral argument of a pinned definition (a4: `decel`, `cosmoCoeff`, `omega0`), so no literal reading or baseline line was needed.
3. Prose: the first docstrings failed V12 (`printedQ2 - correctQ2` and negative numerals as code spans that do not occur in the claim; Lean prints −0.0833 as `-833e-4`) and rule 7 (equation numbers in the section heading); rewritten in claim words ("rounds to", "less") and checked against a patched CLAIMS/meaning before rebuilding.
4. First FINDINGS generation failed S2 (two certified differences in one record have no selector): F6 and F7 split by coefficient order (`_third`, `_fourth`). Second: G1/G5 — the flat de Sitter values (3, 6, 0.25, 0.45, 0.75) equal numbers in other findings' author notes ("−6H₀²", "Ω = 0.25", "1/4"); rewording old notes would have touched F1, F2, F9, F10, so the witness model changed instead (K = 1 for F4/F5, K = 5 for F7), chosen with `scripts/prose_collisions.py`.
5. FINDINGS: blocks for F4–F7, `--write-layout F4 F5 F6 F7`, `check_numbers.py --write`; `findings_norecord_baseline.txt` empty; LEDGER lines (FB7, relock).

## Not done / next
- Fresh blind readings with reader files for the legacy PRINTED definitions (`printedD2y`, `printedQ2`, `printedD3y`, `printedD4y`, `printedDA3`, `printedDA4`, `printedD4`, F9/F10 families) so FB11 describes their sources: needs a new SecondReading module per reading and the agreement theorems repointed (`reader_of` uses the earliest runs/ copy committed before the module).
- Records that state the corrected value as a property of the distance itself (series theorem + evaluation) rather than through a FORMULA definition.

## Local checks and push
- Local: `lake build Checked` green; StatementDeps exit 0 with relock (287 headlines, NV 170/170; hypothesis tally unchanged: needed 582, redundant 155, open 235); Claims exit 0; check_claim_vocab, check_prose, check_literals, check_numbers, check_findings, make_packet (packet regenerated: the new records change its items), precheck_citations green; `records_check.py 0935097` after the final commit (see the commit message).
- CI read: 43551580603 (0935097) green on every job (checked job 04:14–07:05Z) → run 0228Z's necessity classifications stand in CI's TRUST_MAP. 43563791919 (96643b0, `bonnor_ebert_min`) started at 07:05Z (in progress at the end); this run's push cb49239 queued behind it.
