# Run 2026-10-30T1028Z (scheduled)

Environment: repo pre-cloned (add_repo not exposed; not needed); pushes verified (remote head = local); local Lean via elan + cache (~3 min); previous run's last CI runs 41036605782, 41037683712 green; this run's CI in STATE.

**TARGET AND BOTTLENECK:** target 1 (cosmography). Bottleneck: curvature in Lean (C6/C7 needed the curved comoving transverse distance and a fifth-order curved d_L(y)). Yes → finding F6 and the first general curved d_L series in Lean; no → the screen and referee derivations were wrong.

**WHAT WE ACTUALLY DID:** froze C6 (b485344), proved the general curved d_L(y) series to y⁵ and the refutations (be8b84d, ~15 min of Lean work), blind restatement (closed in Lean), referee (STANDS-WITH-CORRECTIONS, found the upstream source), promoted to Checked with the S_K helper.

**RESULT:** PROVED + AUDITED: `Checked.Cosmography.BambaK.{lumDist_y_fifth_order, printedD3y_fails, printedD3y_fails_past, printedD4y_fails, printedD4y_fails_past, bambaD3yClaim_false, bambaD3yClaimPast_false, bambaD4yClaim_false, bambaD4yClaimPast_false, milne_printedD3y_fails_past, milne_printedD4y_fails_past, printed_flat_eq}`, helper `Checked.Cosmography.Transverse.transverse_expansion`. Verified findings **F6** (Bamba et al. 2012 Eqs. 10.55–10.57, copied from Capozziello & Salzano 2009 Eqs. 56–58: curvature terms of D³_{L,y}, D⁴_{L,y} wrong) and **F7** (Eqs. 10.61–10.63, d_A,y: `Checked.Cosmography.BambaA.{angDist_y_fifth_order, printedDA3_fails[_past], printedDA4_fails[_past], bambaDA3Claim[Past]_false, bambaDA4Claim[Past]_false, milne_printedDA4_fails_past}`; freeze 4337b9b, proofs 8e2df42). Correction to F4's provenance (the sign error is already in the 2009 paper).

**ACTUAL IMPROVEMENT:** first general luminosity-distance theorem with spatial curvature (every real K, fifth order, any C⁵ scale factor); a reusable truncated-series algebra (`approx_mul`, `approx_pow`) that replaces hand-built remainder chains.

**WHAT COULD STILL BE WRONG:** y-series form is inferred (as F4); restater and referee are the same model; part of the D⁴ discrepancy ((Ω₀−1)²/120) is explained by the review's own O(χ⁵) truncation in (10.30) (the rest is not); no impact on the review's numerical results.

**STILL MISSING / NEXT STEP:** see STATE (C9/C10 from the referee's side checks; Sec. XI screen).

Files: `source_C6.md`, `audit.md` (C6, C7), `blind/` (C6_blind.lean, sympy), `referee/` (scripts; PDFs kept out of the repo), `scripts/gen_curved.py` (+ `polys.json`, `emit_lean.py`, parts), `typeset/` (v1–v3 crops, upstream 0902.0088 p. 7 crops).
