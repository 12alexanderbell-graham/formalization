# FINDINGS

Verified errors, gaps and unstated assumptions in sources (annex XLVII.2). Each entry: source location, Lean evidence, classification, scope, plain-words explanation, prior-art check, referee result.

## Verified findings

### F1 (was C2). Aviles, Gruber, Luongo, Quevedo, PRD 86, 123516 (2012), arXiv:1204.2007 (v1 and v2), Eq. (15): misprinted ΛCDM l₀ and m₀
- **Printed:** l₀ = 1 + 3Ω_m − (27/2)Ω_m², m₀ = 1 − (27/2)Ω_m² − 81Ω_m² − (81/2)Ω_m³ (typeset text read from the rendered PDF, both arXiv versions; `runs/2026-10-30T0220Z/typeset/`).
- **Correct (flat ΛCDM, H = H₀√(Ω_m(1+z)³ + 1 − Ω_m)):** l₀ = 1 + 3Ω_m + (27/2)Ω_m², m₀ = 1 − (27/2)Ω_m − 81Ω_m² − (81/4)Ω_m³. Printed q₀, j₀, s₀ are right.
- **Lean evidence (Checked, CI 40996176398 green):** `Checked.Cosmography.Aviles.flatLCDM_coeffs` (correct q₀…m₀ for every Ω, any C⁶ scale factor obeying the model near t₀); `avilesL0Claim_false`, `avilesM0Claim_false` (printed formulas refuted on Einstein–de Sitter, Ω_m = 1: true l₀ = 35/2 vs printed −19/2; true m₀ = −455/4 vs printed −134).
- **Classification:** Source error (misprint). **Scope:** the paper's numbers are unaffected: its Table V l₀ = 2.774, m₀ = −8.827 (and their asymmetric error bars) follow the correct formulas (referee check). The l₀ discrepancy, 27Ω_m², is nonzero for every Ω_m ≠ 0; the m₀ one vanishes at Ω_m = 0 and Ω_m = (√7 − 1)/3 ≈ 0.549.
- **Propagation:** the l₀ misprint is repeated in Aviles, Bravetti, Capozziello, Luongo, PRD 90, 043531 (2014), arXiv:1405.6935, Eq. (30) (rendered and read; that paper's Table IV value again follows the correct formula). Correct formulas appear in arXiv:1903.11433 Eq. (21), 2307.13464 Eq. (A7) (cites 1204.2007), 2408.10704 Eq. (7).
- **Plain words:** a sign slip in a printed formula, copied once, that a reader using the formula (not the paper's numbers) would get wrong: at Ω_m = 0.3 the printed l₀ is 0.685 instead of 3.115.
- **Fidelity audit:** `runs/2026-10-30T0220Z/audit.md` (blind restatement derived verbatim; restater's own reading also refuted, with a globally C⁶ model).
- **Referee (subagent, independent):** STANDS-WITH-CORRECTIONS (corrections adopted above: v1 exists and has the same text; m₀ nuance). Weakness noted: no Lean witness model with 0 < Ω_m < 1 yet (only Ω_m = 1 refutes in Lean; Ω_m ∈ (0,1) is conditional on existence).
- **Errata:** none found (arXiv abs pages, web search).
- **Open before reporting outside the program:** nanoda repair (STATE rule); Alexander decides any contact (47.1).

## Candidates under verification (UNVERIFIED, not findings)

From the literature screen of run 2026-10-30T0028Z (`runs/2026-10-30T0028Z/screen/SCREEN_REPORT.md`). Protocol before any of these becomes a finding (original XXVIII.1, XXIX; annex 47.2):
1. Confirm the printed formula from the typeset paper text (not a summariser): arXiv source or PDF text extraction, journal version if reachable.
2. Rule out convention differences (sign of k / Ω_k, a₀, c/H₀, definitions of j, s, l, m).
3. Check errata, later arXiv versions, follow-up papers that reuse the formula.
4. Lean evidence: prove the correct coefficient (or a concrete model where the printed one fails, e.g. Einstein–de Sitter or de Sitter) in `Checked`.
5. Referee subagent reconstructs and attacks without seeing our reasoning.
6. Repair nanoda (STATE known gap) before reporting.

| ID | Source | Claim to check | Status |
|---|---|---|---|
| C1 | Cattoën & Visser 2007 (0710.1887v1) Eq. 59; repeated 2008 (0809.0537v1) Eq. 32 | d_Q(y) y²-coefficient printed 1/12, should be 1/24 (paper's own Eq. 64 and 0809.0537 Eq. 17 agree with 1/24) | typeset CONFIRMED as printed (rendered PDF); sympy + hand check; no erratum. Next: Lean |
| C2 | Aviles et al. 2012 | — | → **F1** |
| C3 | Capozziello, Cardone, Salzano 2008 (0802.1583v2; App. A absent in v1) Eqs. A2 (D_z⁴), A5 (R_D⁵) | (7/2)q₀⁴ should be (7/8)q₀⁴; 24 l₀/144 should be l₀/720; k² terms dropped in R_D⁴, R_D⁵ (paper assumes k = 0) | typeset CONFIRMED (rendered PDF); sympy; de Sitter hand check (D_z⁴ = 1/5 with 7/8); no erratum. Next: Lean |
| C4 | Capozziello, Lazkoz, Salzano 2011 (1104.3096 v1, v2) Eq. 22 | CPL l₀: w_a² term printed (1−Ω_m)/4·(7−Ω_m), should be (9/4)(1−Ω_m)(7−Ω_m); all w₀ terms right; Eq. 21 has a dropped "−" sign before 27/4 | typeset CONFIRMED (rendered PDF, both versions); sympy (subagent). Next: independent re-derivation, Lean |
