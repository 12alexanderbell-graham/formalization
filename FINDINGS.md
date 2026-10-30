# FINDINGS

Verified errors, gaps and unstated assumptions in sources (annex XLVII.2). Each entry: source location, Lean evidence, classification, scope, plain-words explanation, prior-art check, referee result.

## Verified findings

None yet.

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
| C1 | Cattoën & Visser 2007 (0710.1887) Eq. 59; repeated 2008 (0809.0537) Eq. 32 | d_Q(y) y²-coefficient 1/12 should be 1/24 | screen only |
| C2 | Aviles et al. 2012 (1204.2007) Eq. 15 | ΛCDM l₀ sign of 27/2 Ω_m²; m₀ terms | screen + independent sympy re-derivation of the correct value |
| C3 | Capozziello, Cardone, Salzano 2008 (0802.1583) App. A, Eqs. A2, A5 (+ O(Ω_k²) truncation in A6/A7) | z⁵ coefficients 7/2 q₀⁴ → 7/8; 24 l₀/144 → l₀/720 | screen only |
| C4 | Capozziello, Lazkoz, Salzano 2011 (1104.3096) Eq. 22 | CPL l₀: missing factor 9 | screen only |
