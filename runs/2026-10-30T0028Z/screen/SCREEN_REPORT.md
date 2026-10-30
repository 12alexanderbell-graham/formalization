# Literature screen of cosmographic series (subagent, run 2026-10-30T0028Z)

Status of everything here: **UNVERIFIED candidates** (original XVI). Screening by sympy against a 5th-order reference series; transcriptions made via WebFetch, which passes pages through a summarising model, so **transcription error is the leading alternative explanation** for every discrepancy. Nothing here is a finding until the protocol in FINDINGS.md is complete.

Reference: `reference.py` (a(t) Taylor to 5th order, q,j,s,l; d_L, d_A, χ, r, lookback, H(z), μ in z and y), validated against exact curved ΛCDM (`check_lcdm.py`), Milne, de Sitter. Results of all 105 checks: `all_results.txt`.

9 papers, 105 printed equations/identities: 83 agree. Discrepancies (4 papers):

| # | Paper | Eq. | Printed (as transcribed) | Reference | Screen's diagnosis |
|---|---|---|---|---|---|
| C1 | Cattoën & Visser, arXiv:0710.1887v1 (CQG 24, 5985) | (59) d_Q(y), y² term | (1/12)[3 − 2q₀ + 12q₀² − 4(j₀+Ω₀)] | 1/24 | typo; paper's own Eq. (64) is consistent with 1/24 |
| C1' | Cattoën & Visser, arXiv:0809.0537 (PRD 78, 063501) | (32) | same 1/12 | 1/24 | copied |
| C2 | Aviles, Gruber, Luongo, Quevedo, arXiv:1204.2007 (PRD 86, 123516) | (15) ΛCDM l₀, m₀ | l₀ = 1 + 3Ω_m − 27/2 Ω_m²; m₀ = 1 − 27/2 Ω_m² − 81Ω_m² − 81/2 Ω_m³ | l₀ = 1 + 3Ω_m + 27/2 Ω_m²; m₀ = 1 − 27/2 Ω_m − 81Ω_m² − 81/4 Ω_m³ | wrong values; EdS check (Ω_m=1: l₀ = 35/2, m₀ = −455/4) |
| C3 | Capozziello, Cardone, Salzano, arXiv:0802.1583 (PRD 78, 063504) | (A2) D(z), z⁵ term | (7/2) q₀⁴ | (7/8) q₀⁴ | typo (de Sitter check fails) |
| C3' | same | (A5) r₀(D), 5th order | 24 l₀ /144 | l₀/720 (= (l₀/5)/144) | wrong coefficient (de Sitter check fails) |
| C3'' | same | (A6)/(A7) | curvature terms only to O(Ω_k) | O(Ω_k²) terms at z⁵ (+Ω_k²/120) | unstated truncation (paper says it assumes k = 0) |
| C4 | Capozziello, Lazkoz, Salzano, arXiv:1104.3096 (PRD 84, 124061) | (22) CPL l₀ | (1−Ω_m)/4·[213 + (7−Ω_m)w_a]w_a | factor 9 on the (7−Ω_m)w_a term | missing factor 9 |
| (minor) | same | (21), (4) | missing operator / "+" in rendering | — | typesetting |

Independent re-derivation by the main session (`../lcdm_l0.py`, different method: d/dt = ȧ d/da on the Friedmann solution): ΛCDM q₀ = 3Ω_m/2 − 1, j₀ = 1, s₀ = 1 − 9Ω_m/2, l₀ = 1 + 3Ω_m + 27/2 Ω_m². Confirms the reference value in C2 (not yet the printed value).

Agreements worth reusing as checked sources: Visser gr-qc/0309109 Eq. (46), gr-qc/0411131 Eqs. (11), (19); Chiba & Nakamura (with their Ω_k0 = +k/(a₀H₀)² sign); Vitagliano et al. 0911.1249 Eqs. (4), (9)–(11); Dunsby & Luongo 1511.06532 Eqs. (13)–(14) to z⁶; Aviles et al. App. A d_L flat to z⁵.

Could not read: 1904.01427 (truncated), Weinberg 2008 §1.4 (not attempted), journal versions/errata (not accessible).
