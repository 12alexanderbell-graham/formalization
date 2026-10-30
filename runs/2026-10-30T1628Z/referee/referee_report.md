# Referee report: C14 (`Work/Cosmography/FREta.lean` @ a164886)

**Verdict: STANDS-WITH-CORRECTIONS.** The refutation is sound. Every correction below is to a docstring or the scope of a claim. No frozen statement is wrong or vacuous.

## What I checked (fresh, independent)
- **Field equations (`ref_fieldeq.py`):** I re-derived F(R₀), F″(R₀) and F‴(R₀) from the metric f(R) FLRW equations with dust. The inputs were a quintic Taylor a(t), cubic f, and E1, E1′, E1″ at t₀; the E1, E2, E2′ route gives the same result. This is independent of the program's scripts and of FRCosmo.
  - In the convention R = +6(Ḣ+2H²) it gives F/(6H²) = +(P₀Ω+Q₀)/R_corr, 6H²F″ = +(P₂Ω+Q₂)/R_corr and 36H⁴F‴ = −(P₃Ω+Q₃)/((j−q−2)R_corr).
  - This is exactly the review's (11.21), (11.23) and (11.24) after the map F_rev(x) = −F_std(−x), which corresponds to the review's convention (11.6) R = −6(Ḣ+2H²).
  - This confirms P₀…Q₃ and `correctR` independently.
- **(11.39):** j₀ = 1, s₀ = 1 − 9Ω/2 and l₀ = 1 + 3Ω + 27Ω²/2 re-derived from flat ΛCDM (`ref_checks3.py`).
- **Coefficients (`ref_eta.py`):** a symbolic derivative at ε = 0 reproduces `correct20` and `correct30` exactly. The difference is 0 for both.
  - η(0) = 0 for both.
  - Central finite differences (h = 1e-12, 40 digits): −0.2494433 and −0.3999559 at Ω = 0.041; −0.0319876 and −0.0151669 at Ω = 0.25.
  - The printed formulas give 0.1521, 4.020, −0.1187 and −0.1837 there. So (11.44)–(11.45) are faithful evaluations of the wrong formulas (11.42)–(11.43).
- **`eta_numbers` intervals:** all hold (−0.24944, −0.03199, −0.39996, −0.01517).
- **Where printed and correct agree in (0,1):** only Ω ≈ 0.5989 and 0.7314. These are the roots of (54Ω²−29Ω−2)(27Ω²+24Ω−32), the same for η₂₀ and η₃₀ (the η₃₀ difference has an extra factor (3Ω+8)). That matches `hne`.
- **Elaboration:** `lake env lean Work/Cosmography/FREta.lean` elaborates, with 8 `sorry` warnings only.

## Attempts to make the paper right (all fail; `ref_fieldeq.py`, `ref_readings2.py`)
1. Additive ε (q₀ = q₀^Λ + ε, …): 0.199 and 0.306 at Ω = 0.041.
2. F′(R₀) = (1+ε)⁻¹ in addition to the common ε. Upstream v1 §IV and the Hu–Sawicki section discuss this. With the common ε it gives −0.264 and 0.403; on its own it gives −0.014 and 0.003.
3. Any subset or sign pattern of (ε_q, ε_j, ε_s, ε_l), 80 combinations: none comes near 0.15 or 4 at Ω = 0.041.
   - ∂/∂ε_s = ∂/∂ε_l = 0 for both η, so only ε_q and ε_j matter.
   - Constant weights fitted to the printed η₂₀ at the two Ω values give (w_q, w_j) ≈ (−16, 106) and do not reproduce η₃₀.
   - Printed η₂₀ has the factor 27Ω³+276Ω²−4Ω−8 in its denominator, which no ε-direction can produce.
4. Non-cancelling R (printed (11.31) in F and corrected R in F″, or the reverse): 425ε and 682ε, or 1.5e-4ε and 2.3e-4ε.
5. Wrong expansions: N′/D′, N′/(D₀+D′), N′/D(ε=1), exact η at ε = 1, and the second-order coefficient. None match.
6. **General obstruction:** printed20/correct20 = Ω(27Ω²+60Ω+112)/(27Ω³+276Ω²−4Ω−8). printed30/correct30 is a *different* function of Ω.
   - So no constant rescaling matches: H₀ factors, (6H²)ⁿ normalisations, and the R → −R convention flip (η₃₀ → −η₃₀) are all ruled out.
   - No change confined to F(R₀) or to R matches either, because it would multiply both coefficients by the same factor.
   - Curiosity: the printed η₂₀ numerator, 64−6Ω(9Ω+8) = −2(27Ω²+24Ω−32), equals the correct numerator. The error in η₂₀ is in the denominator only.

## Issues

| # | Severity | Issue | Fix |
|---|---|---|---|
| 1 | Moderate (docs) | The sign of η₃₀ depends on convention. Under R → −R, F → −F(−R): η₂₀ is unchanged and η₃₀ changes sign. `correct30` ≈ −0.400ε and −0.0152ε is right *in the review's convention* (11.6), where F(R₀) = R₀+2Λ. In the common convention R = +6(Ḣ+2H²) it is +0.400ε and +0.0152ε. The refutation is unaffected: the printed values are 4 and −0.18, and the ratio is not constant. | In the docstring and the ledger, write "(review convention R = −6(Ḣ+2H²), (11.6))" next to the η₃₀ numbers, and note that η₃₀ flips sign under R → −R. |
| 2 | Minor (provenance) | In upstream 0802.1583, the η formulas are Eqs. (43)–(44). The numbers are an *unnumbered* display; upstream Eq. (45) is the Hu–Sawicki model. v1 and v2 are identical; there is no v3 (404). | Change "Eqs. (43)–(45)" to "Eqs. (43)–(44) and the unnumbered display after (44) (v1 p.7, v2 p.8)". |
| 3 | Minor (prior art) | Capozziello & Salzano 2009, arXiv:0902.0088, Eqs. (107)–(108) and the display after them, reprint the same formulas and numbers verbatim. That makes three appearances of the same error: 2008, 2009 and the 2012 review (v1, v2 and v3 all contain the same text). I found no erratum or correction. 1210.5149 and 1010.1547 do not use η₂₀ or η₃₀. | Record it in the provenance note. |
| 4 | Minor (hypotheses) | In `eta_ratios`, `hF : F(R₀) ≠ 0` is redundant. With `hR`, fR_values gives F = 0 ⇒ P₀Ω+Q₀ = 0, so both sides are the junk value 0. `hR` and `hJ` are necessary, since F″ and F‴ are undetermined without them. At ΛCDM, correctR = −9Ω²(27Ω²+60Ω+112)/16, j−q−2 = −3Ω/2 and F = −6H₀²(1−Ω/2) are all ≠ 0, so the hypotheses are not vacuous. | Optional: drop `hF`, or keep it and say it is redundant. Statements are frozen, so a docstring note is enough. |
| 5 | Info | `printedDen ≠ 0` is the right exclusion. printedDen = (Ω−2)(27Ω³+276Ω²−4Ω−8) has one root in (0,1), Ω ≈ 0.17608. printed30 has an extra 1/Ω², which is harmless for Ω > 0. eta20Of and eta30Of have no 0/0 at ε = 0 for any Ω ∈ (0,1), since P₀Ω+Q₀ = 9Ω²(Ω−2)(27Ω²+60Ω+112)/32 ≠ 0. `η(0) = 0 ∧ HasDerivAt η c 0` is the exact meaning of "η = cε to first order" for these rational functions. The common-ε reading is explicit in the text, and upstream v1 even writes q₀ = q₀^Λ(1+ε) with a single ε. | None. |
| 6 | Moderate (consequence, not formalized) | The linear formulas fail near ε ≃ 0.03 at Ω = 0.041. Along the family, j₀−q₀−2 = 0 at ε = 3Ω/(4−3Ω) ≈ 0.0317, where η₃₀ has a real pole (exact \|η₃₀\| reaches about 2.8e3 on the grid). F(R₀) has complex zeros at ε ≈ 0.0348 ± 0.0053i. So the radius of convergence is about 0.032, not 0.1. Exact η₂₀ is +0.0105 at ε = 0.1 and +0.0063 at ε = −0.1, while the linear prediction is ∓0.025. The paper's statement that it "numerically checked that the above relations approximate very well the exact expressions up to ε ≃ 0.1" is false at Ω = 0.041, for both the printed and the corrected coefficients. At Ω = 0.25 (poles at ε ≈ 0.23 real and 0.27 ± 0.055i) the exact \|η\| ≤ 0.005 for \|ε\| ≤ 0.1. | Mention in the C14 write-up. A possible follow-up candidate: `eta30` is unbounded near ε = 3Ω/(4−3Ω). |
| 7 | Info (consequence) | Nothing else in the review uses (11.42)–(11.45). The CPL figures and Fisher forecasts in §XI.C–E use the exact (11.21)–(11.24). The conclusion "F(R) deviates little from GR" survives, and is stronger, at Ω = 0.25: \|c₂₀\| = 0.032 and \|c₃₀\| = 0.015, against the printed 0.12 and 0.18. At Ω = 0.041 it is not supported for ε near 0.03. Side note: the review's later remark (p. ~122, as in 0902.0088) that "in the ΛCDM case η₂₀ and η₃₀ always have opposite signs" contradicts its own printed (11.44)–(11.45), which have the same sign at both Ω. With the corrected coefficients they also have the same sign for Ω < 0.731. | Optional mention. |

## Files written (all in `runs/2026-10-30T1628Z/referee/`)
- `referee_report.md` (this file)
- `ref_eta.py`: coefficients, finite differences, agreement roots
- `ref_fieldeq.py`: independent field-equation derivation and alternative readings
- `ref_readings2.py`: weights, R-mixing, wrong expansions, ratio obstruction, poles in ε
- `ref_checks3.py`: (11.39) re-derivation and exact η on \|ε\| ≤ 0.1
- Crops: `review_v3_p121_eq11.42-43.png`, `upstream_v1_p7_eq43-44_numbers.png`, `upstream_v2_p8_eq43-44_numbers.png` (each ≤ 46 KB)

PDFs, text dumps and full-page renders are in /tmp/ref_c14 (review v1–v3, upstream v1–v2, 0902.0088, 1210.5149, 1403.1421, 1010.1547).
