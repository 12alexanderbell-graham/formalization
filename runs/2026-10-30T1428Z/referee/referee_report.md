# Referee report: candidates C11, C13 (`Work/Cosmography/FRCosmo.lean`)

Source: Bamba–Capozziello–Nojiri–Odintsov, arXiv:1205.3421 v1–v3, Sec. XI; upstream Capozziello–Cardone–Salzano,
arXiv:0802.1583 v1, v2. PDFs and full-page renders are in `/tmp/claude-0/referee` (outside the repo); crops are here.

**Verdict: STANDS (minor wording fixes recommended).**

## 1. Physics and the encoding

* Standard metric f(R), signature (−,+,+,+), R_s = 6(Ḣ+2H²), 8πG = 1, dust:
  `3f′H² = ρ + (f′R_s − f)/2 − 3H ḟ′`, `−2f′Ḣ = ρ + f̈′ − H ḟ′`. The paper uses R = −6(Ḣ+2H²) = −R_s. Its F is
  `F(R) = −f(−R)`, so F′ = f′, F″ = −f″ and F‴ = f‴. For ΛCDM this gives `f = R_s − 2Λ ↔ F = R + 2Λ`, which is (11.40).
  Substituting turns the standard pair into exactly `FriedmannEq` and `MasterEq`, which are (11.1)–(11.2) and (11.5)
  multiplied by 3F′ and −2F′. `ref_derive.py` checks this exactly: the equations at t₀ and the time derivative of
  the master equation at t₀ are identical in both conventions (`[True, True, True]`).
* (11.14)/(11.15) are the t₀ values of these equations. (11.17) is `newton`. The paper's (11.19) truncates F to a
  cubic, so F⁽ⁿ⁾ ≡ 0 for n ≥ 4. Lean requires only `F⁽⁴⁾(R₀) = 0`. That is a weaker hypothesis, so it gives a stronger
  positive theorem, and it is exactly what the derivative of (11.5) at t₀ needs.
* Regularity: a is C⁵ near t₀ (`ContDiffAt 5`). Then H is C⁴, curv is C³, and deriv²(curv) is C¹. F is C⁴, so
  deriv³F is C¹. Every term of `MasterEq` is therefore differentiable at t₀, and "eventually in 𝓝 t₀" gives
  (11.20). The hypotheses are neither vacuous (ΛCDM satisfies them) nor too weak: `ref_cert_check.py` shows that all
  three multiplied-out identities in `fR_values` are polynomial combinations (coefficients polynomial in q, j, s, l
  and H₀⁻¹) of E1, E2 and dE2/dt:
  `T0 = −2R·E1 − 6(q+2−j)(3q²+25q+3s+20−j)·E2 − 6(q+2−j)²/H₀·E3`, `T2·H₀³ = (j−3q²−25q−3s−20)H₀·E2 + (j−q−2)·E3`,
  `T3·H₀³ = (3jq+9j−l+18q²+53q+2s+28)H₀·E2 + (q²+9q+s+8−j)·E3`.
  So `fR_values` needs no nondegeneracy hypothesis; de Sitter, where correctR = 0, is included. Its
  statement is sound.
* Cosmographic conventions: (10.2)–(10.5) define q = −ä/(aH²) and j, s, l = a⁽ⁿ⁾/(aHⁿ). This matches
  `decel`/`cosmoCoeff`. (10.6)–(10.9) were rechecked and are correct.

## 2. Independent derivation (`ref_derive.py`, series method, not the h_i recursion of `derive_fr.py`)

* (11.10)–(11.12) are correct. For (11.13), `d³R₀/dt³ − printed = 24H₀⁵ j₀(q₀+4)`. The true value is
  `−6H₀⁵[l₀ − s₀ − 2(q₀+4)j₀ − 6(3q₀+8)q₀ − 24]`, the same as `curv_derivs`. **C11 confirmed.** In ΛCDM
  (j = 1, q+4 > 0) the difference is nonzero, so the refutation works.
* Solving E1, E2 and dE2/dt with F′ = 1 gives F(R₀), F″ and F‴ exactly equal to −6H₀²(P₀Ω+Q₀)/R_c,
  −(P₂Ω+Q₂)/(6H₀²R_c) and −(P₃Ω+Q₃)/(36H₀⁴(j−q−2)R_c), with R_c = `correctR` and the printed P₀…Q₃ (transcription
  checked against the 200-dpi typeset, p. 116). `correctR − printedR = −2(3j²q + 10j² + 11jq² + 4jq + 90q²)`.
  **C13 confirmed:** the printed R is wrong and the printed P/Q are right.
* The paper's own (11.20) has `+Ḣ₀Ṙ₀`; the correct sign is `−Ḣ₀Ṙ₀`. The same error appears in (11.18) and in
  upstream (20) and (22). (11.20) also writes `H Ṙ₀²` where H₀ is meant, which is harmless. `ref_variants.py` solves
  the closure with (a) the literal (11.20), (b) the printed (11.13), and (c) both. None of the three reproduces
  the printed R or the printed P/Q, because each gives a different denominator. Only the correct pair reproduces
  P/Q, and only with `correctR`. So the authors computed with correct equations; (11.13), (11.20) and (11.31)
  are typos in the typeset text. They do not change the mathematical result and do not explain the printed R.

## 3. Legitimacy of the refutation

* The ΛCDM values (q, j, s, l) = (3Ω/2−1, 1, 1−9Ω/2, 1+3Ω+27Ω²/2) were derived independently from H² = H₀²(Ωa⁻³+1−Ω).
  They agree with (11.39). With F = R + 2Λ, Λ = 3H₀²(1−Ω), F′ = 1 and F″ = F‴ = F⁗ = 0, the equations E1, E2 and dE2
  are identically 0, so `exists_LCDM_model` is the right statement.
* In ΛCDM, printedR = −(243Ω⁴+540Ω³−6264Ω²+9360Ω−3328)/16, which matches the Lean docstring, and correctR =
  −9Ω²(27Ω²+60Ω+112)/16. With printedR,
  `printedR·F(R₀) + 6H₀²(P₀Ω+Q₀) = (3/2)H₀²(Ω−2)(909Ω²−1170Ω+416)`. The discriminant is −143676 < 0 and
  Ω − 2 ≠ 0, so the multiplied form fails for every real Ω ≠ 2, in particular on (0,1). With correctR this
  expression is 0.
* Real roots of printedR at ΛCDM: −6.849, **0.53829**, 1.362, 2.726. One root lies inside (0,1). At Ω ≈ 0.538 the
  printed (11.21) has a pole rather than a wrong value. The Lean division form handles this correctly through `hR`
  and the `printedR ≠ 0` premise, so there is no junk value. However, the summary sentence "fails at every
  Ω ∈ (0,1)" is literally true only for the multiplied form (see recommendations). At Ω = 1/4 the printed formula
  gives F(R₀)/H₀² = +0.277 instead of −5.25; at Ω = 0.041 it gives +0.0034 instead of −5.877.
* The paper's remark after (11.40), that fixing (q₀, j₀) alone already forces (11.40), holds with correctR. With
  printedR, F(R₀) depends on s₀ and l₀, so the remark fails.

## 4. Whole block: further discrepancies

* (11.5): stray "+ +" (typographical only).
* **(11.42)–(11.45), the η's, are wrong.** The ratios F″/F and F‴/F do not depend on R, because R cancels. Using
  the printed P/Q, the common-ε scaling (11.41), and expansion to first order (`ref_eta2.py`, checked by finite
  differences):
  `η₂₀ = −2(27Ω²+24Ω−32)/(27Ω(Ω−2)(27Ω²+60Ω+112))·ε`, `η₃₀ = −2(81Ω²−60Ω−16)/(243Ω²(Ω−2)(27Ω²+60Ω+112))·ε`.
  The numerator of η₂₀ agrees with the printed one. The printed denominator `[3(9Ω+74)Ω−556]Ω²+16`
  = (Ω−2)(27Ω³+276Ω²−4Ω−8) does not agree. The printed η₃₀ numerator `6[(81Ω−110)Ω+40]Ω+16` also does not agree.
  Numbers (correct vs printed): η₂₀/ε = −0.249 vs 0.15 at Ω = 0.041 and −0.032 vs −0.12 at Ω = 0.25;
  η₃₀/ε = −0.40 vs 4 at Ω = 0.041 and −0.015 vs −0.18 at Ω = 0.25. The printed numbers are consistent with the
  printed formulas, so the formulas themselves are wrong. No R variant explains this (`ref_eta3.py`), and a
  sign-flipped l₀ does not either. The review's qualitative conclusion (small η) survives, and is in fact
  strengthened. This is a separate candidate and is not part of the frozen statements.
* (11.35)–(11.38), the CPL coefficients, were not checked.

## 5. Provenance and prior art

* Upstream 0802.1583 v1 and v2, eq. (33) (crops `CCS2008_0802.1583v2_p5_eq33_R.png` and
  `../typeset/CCS2008_0802.1583v1_p5_eq31-33_R.png`), reads `+[(3q₀+10)j₀ + 11q₀² + 4q₀ − 18] j₀ − (3q₀⁴+34q₀³+246q₀+104)`.
  It has the same wrong bracket sign and the same missing 180q₀², but **−18**. The review changed this to +18,
  adding a further error. With the upstream R in ΛCDM the residual is (3/2)H₀²(Ω−2)(909Ω²−1170Ω+344). This
  vanishes at Ω ≈ 0.4545 and 0.8326, so the upstream (23)+(33) fails in ΛCDM except at those two values.
* Upstream (16) has the same sign error as (11.13) in v1 and v2 (crops `CCS2008_0802.1583v{1,2}_p4_eq16_R3.png`).
  Upstream (20) and (22) have the same `+ḢṘ`. Upstream (43)–(45) are identical to (11.42)–(11.45), so the η errors
  are inherited.
* Capozziello & Salzano, arXiv:0902.0088 (Adv. Astron. 2009) repeats the upstream formulas: (80) has the wrong-sign
  d³R₀/dt³, (97) has the upstream R with −18, and (22)'s analogue has +Ḣ₀Ṙ₀.
* Later work, all checked by text search, uses different schemes and does not correct these formulas:
  Aviles–Bravetti–Capozziello–Luongo, arXiv:1210.5149 (z-derivatives, f″(R₀) = 0 imposed); Teppa Pannia &
  Perez Bergliaffa, arXiv:1301.6140 (a redshift-drift condition); Capozziello–D'Agostino–Luongo, arXiv:1709.08407
  (Padé) and arXiv:1904.01427 (review). Web searches found no erratum for 1205.3421 or 0802.1583. **The correction
  does not appear to be in the literature** (search not exhaustive).

## 6. Recommendations (statement level; none is blocking)

1. In the claim text and the docstring of `printedF0_false_at`, say "fails at every Ω ∈ (0,1) (multiplied form);
   in division form at every Ω ∈ (0,1) except Ω ≈ 0.53829, where the printed R vanishes in ΛCDM and (11.21) is
   undefined". The Lean statements are already correct.
2. The header comment "review v1–v3 identical" is confirmed for (11.13), (11.31) and (11.44)–(11.45). Add that
   upstream (33) has −18 and that the review's +18 is a new transcription error.
3. Optional new candidate: (11.42)–(11.45) and upstream (43)–(45), with the corrected η₂₀ and η₃₀ given above.

Files: `ref_derive.py/.out`, `ref_variants.py/.out`, `ref_cert_check.py/.out`, `ref_eta.py/.out` (superseded by
`ref_eta2`, because `ref_eta` misparsed (11.43)'s numerator), `ref_eta2.py/.out`, `ref_eta3.py/.out`, and crops
`review_v3_p115_eq11.20.png`, `review_v3_p121_eq11.42-43.png`, `CCS2008_*`.
