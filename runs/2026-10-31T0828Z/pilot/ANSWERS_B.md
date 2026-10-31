# Answers (Pilot B)

| Item | Q1 | Q2 | Q3 | Q4 | Defect found (what, MATERIAL/MINOR) | confidence |
|---|---|---|---|---|---|---|
| 02 | YES | YES | YES | YES | none (plain claim empty; flat D4_A true coefficient is -137 j, source quote confirmed) | high |
| 04 | YES | NO | YES | YES | Lean hypothesis `hne : (1-Ω)(7-Ω)wₐ = 0` but claim needs `≠ 0` -> theorem false as stated (printed l0 is correct when product = 0). MATERIAL | high |
| 06 | YES | YES | YES | YES | none | high |
| 08 | YES | YES | YES | YES | none (all four numbers recomputed) | high |
| 10 | YES | YES | YES | YES | none | high |
| 12 | YES | YES | YES | YES | none | high |
| 14 | YES | YES | YES | YES | none | high |
| 16 | YES | YES | YES | YES | none (MINOR note: CCS Eq.(33) prints "4q0 − 18", Bamba (11.31) prints "+18"; Lean follows Bamba, so fine) | med-high |
| 18 | YES | YES | CANNOT TELL | YES | none | high |
| 20 | YES | YES | YES | YES | MINOR: "only points not covered" ignores the hypothesis printedDen≠0 (den also vanishes at Ω≈0.17 in (0,1)); roots 0.5989, 0.7314 correct | med |
| 22 | YES | YES | YES | YES | none | high |
| 24 | YES | YES | YES | YES | none | high |
| 26 | YES | YES | YES | YES | none | high |
| 28 | YES | YES | YES | YES | none | high |
| 30 | YES | YES | YES | YES | none | high |
| 32 | YES | YES | YES | YES | none | high |
| 34 | YES | YES | YES | YES | none | high |
| 36 | NO | NO | CANNOT TELL | NO | Ω_b = 0.07780 is the Peng-Robinson value; Redlich-Kwong Ω_b = 0.08664 (0.086640). Wrong in plain claim and Lean `RoundsTo ... 0.07780 5`. MATERIAL | high |
| 38 | YES | YES | YES | YES | none | high |
| 40 | YES (plain) | NO | CANNOT TELL | YES | Item-local `hubble a t = deriv a t / a t ^ 2` (ȧ/a²) replaces the glossary ȧ/a; plain claim says ȧ/a. With that def the theorem is false (HubbleSpec pins d ln a/dt). MATERIAL | high |
| 42 | NO | YES | YES | NO | Plain words swap the values: says correct D4 = 0.4555, printed = 0.2153. Truth (and Lean) correct = 0.2153, printed = 0.4555. MATERIAL (plain claim only) | high |
| 44 | YES | YES | CANNOT TELL | YES | none | high |
| 46 | YES | YES | NO | YES | Source wrong: arXiv:1903.11433 Eq. (21) (v1, v2, v3) prints l0 = 1+3Ωm+(27/2)Ωm²+... (correct, Ωm=0.3 gives its own 3.115). The "1+3Ω−27/2Ω²" misprint is Aviles et al. arXiv:1204.2007 Eq.(15), which is what the Lean AvilesL0Claim encodes. MATERIAL (source) | high |
| 48 | YES | YES | YES | YES | none | high |

## Evidence

Method: sympy series (script /tmp/pilot/B_scratch/cosmo.py) for d_L, d_A in z and y and the lookback D(z) for general (q,j,s,l,K), H0=a0=1; flat LCDM and flat CPL coefficients from H(z) (c1.py, c2.py); eta formulas (c4.py); EOS critical constants (chem.py).

### Item 04 (Q2)
Printed CLS Eq.(22) l0 minus true flat-CPL l0 = -2(1-Ω)(7-Ω)wₐ² exactly (sympy; the true wₐ² coefficient is 9× the printed one). With `hne : (1-Ω)(7-Ω)wₐ = 0` (Ω=1, Ω=7 or wₐ=0) the printed l0 equals the true l0, so the conclusion `cosmoCoeff 5 a t₀ ≠ printed` is false; the plain words (and item 22, which has `≠ 0`) require `≠ 0`.

### Item 36 (Q1,Q2,Q4)
Critical point of P = RT/(v-b) - a/(v²+ubv) solved exactly: RK (u=1,w=0): x=v_c/b=3.8473, Zc=1/3, Ω_b=0.0866404, Ω_a=0.4274802. PR (u=2,w=-1): Ω_b=0.07780, Ω_a=0.45724, Zc=0.3074. So 0.07780 belongs to Peng-Robinson. Zc=1/3 and Ω_a=0.42748 are correct. (vdW item 44 checks: 3/8, 1/8, 27/64 exactly; hypotheses force RT>0, so no degenerate case.)

### Item 40 (Q2)
Glossary: `hubble a t = deriv a t / a t`. Item text defines `deriv a t / a t ^ 2` "in place of the glossary entry". HubbleSpec.deSitter (a=e^{ht} gives H=h) and powerLaw (n/t) fail for ȧ/a², so `hubbleSpec_pins` cannot be true with it; also the item's plain claim (H = d ln a/dt) is about ȧ/a.

### Item 42 (Q1,Q4)
ΛCDM Ω=0.3: q0=-0.55, j=1, s=0.35, l=3.115. correct D4 (7/8 q⁴) = 0.215255 -> 0.2153; printed D4 (7/2 q⁴) = 0.455459 -> 0.4555; difference = 21/8 q⁴ = 0.2402 -> 0.24. Plain text assigns 0.4555 to "correct" and 0.2153 to "printed". Lean is right. Check: de Sitter ln(1+z) series needs D4=1/5 with 7/8 (verified).

### Item 46 (Q3)
Fetched arXiv:1903.11433 v1, v2, v3: Eq.(21) l0 = 1 + 3Ωm + (27/2)Ωm² + ΩK² − ΩK(2−9Ωm); l0=3.115 at Ωm=0.3. The misprint "1+3Ωm − (27/2)Ωm²" is in Aviles et al. Eq.(15) (viewed page image), matching the Lean definition. Values quoted (−19/2 printed, 35/2 true at Ω=1) are right.

### Verified without defect
- LCDM coefficients: j=1, s=1−9Ω/2, l=1+3Ω+27Ω²/2, m=1−27Ω/2−81Ω²−81Ω³/4. Aviles Eq.(15) prints l0 with −27/2Ω² and m0 = 1−27/2Ω²−81Ω²−81/2Ω³ (page image). Item 24: printed−true m0 = (27/4)Ω(2−2Ω−3Ω²), root (√7−1)/3 correct. Item 14 diff 27Ω² ≠ 0.
- CCS lookback: correct D4 has 7/8 q⁴, printed 7/2 (A2 text checked), D1–D3 as in Lean. Items 10, 34.
- d_L(y): D2 = +(1/6)(12−5q+3q²−j−Ω) (printed has − sign); D3 true = printed + (Ω−1)(3q−2)/6; D4 true = printed + (Ω−1)²/120 + 5q(Ω−1)/12. Items 06, 32, 38 hypotheses match exactly. d_A(y): D3 true = printed + q(Ω−1)/4 (item 48). Bamba eqs (10.54)-(10.63) checked against PDF text.
- d_A(z): flat D4_A true has −137 j and otherwise equals demDA4; DA1z–DA3z verified; D4 curvature part lacks +K²/120. Demianski Eq.(23) prints +137 j0, D_L prints −105 q0⁴ (PDF text; Lusso reprint of −105 q0⁴ found). Items 02, 12.
- Cattoën-Visser Eq.(59) prints 1/12; true 1/24 (derived from d_L(y) and (1−y)^{3/2}); de Sitter: y(1−y)^{-1/2} gives 3/8 vs printed 3/4. Item 30.
- FR eta: eta20(ε=0)=eta30(ε=0)=0; d/dε equals correct20/correct30 exactly. Numbers: correct20(0.041)=−0.24944, (0.25)=−0.031988; correct30(0.041)=−0.399956, (0.25)=−0.015167; all satisfy RoundsTo (item 08). printed20−correct20 ∝ (27Ω²+24Ω−32)(54Ω²−29Ω−2), same for 30 (items 20, 28); roots 0.598881, 0.731445.
- FR printedR at LCDM = −(243Ω⁴+540Ω³−6264Ω²+9360Ω−3328)/16 (item 16); true R_LCDM would be −9Ω²(27Ω²+60Ω+112)/16; true F/(6H0²)=(Ω−2)/2 in ΛCDM; printed relation fails iff 7272Ω²−9360Ω+3328=0, which has negative discriminant, so fails for all Ω (items 16, 26). Bamba (11.31) prints +18 (Lean follows it); CCS Eq.(33) prints −18 (minor discrepancy in "copied verbatim" statement; neither passes the LCDM check).
- CPL printed l0 transcription matches arXiv:1104.3096 Eq.(22).
- Item 18: RicciFlatFLRWSpec anchors consistent (dS −12h², radiation 0, matter −4/(3t²)); curv = −6(ä/a+H²) pinned; fine.
