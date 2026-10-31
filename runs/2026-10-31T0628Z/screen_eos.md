# Screen: printed critical constants of two-parameter cubic EOS

Reference: x = v_c/b is the root > 1 of x³−3x²−3(u+w)x−(u²+uw−w); Ω_b, Ω_a, Z_c from the closed form (mpmath, 30 digits; script /tmp/screen_eos_scripts/eos.py). Every candidate below was read from a 200-dpi render of the page. PDFs and text dumps are in /tmp/screen_eos.

## Candidates

1. **arXiv:2607.10076v1** (Romero-Figueroa et al., "Geometric Universality…"), p.8, eq.(38). PR: printed Z_c = [χ(χ−2)−1]/[2(χ−1)²(1+χ)] ≈ 0.307, with χ = v_c/b = 3.951373. The printed expression evaluates to **0.0777961**, which is Ω_b. The correct value is Z_c = χ[χ(χ−2)−1]/[2(χ−1)²(1+χ)] = 0.3074013, so the formula is missing a factor χ. The decimal 0.307 is right. Crop: `typeset/screen_eos_2607.10076_p8_eq35-38.png`.
2. **arXiv:2607.10076v1**, p.7, eq.(33). RK: printed P_c = [17(1+2^{4/3})−37·2^{2/3}]/36 · (k_B/b)(a/k_Bb)^{2/3}, a coefficient of **0.0306521**. The correct coefficient is Ω_b(Ω_b/Ω_a)^{2/3} = (4·2^{2/3}−2^{1/3}−5)/3 = **0.0298944** (2.5% off). This also contradicts the paper's own eqs. (29), (33) T_c and (37): with the printed P_c, Z_c = 0.3418, not 1/3. Crop: `typeset/screen_eos_2607.10076_p7_eq31-34.png`. In the same paper, eqs. (27)–(32), (34) [PR T_c, P_c], (35)–(37) and the Table I Boyle ratios are correct.
3. **Solano-Torres, Estévez & Lee, Rev. Mex. Fís. 37 (1991) 255** (not arXiv; rmf.smf.mx), p.259. Printed Z_PR = **0.307399**; the correct value is **0.3074013** (2 units off in the last digit). The cause is that the printed formula was evaluated at the truncated ν = 0.253076; the exact ν = 0.2530766 gives 0.307401. The Z_PR formula itself, ν²(ν³+3ν²−3ν+3)/[(2ν³+3ν²+1)(1−ν)³], is correct. Crop: `typeset/screen_eos_RMF37-255_p259_ZPR.png`.
4. Same paper, p.258, eq.(7). PR: printed P_c = (ν³+3ν²−3ν+3)ν³/(1+2ν−ν²)³ · **(a/b)**. The coefficient is correct (0.0132366), but by dimensions the factor must be a/b², so this is a typo. T_c in (7), the RK eq.(6) (P_c, T_c, ν = 2^{1/3}−1), Z_RK = 2ν²/(1−ν)³ = 1/3, and Z_vdW = 3/8 are all correct. Crop: `typeset/screen_eos_RMF37-255_p258_eq7.png`.
5. (Marginal) **arXiv:2209.14616v1** (Trummler et al.), p.3, Table I. SRK Ω_a is printed as **0.42747**; the correct value is 0.4274802 (rounds to 0.42748; the error is 1.02 units of the last digit). This is the traditional Soave truncation. Everything else in the table is correct: SRK Ω_b = 0.08664; PR δ's, 0.45724 and 0.0778; and the RKPR closed forms Ω_a = (3y²+3yd+d²+d−1)/(3y+d−1)² and Ω_b = 1/(3y+d−1), with d = (1+δ₁²)/(1+δ₁), y = 1+[2(1+δ₁)]^{1/3}+[4/(1+δ₁)]^{1/3} and δ₂ = (1−δ₁)/(1+δ₁). I verified these to 10 digits for δ₁ ∈ {0.5, 1, 1.5, 2, 1+√2, 3, 5, 10}; y/(3y+d−1) = Z_c holds too. The text's "Z_c ≈ 0.285 SRK, 0.263 PR" equals EOS Z_c/1.168 (the RKPR c_z convention), so it is not an error. Crop: `typeset/screen_eos_2209.14616_p3_tableI.png`.

Out of scope: **arXiv:2201.08927v2** (Clapeyron.jl), p.13, eq.(1). The generic cubic is printed as p = Nk_BT/(V−Nb) **+** a(T)/((V−Nb₁)(V−Nb₂)). It has the wrong sign and is missing N² on the attractive term. No Ω values are printed. Crop: `typeset/screen_eos_2201.08927_p13_eq1.png`.

## Sources checked with no error found

- **Guevara-Rodríguez, Rev. Mex. Fís. 57 (2011) 125**, p.126, Table I (rendered; Z_c, Ω_a, b/v_c):
  - NM (2,−2): 0.302/0.498/0.313 vs 0.30185/0.49793/0.31291 ✓
  - TST (5/2,−3/2): 8/27, (7/9)³, 1/4, all exact ✓
  - H (3,−2): 0.286/0.483/0.247 vs 0.28619/0.48288/0.24712 ✓
  - PR: 0.307/0.457/0.253 ✓
  - SRK: 1/3, 0.427, 0.260 ✓
  - vdW: 3/8, (3/4)³, 1/3 ✓
  - Kubic–Clausius closed forms ✓ (derived by hand).
  - Schmidt–Wenzel forms with u+w=1 ✓: b/v_c = [1+∛(2+u+r)+∛(2+u−r)]⁻¹ with r = √(u²−4w), and Z_c = (3−w b/v_c)⁻¹. Both fail if u+w≠1, but the paper restricts them to u+w=1.
  - Ω_a = (1−Z_c(1−b/v_c))³ = (1−Z_c+Ω_b)³ holds for all (u,w) I tested. This may be a useful lemma.
- **arXiv:2004.03584v3**, p.12–13. PR Ω_A = (8+40η)/(49−37η) = 0.45724, Ω_B = η/(η+3) = 0.07780, η = 1/(1+∛(4−√8)+∛(4+√8)) = 0.25308 = b/v_c. All are exact identities (30 digits) ✓.
- **arXiv:2112.01975**, p.10: vdW 27/64, 1/8; PR 0.45724, 0.0778; SRK 0.42748, 0.08664 ✓.
- **arXiv:2212.10680**, App. C: RK 0.4274802, 0.08664035; PR 0.457235529, 0.077796074 ✓ (all digits).
- **arXiv:1812.03952**: 0.427480, 0.086640 ✓.
- **arXiv:2003.02051**: vdW Z_c = 0.375 ✓.
- **arXiv:1701.06524**, Table I: nuclear-matter Z_c (quantum statistics) is not comparable to the classical value, so it was skipped.
- No relevant constants: 1904.04778, 1712.06079, 1906.09530, 1611.00907, 2510.21065, 2607.10609, 2511.21485, 2410.23694, 2309.10659.
- Not retrievable: Valderrama 2000 (OGST, 403); Sci. Rep. 2025 / PMC12397249 (429 or bot page); Int. J. Thermophys. 10.1007/s10765-022-03090-1 (HTML only).

## Verdicts

- 2607.10076: **two genuine formula errors** (PR Z_c missing χ; RK P_c coefficient wrong).
- RMF 37 (1991) 255: Z_PR printed 0.307399 instead of 0.307401; P_c (PR) dimension typo.
- 2209.14616: correct apart from the conventional 0.42747 truncation.
- RMF 57 (2011) 125: all rows correct.
- 2004.03584, 2112.01975, 2212.10680, 1812.03952: correct.
- 2201.08927: sign typo in the generic EOS (outside the constants check).
