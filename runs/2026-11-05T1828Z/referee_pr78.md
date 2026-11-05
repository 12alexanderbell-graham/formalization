# Referee report: Work/Chemistry/PR78Acentric.lean (frozen, run 2026-11-05T1828Z)

**Verdict: STANDS-WITH-CORRECTIONS.** Both statements are faithful, can be satisfied, are not vacuous and are true. The Maxwell state is unique. The corrections are to the prose and bookkeeping only (§5).

**Files read:** `Work/Chemistry/PR78Acentric.lean`; `Checked/Chemistry/{CubicEOS,Coexistence}.lean` and `Checked/Records/Basic.lean` (definitions byte-identical to those refereed in 1228Z); `runs/2026-11-05T1228Z/referee_pr.md`. I did not read `runs/2026-11-05T1828Z/scripts/`.

**Scripts** (`runs/2026-11-05T1828Z/referee/`):
- `pr78_routeA_fugacity.py`: equal fugacity on the Z-cubic, closed-form Ω_a and Ω_b, mpmath at 50 digits.
- `pr78_routeB_dimensional.py`: dimensional; T_c, v_c by Newton on numerical P′, P″; p_s from the closed-form antiderivative of P (no quadrature, no fugacity), 45 digits. Two fluids: (R, a_c, b) = (8.314462618, 2.3, 1.2e-4), and R = −1, T_c < 0.

## 1. Numerics: the two routes agree to all printed digits (at least 44)
| quantity | value |
|---|---|
| κ(1), exact rational | 1.716915 |
| α(0.7) = (1 + κ(1 − √0.7))² | 1.6395287717399155439652782030286215466 |
| p_s/P_c | 0.0099979544435690022737045609718429525770872 |
| ω_out | 1.0000888464743740856375690988452932282246980 |
| v_l/b, v_g/b | 1.20920828872839327518…, 887.053194802575497973… |

- **Rounding windows** (`RoundsTo`: \|x − d\| ≤ ½·10⁻ᵏ). p_s/P_c ∈ [0.00995, 0.01005]: margins 4.80e-5 (lower), 5.20e-5 (upper). ω ∈ [0.9995, 1.0005]: margins 5.89e-4 (lower), 4.11e-4 (upper).
- **Binding constraint:** ω ≤ 1.0005, i.e. p_s/P_c ≥ 10^−2.0005 = 0.00998849370. The true value clears it by 9.46e-6 (relative 9.5e-4), about 4.5× looser than the PR76 proof needed (2.1e-4).
- **Uniqueness: yes.** On (b, ∞) P′ has exactly two zeros, v/b = 1.524596 and 22.153136 (P_min/P_c = −11.17, P_max/P_c = 0.19344). P = p_s is a cubic. The 1228Z argument carries over unchanged: Maxwell needs a sign change, so (v_l, v_g) are the outer roots and p_s ≤ 0 is excluded. A 499-level scan of (0, P_max) gives exactly one sign change of the equal-area function, in both fluids.
- **Context, ω_in → ω_out.** PR78: 0.491 → 0.490905, 0.8 → 0.800006, 1.2 → 1.200099, 1.5 → 1.499964, 2.0 → 2.000225. PR76 at the same inputs: 0.4877 at 0.491, 0.9424 at 1.0, 1.5783 at 2.0.
- The κ reproducing ω = 1 exactly is κ* = 1.7168078629; κ78(1) − κ* = 1.07e-4.

## 2. Attack on the statements
1. **Formula.** The Lean literal `0.379642 + 1.48503*1 - 0.164423*1^2 + 0.016666*1^3` parses as ((a + b) − c) + d = 1.716915, signs + − +. It is the PR78 cubic at ω = 1, inside the correlation's range ω > 0.491, so unlike 1228Z there is no out-of-range issue. α, T = 7/10·T_c and P_c are as in 1228Z.
2. **Hypotheses.** `hac`, `hvc` and `hl` each block a real junk counterexample, as in 1228Z: a_c = 0 gives p_s = 0; v = b is non-differentiable, so `deriv` = 0 there; v_l < b < v_g makes the integral non-integrable, so ∫ = 0 and p_s = 0.
   - `vl > b` is enough: with v_g > v_l > b and D(v) = v² + 2bv − b² > 2b² > 0, the integrand is continuous on [v_l, v_g].
   - `b < vc` is enough: D(v_c) > 0, and `isCritical_iff` then forces R·T_c > 0 and v_c/b = 3.95137, the single real root of x³ − 3x² − 3x − 3 = 0.
   - Route B with R = −1, T_c = −0.170144 reproduces p_s/P_c to every digit, so not assuming a sign is right.
3. **Definitions match the module doc.** `cubicP` with u = 2, w = −1 is the PR form. `IsCriticalIsotherm` is ∂P/∂v = ∂²P/∂v² = 0 at fixed T. `IsMaxwellCoexistence` is v_l < v_g, both pressures equal p_s, and equal area. `acentric` is −log₁₀(p_s/P_c) − 1.
4. **Nothing vacuous; neither conjunct is automatic.** Route B builds explicit witnesses. Remark, no correction needed: given p_s/P_c > 0, conjunct 1 follows from conjunct 2 (ω ∈ [0.9995, 1.0005] ⇔ p_s/P_c ∈ [0.0099885, 0.0100115]). In Lean conjunct 1 still excludes p_s/P_c < 0, because `logb` takes |x|. Harmless.
5. **The claim depends on the exact coefficients.** Variants make it FALSE (see §3): Cantera code variant 0.99799; Cantera documented variant 1.00214; ω³ term dropped 0.98629; − sign on ω³ 0.97252. The frozen (consensus) coefficients give 1.00009.

## 3. Transcription: the coefficients are confirmed
Every number below was seen in typeset or raw form, with no summarising tool:
- **thermo (C. Bell), raw `thermo/eos.py`, class PR78.** Code: `omega*(omega*(0.016666*omega - 0.164423) + 1.48503) + 0.379642`. Docstring: "κ = 0.379642 + 1.48503ω − 0.164423ω² + 0.016666ω³ if ω > 0.491". Cites Robinson & Peng, *The Characterization of the Heptanes and Heavier Fractions for the GPA Peng-Robinson Programs*, GPA, Tulsa 1978, and Robinson, Peng & Chung (Chem. Eng. Commun. 1985).
- **pychemqt, `lib/EoS/Cubic/PR78` source.** `0.379642 + 1.48503*w - 0.164423*w**2 + 0.016666*w**3` for ω > 0.491 (code tests `<= 0.491`, docstring says "ω < 0.491"). Cites Peng & Robinson, ACS Symp. Ser. 133 (1980) 393–414.
- **arXiv PDFs (`pdftotext`).** arxiv.org/pdf/1903.08852 (Kou, Sun, Wang): "m = 0.379642 + 1.485030ω − 0.164423ω² + 0.016666ω³, ω > 0.49"; arxiv.org/pdf/1611.08622 and 1802.09020 have the same text. arxiv.org/pdf/2012.12928 (Chakraborty et al.) eq. 2.9 has the same numbers, "in 1978 for heavier components having acentric factor greater than 0.49" (superscripts lost in extraction, minus sign kept).
- **DWSIM PR78 page (HTML):** "ω > 0.491: m = 0.379642 + 1.48503ω − 0.164423ω² + 0.016666ω³".

**Variants found.** Threshold 0.491 versus 0.49 (arXiv). "1.485030" is the same value with a trailing zero. Cantera is garbled and fails the claim (§2.5): its code (`src/thermo/PengRobinson.cpp`, raw) uses `0.374642 + 1.487503*w - 0.164423*w*w + 0.016666*w*w*w`, and the Doxygen header of `PengRobinson.h` in Cantera 3.2 says 0.379642 + 1.487503ω − 0.164423ω² + 0.016667ω³. The primary GPA RR-28 (1978) was not reachable.

## 4. Prior art
- **Qualitative answer in print.** Mohamed, Kozinski & Ramos-Pallares, ACS Omega 9 (2024) 50385, doi 10.1021/acsomega.4c07037 (read in full on PMC): "The updated piecewise function produced results with lower deviations for heavy hydrocarbons with an acentric factors higher than 0.491 compared to those from the original expression for m." DWSIM: "The 1976 m(ω) gives too high a vapor pressure for compounds with large acentric factors … so they come out too volatile".
- **Side finding.** The same ACS Omega paper says PR76 m was "fitted to match pure component saturation pressure from the normal boiling point up to the critical point". This is a secondary source, but it confirms the recollection flagged in 1228Z §3.
- **Exact figure not located.** No source I found prints ω_out(PR78, ω = 1) ≈ 1.0001, or PR76's 0.942 or 0.058 shortfall.
- **Classification:** qualitative answer in print; exact figure not located. RR-28 and the full text of Piña-Martinez et al. 2019 were unreachable, and either could tabulate it.

## 5. Verdict: STANDS-WITH-CORRECTIONS
1. **The statements stand as frozen.** Both are true: p_s/P_c = 0.0099980 rounds to 0.0100, ω = 1.000089 rounds to 1.000. The binding margin is 9.46e-6 in p_s/P_c, on the ω ≤ 1.0005 side. Uniqueness is genuine.
2. **Bookkeeping.** Record this as a certified known effect, not a new result. PR78 was fitted to heavy-compound vapour pressures and ω is itself a vapour pressure at T_r = 0.7, so near-self-consistency is expected by construction. Say "the 1978 correction is qualitatively in print; the value 1.00009 was not located in print".
3. **Prose (citation).** Cite the 1978 source as GPA Research Report RR-28 (Robinson & Peng 1978). Note that the correlation is often cited via Peng & Robinson, ACS Symp. Ser. 133 (1980), or Robinson, Peng & Chung (1985). Mention the threshold variant (0.491 versus 0.49), which does not matter at ω = 1.
4. **Prose (transcription warning).** Add one line saying Cantera's coefficient variants (0.374642 / 1.487503 / 0.016667) are garbled and would give ω_out = 0.998 or 1.002. The statement uses the consensus coefficients: thermo, pychemqt, DWSIM and four arXiv papers.
5. **Optional, not required.** The 1228Z prose about PR76 being fitted "from the normal boiling point to the critical point" now has a secondary source (ACS Omega 2024). A stronger statement that is still true is available if wanted: ω = 1.0001 to 4 decimals, margin 3.9e-5.
