# Referee report: Work/Chemistry/SRKAcentric.lean (frozen, run 2026-11-06T0028Z)

**Verdict: STANDS-WITH-CORRECTIONS.** Both statements are faithful, can be satisfied, are not vacuous and are true. The Maxwell state is unique. The corrections are to the prose only (§5): ω = 1 lies outside the range Soave fitted (0 to 0.5), and the qualitative effect is known.

**Files read:** `Work/Chemistry/SRKAcentric.lean`; `Checked/Chemistry/{CubicEOS,Coexistence}.lean`, `Checked/Records/Basic.lean`; `runs/2026-11-05T1828Z/referee_pr78.md`. I did not read `runs/2026-11-06T0028Z/scripts/`.

**Scripts** (`runs/2026-11-06T0028Z/referee/`):
- `srk_routeA_fugacity.py`: equal fugacity on the Z-cubic with closed-form Ω_a = 1/(9(2^{1/3}−1)) and Ω_b = (2^{1/3}−1)/3, 50 digits. Also produces the ω_in → ω_out table and κ*.
- `srk_routeB_dimensional.py`: dimensional, 45 digits. T_c and v_c come from Newton on numerical P′ and P″. p_s comes from the closed-form antiderivative R T ln(v−b) − (a/b) ln(v/(v+b)), with no quadrature and no fugacity. It also finds the spinodals and scans for uniqueness. Four fluids: physical (R = 8.314…, T_c ≈ 190); (2.5, 7, 0.3); **R = −1, T_c = −0.2027**; **a_c = −1, T_c < 0**.
- `srk_hypotheses.py`: root structure below b, and the b < 0 junk counterexample.
- `srk_refit_soave.py`: reconstructs Soave's 1972 fitting procedure.

## 1. Numerics: the two routes agree to at least 44 digits
| quantity | value |
|---|---|
| κ(1) (Lean literal) | 1.878 exactly |
| α(0.7) = (1 + κ(1 − √0.7))² | 1.7076020182927992318830913371721054032 |
| p_s/P_c | 0.010185111983371700179592391262953239120 |
| ω_out | 0.99203419165222808672494939783772843950 |
| v_l/b, v_g/b | 1.22694883903844141345873360…, 782.076672819352150229642886… |
| v_c/b, Z_c (route B, from Newton) | 3.84732210186 = 1/(2^{1/3}−1), 1/3 |

- **Rounding windows** (`RoundsTo`: \|x − d\| ≤ ½·10⁻ᵏ).
  - p_s/P_c ∈ [0.01015, 0.01025]: margin 3.51e-5 below, 6.49e-5 above.
  - ω ∈ [0.9915, 0.9925]: margin 5.34e-4 below, 4.66e-4 above.
- **Binding constraint: ω ≤ 0.9925**, i.e. p_s/P_c ≥ 10^−1.9925 = 0.0101741937. The true value clears it by 1.09e-5 (relative 1.1e-3), comparable to PR78's 9.5e-6. The other side, ω ≥ 0.9915, has 1.25e-5 of room in p_s/P_c.
- **Other fluids.** R < 0 with T_c < 0, and a_c < 0, give p_s/P_c identical to 47 digits.
- **Uniqueness: yes.**
  - On (b, ∞), P′ has exactly two zeros, v/b = 1.5728971 and 20.240186 (P_min/P_c = −9.927, P_max/P_c = 0.19372). All four roots of the numerator of P′ are real: −0.4988, 0.7579, 1.5729, 20.2402 (in units of b).
  - p_s ≤ 0 or p_s ≥ P_max leaves at most two roots in (b, ∞), with P − p_s of one sign between them, so the area is not 0.
  - On (0, P_max) the equal-area function F(p) = ∫_{v₁}^{v₃}(P − p) has dF/dp = −(v₃ − v₁) < 0, so it has one zero. A 499-level scan finds exactly one sign change in each fluid.
- **κ that returns ω = 1 exactly:** κ* = 1.888080109. κ(1) − κ* = −0.0101. dω_out/dκ ≈ 0.79, so the 3-decimal window corresponds to ±6.3e-4 in κ.

**Context, ω_in → ω_out** (SRK; Soave 1972 κ vs Graboski–Daubert 1978 κ):

| ω_in | 0 | 0.2 | 0.5 | 0.8 | 1.0 | 1.5 | 2.0 |
|---|---|---|---|---|---|---|---|
| Soave 1972 | 0.00013 | 0.20018 | 0.50015 | 0.79727 | **0.99203** | 1.4593 | 1.8850 |
| GD 1978 | 0.00336 | 0.20113 | 0.49937 | 0.79724 | 0.99414 | 1.4734 | 1.9219 |

Inside Soave's fitted range (0 to 0.5) the error is 1 to 2e-4, which is fit residual. Beyond that range the error grows: −0.0027 at 0.8, −0.0080 at 1.0, −0.041 at 1.5. ω_out < ω_in means the predicted p_s is too high, so heavy compounds come out too volatile.

## 2. Attack on the statements
1. **Formula.** `0.480 + 1.574 * 1 - 0.176 * 1 ^ 2` parses as (0.480 + 1.574·1) − 0.176·(1²) = 1.878, with signs + and −. The rest matches the module doc:
   - α = (1 + κ(1 − √(7/10)))² multiplies `ac`;
   - T = 7/10·T_c;
   - P_c = `cubicP R ac b 1 0 Tc vc` (α(T_c) = 1);
   - u = 1, w = 0 gives RT/(v−b) − a/(v² + bv).
2. **Hypotheses.** Each of `hac`, `hb`, `hvc` and `hc` blocks a real junk counterexample. `hl` does not; it is redundant.
   - **`hac`**: a_c = 0 together with `hc` forces R·T_c = 0. Then P ≡ 0, any v_l < v_g with p_s = 0 is a Maxwell state, and p_s/P_c = 0/0 = 0. Only a_c = 0 is junk. With a_c < 0 the isotherm is minus an ordinary SRK isotherm, the conditions are linear in P, and the conclusion holds (route B, fluid 4). `a_c ≠ 0` would be enough. No change needed.
   - **`hvc`**: at v_c = b, P is not differentiable, so `deriv` = 0 and `deriv ∘ deriv` = 0, and `hc` holds for any T_c with R·T_c ≠ 0. Then P_c = −a_c/(2b²) < 0, while the genuine p_s at 0.7 T_c is positive, so the ratio is negative.
   - **`hb`** (new relative to PR78): take b = −1, R = T_c = a_c = 1, v_c = 0 > b. Then v = 0 is a pole of a/(v² + bv), so the junk derivatives make `hc` hold, and P_c = R·T_c/(−b) − a/0 = 1. P = 0 at 0.7 T_c has roots v_l = −0.6034 > b and v_g = 4.0428. The interval [v_l, v_g] straddles the poles 0 and 1, so the integral is non-integrable and Lean takes it as 0 = 0·(v_g − v_l). This gives a Maxwell state with p_s/P_c = 0. So `hb` is needed, in both theorems.
   - **`hl`** (b < v_l) **is logically redundant.** Every way to violate it fails (`srk_hypotheses.py`):
     - If [v_l, v_g] contains a pole (v = −b, 0 or b), the integral is 0, so p_s = 0 and P(v_l) = 0. The two roots of P = 0, the quadratic R T v(v+b) = a(v−b), are 1.2270b and 9.8090b, both > b. The junk values P(b), P(0) and P(−b) are nonzero.
     - Otherwise v_l and v_g lie in one interval: (−∞, −b), (−b, 0) or (0, b).
       - On (−∞, −b), P′ < 0 because 2v + b < 0, so P = p_s has at most one root there.
       - On (−b, 0) and (0, b), P tends to the same infinity at both ends and has one stationary point, so P = p_s has at most two roots there, with P − p_s of one sign between them. The area cannot be 0: the scan over 1602 levels gives a minimum relative residual of 0.024.
     - Unlike the PR78 report's §2.2 justification, v_l < b < v_g is **not** a counterexample here. The same check for PR78 gives P = 0 roots 1.209b and 10.557b, both > b, so that report's sentence on `hl` looks wrong too. I did not fully check the PR case.
     - Keeping `hl` is harmless. Dropping it is a strengthening that costs the case analysis above. In `srk_omega1_exists`, `b < vl` is in the conclusion, where it strengthens the statement.
   - **Signs of R and T_c.** `b < vc` with `isCritical_iff` forces v_c/b = 1/(2^{1/3} − 1) (the single real root of x³ − 3x² − 3x − 1) and R·T_c > 0 when a_c > 0. Not assuming a sign is correct: route B with R = −1, T_c = −0.2027 reproduces every digit.
3. **Not vacuous.** Route B gives explicit witnesses, e.g. (R, a_c, b) = (2.5, 7, 0.3), T_c = 1.891651, v_c = 3.847322b. Both conjuncts are informative. As with PR78, given p_s/P_c > 0, conjunct 2 implies conjunct 1, since ω ∈ [0.9915, 0.9925] ⇔ p_s/P_c ∈ [0.010174, 0.010198]. Conjunct 1 still excludes p_s/P_c < 0, because `logb` uses \|x\|. Harmless.
4. **The claim depends on the exact coefficients.**
   - Graboski–Daubert coefficients give ω_out = 0.99414, which rounds to 0.994: the claim would be FALSE.
   - My least-squares reconstruction of Soave's procedure (§3) gives 0.479902 + 1.57239ω − 0.173685ω². At ω = 1 that yields 0.992513, just outside the window.
   - The literal is the published one, so it stands. Any prose or transcription must keep 0.176, not a refit.

## 3. Transcription: coefficients confirmed; ω = 1 is an extrapolation
Every source below was seen in raw form:
- **thermo (C. Bell), raw `thermo/eos.py`, class SRK.** Docstring "m = 0.480 + 1.574ω − 0.176ω²"; code `self.m = 0.480 + 1.574*omega - 0.176*omega*omega`. Cites Soave, Chem. Eng. Sci. 27(6) 1197–1203 (1972), doi 10.1016/0009-2509(72)80096-4. Class APISRK uses Graboski–Daubert `0.48508 + 1.55171*omega - 0.15613*omega*omega`.
- **CoolProp, raw `src/Backends/Cubics/GeneralizedCubic.cpp`, `SRK::m_ii`.** `0.480 + 1.574 * omega - 0.176 * omega * omega`, with the comment "Values from Soave, 1972".
- **pychemqt, raw `lib/EoS/Cubic/SRK.py`.** `0.48 + 1.574*cmp.f_acent - 0.176*cmp.f_acent**2` (Eq. 15). Cites "Chem. Eng. Sci. 27 (1972) 1197-1203".
- **Wikipedia, "Cubic equations of state", raw wikitext.** The main SRK display uses Graboski–Daubert, then: "The original formulation from Soave is: … 0.480 + 1.574 ω − 0.176 ω²".
- **Variants.** 0.48 versus 0.480 is the same value. The Penn State PNG 520 course page prints Graboski–Daubert (0.48508/1.55171/0.15613) under the heading "SRK EOS (1972)", which is a mislabel.
- **Primary source not read.** The publisher copy is paywalled. Third-party copies exist, but I did not download them.
- **Fit range: ω = 1 lies outside it.** Piña-Martinez, Privat, Jaubert & Peng, Fluid Phase Equilib. 485 (2019) 264–269, doi 10.1016/j.fluid.2018.12.007, read on the ScienceDirect page: "In 1972, Soave [2] assumed ω values ranging from zero to 0.5 with a step of 0.05. For each of these eleven ω values, he determined the corresponding m values enabling to exactly reproduce reduced vapor pressures at Tr = 0.7".
  - So within [0, 0.5] self-consistency holds by construction, up to fit residual.
  - At ω = 1 the formula is extrapolated to twice the fitted range.
  - My reconstruction (`srk_refit_soave.py`) returns 0.4799 / 1.5724 / −0.1737. That is close to the printed values but not identical: the printed κ sits 1.5 to 4.7e-4 above the exact κ* at all 11 nodes, consistent with Soave's 1972 numerics or constants. This is an independent check that the printed numbers are the Tr = 0.7 self-consistency fit.

## 4. Prior art
- **Qualitative answer in print.** Three sources:
  - Piña-Martinez et al. 2019, above: the original fit uses only ω ≤ 0.5. The abstract says the updated SRK m(ω) gives "A substantial improvement … for heavy molecules with an acentric factor larger than 0.9".
  - Soave, Fluid Phase Equilib. 84 (1993) 339–342, "Improving the treatment of heavy hydrocarbons by the SRK EOS" (bibliographic record and abstract only). It proposes a new α to extrapolate heavy-hydrocarbon vapour pressures more reliably than the original SRK.
  - Graboski–Daubert (1978) refit m(ω) on API data.
  - Together these say that the original correlation is reliable only up to ω ≈ 0.5 and degrades for heavy compounds. That the extrapolated formula fails to reproduce ω itself follows directly from Soave's construction and the fit range.
- **Exact figure not located.** No source I found prints ω_out(SRK, ω = 1) ≈ 0.992, a shortfall of 0.008, or κ*(1) = 1.8881.
- **Classification:** qualitative answer in print (fit range ω ≤ 0.5, poorer for heavy compounds); exact figure not located. Not checked: Soave 1972 itself, which may show m(ω) beyond 0.5, and the full text of Piña-Martinez 2019, which may tabulate it.

## 5. Verdict: STANDS-WITH-CORRECTIONS
1. **The statements stand as frozen and are true.** p_s/P_c = 0.0101851 rounds to 0.0102; ω = 0.992034 rounds to 0.992. The binding margin is 1.09e-5 in p_s/P_c, on the ω ≤ 0.9925 side. Uniqueness is genuine.
2. **Prose (fit range).** The module doc says κ(ω) was "fitted to vapour pressures at T_r = 0.7". Add: "at eleven ω from 0 to 0.5 (Piña-Martinez et al. 2019); ω = 1 is an extrapolation". Also say that inside the fitted range SRK returns ω to within 2e-4 (table in §1). Without this, the headline reads as a defect of the correlation rather than of extrapolating it.
3. **Bookkeeping.** Record this as a certified known effect, not a new result: "qualitatively in print (fit range, heavy-compound deficiency); the value 0.992 was not located in print".
4. **Prose (variants).** Add one line saying Graboski–Daubert (0.48508/1.55171/0.15613), which Wikipedia's main SRK formula and some course notes use, gives 0.994, and that this statement uses Soave's original coefficients (thermo, CoolProp, pychemqt, Wikipedia "original formulation").
5. **Optional, not required.**
   - `hl` is redundant (§2.2): a stronger true statement drops it.
   - `hac` could be `ac ≠ 0`.
   - A tighter true rounding is available: ω = 0.9920 to 4 decimals, margin 1.6e-5.
   - Side note for the PR78 record: the junk example given there for `hl` (v_l < b < v_g, p_s = 0) does not exist, because both roots of P = 0 are > b.
