# Referee report (annex XL fidelity audit): Work/Chemistry/CubicEOS.lean

**Verdict: STANDS-WITH-CORRECTIONS.** All six statements are true, none is vacuous or trivially true, and every RoundsTo claim holds. The corrections concern scope and prose. Computations: /tmp/referee_eos (sympy 1.14, mpmath 1.3).

## 1. Physics fidelity
1.1 (u,w) = (0,0), (1,0), (2,−1) give vdW, RK/SRK and PR in the Reid–Prausnitz–Poling u–w form.
1.2 `IsCriticalIsotherm` (P_v = P_vv = 0 at fixed T) is the textbook condition. It omits stability (P_vvv < 0) and P_c > 0, but I sampled 3000 cases with u > −2 and 1+u+w > 0, and every solution had P_c > 0 and P_vvv < 0. Nothing false is claimed.
1.3 Using a = a(T) is faithful: derivatives in v at fixed T do not see α(T). Ω_a = a(T_c)P_c/(RT_c)² and Ω_b = bP_c/(RT_c) are the textbook definitions (Soave: a_c = a(T_c) with α(T_c) = 1; PR: a(T_c); RK: a·T_c^{-1/2}). **Correction A:** `exists_unique_critical` covers only constant `a`. With α(T), uniqueness of T_c is a separate fixed-point equation that is not proved here. Do not claim the file settles existence and uniqueness for SRK or PR with α(T). Theorem 4 ("every critical point") is fine.
1.4 Hypotheses: `isCritical_iff` needs only D(v) ≠ 0, so D > 0 is harmless. Given u > −2, D is increasing on [b,∞), so `hD` ⇔ 1+u+w > 0. **Correction B (cosmetic):** state it as `0 < 1+u+w`. u > −2 is sufficient but not necessary. Take u = −3, w = 3: the cubic x³−3x²+3 has two roots above 1, x = 1.347 and x = 2.532, and only the second gives T > 0 (2x+u = −0.305 at the first). So u > −2 is needed for the "exactly one root" lemma. It covers all standard EOS.

## 2. Mathematical truth (independent sympy)
2.1 P_v·(v−b)²D² = −[RT D² − a(v−b)²(2v+ub)] exactly. With P_v = 0, the numerator of P_vv is −2a·(v³ − 3bv² − 3(u+w)b²v − (u²+uw−w)b³). So `isCritical_iff` holds in both directions with no hidden side condition.
2.2 critCubic(1) = −(u+2)(1+u+w) < 0, so a root above 1 exists. The roots sum to 3, so three roots above 1 are impossible. The root is unique.
2.3 Values (b = a = 1):

| EOS | x_c | Z_c | Ω_b | Ω_a |
|---|---|---|---|---|
| vdW | 3 | 0.375 | 0.125 | 27/64 |
| RK | 3.847322101863073 | 1/3 | 0.08664034996495772 | 0.4274802335403414 |
| PR | 3.951373035591441 | 0.3074013086987038 | 0.07779607390388846 | 0.4572355289213822 |

For RK, Ω_b = (2^{1/3}−1)/3 and Ω_a = 1/(9(2^{1/3}−1)).
2.4 RoundsTo margins (tolerance minus |x−d|):

| Claim | Margin |
|---|---|
| RK Ω_b | 4.65e-6 |
| RK Ω_a | 4.77e-6 |
| PR Z_c (k = 4) | 4.87e-5 |
| PR Ω_b | **1.07e-6** |
| PR Ω_a | **5.3e-7** (tight) |

All hold. The exact claims (vdW; RK Z_c = 1/3) are true.

## 3. Lean pitfalls
v > b and D(v) > 0 avoid both poles. `deriv (deriv p) v` depends only on the germ of p near v, where p is smooth, so there are no junk zeros. For vdW, RK and PR, D > 0 is automatic for v > b. ∃! over pairs (T, v) is correctly quantified. The constants theorems are non-vacuous, because a critical point exists with T = a(v−b)²(2v+ub)/(RD²) > 0. Decimal literals are real numbers.

## 4. Prior art and printed values
4.1 The u–w family and its Ω-constants are standard: RPP 4th ed. 1987 (IDAES docs cite it for the table), Schmidt & Wenzel 1980 (Chem. Eng. Sci. 35:1503), Abbott 1973/1979, and the δ1/δ2 form in Michelsen & Mollerup. I found no published proof that the root x > 1 is unique; it appears to be folklore. None of these books was checked in a primary source.
4.2 Printed constants:
- **Soave 1972** (Chem. Eng. Sci. 27:1197; scanned primary PDF, OCR): a_c = **0.42747** R²T_c²/p_c and b = 0.08664 RT_c/p_c. **0.42747 is a truncation** of 0.4274802 and fails RoundsTo(·, 5) by 5.2e-6. **Correction C:** write "0.42748 (Soave printed 0.42747)".
- **Peng–Robinson 1976** (Ind. Eng. Chem. Fundam. 15:59; OCR of an uploaded copy, close to primary): 0.45724, 0.07780 and Z_c = 0.307. All are correct roundings.
- **Redlich–Kwong 1949** (Chem. Rev. 44:233): commonly quoted as 0.4278 and 0.0867. **Not verified**: the primary-PDF fetch was blocked. If these are the printed values, both are mis-roundings. The correct 4-place values are 0.4275 and 0.0866; 0.4278 misses by 3.2e-4 (probably 0.42748 with a digit dropped) and 0.0867 misses by 6.0e-5. **Correction D:** mark the attribution as unverified.

## Summary
1. All theorems true. Tightest margins: PR Ω_a 5.3e-7, PR Ω_b 1.07e-6.
2. Correction A: uniqueness is proved for constant `a` only.
3. Correction B: `hD` ⇔ 1+u+w > 0 (optional restatement).
4. Correction C: Soave printed the truncated value 0.42747.
5. Correction D: the RK 1949 values 0.4278 and 0.0867 are unverified and would be mis-roundings.
6. No Lean junk-value, quantifier or vacuity defects.
