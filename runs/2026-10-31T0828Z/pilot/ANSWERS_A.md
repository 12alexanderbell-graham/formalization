# Answers (reviewer pilot, set A). Only odd items 01..47 were supplied; even rows N/A.

| Item | Q1 | Q2 | Q3 | Q4 | Defect found (what, MATERIAL/MINOR) | confidence |
|---|---|---|---|---|---|---|
| 01 | YES | YES | YES | YES | none (Milne: true D4_A,y=0, printed gives -1/120, so remainder = y^5/120) | high |
| 03 | YES | YES | YES | YES | none | high |
| 05 | YES | YES | YES | YES | none; all four coefficients verified symbolically; printed (21),(22) deviations match paper | high |
| 07 | NO (as stated: vacuous) | NO | CANNOT TELL | YES | MATERIAL: hypotheses h1 `0<1+u+w` and h2 `u+w<-1` contradict each other, so the theorem is vacuous (and the "non-vacuity witness" cannot exist). The underlying fact (exactly one root >1) is true under -2<u, 0<1+u+w alone | high |
| 09 | YES | YES | YES | YES | MINOR: non-vacuity witness named `printedDA4z_fails_past` (a d_A theorem) | high |
| 11 | YES | YES | YES | YES | MINOR: no docstring | high |
| 13 | YES | YES | YES | YES | none (roots 0.599, 0.731 verified; difference printed-correct factorises exactly as claimed) | high |
| 15 | YES | YES | YES | YES | MINOR: no docstring | high |
| 17 | YES | YES | YES | YES | none (printed R in (11.31) differs from the true one by -2(3j^2q+10j^2+11jq^2+4jq+90q^2)) | high |
| 19 | YES | YES | YES | YES | none | high |
| 21 | NO | NO | CANNOT TELL (a2,a3 match Lusso Eq. 8) | NO | MATERIAL: bound 9/10 mag at z=3 is false; true gap over Omega in [0.2,0.4] is 0.115..0.175 mag (min 0.1153 at Omega=0.35). Correct bound would be 1/10 (more than 0.1 mag). Plain text and Lean both wrong | high |
| 23 | YES | YES | YES | YES | none (hand-checked equivalence FriedmannCPL <-> IsFlatCPL) | medium-high |
| 25 | YES | YES | YES | YES | MINOR: non-vacuity witness name is `lumDist_y_third_order` | high |
| 27 | YES | YES | YES | YES | none (min gap 0.368 mag at z=7 > 0.3) | high |
| 29 | NO | NO | YES | YES | MATERIAL: plain claim says "FLRW of any spatial curvature K", but the Lean statement uses `lumDistFlat` and plugs Omega=1 into D2 (flat only); no K in the statement. For K != 0 the flat-Omega statement would be false | medium-high |
| 31 | YES | YES | YES | YES | none (0.27737 -> 0.277; -5.25 exact) | high |
| 33 | YES | YES | YES | YES | none (cubic and RT-equation re-derived by sympy) | high |
| 35 | YES | YES | YES | YES | none (l0 = 0.80855 -> 0.809; printed with missing 9 gives -0.90608 -> -0.906) | high |
| 37 | YES | YES | YES | YES | none | high |
| 39 | YES | YES | YES | YES | none (flat de Sitter: true D2=3, printed -3) | high |
| 41 | YES | YES | YES | YES | MINOR: non-vacuity witness named `lumDist_z_fifth_order`; "Headline. Same for d_A." is not self-contained wording | high |
| 43 | YES | YES | YES | YES | none (true D4y - printed = x^2/120 + 5qx/12, x = Omega-1, exactly hD) | high |
| 45 | YES | YES | YES | YES | none | high |
| 47 | YES | YES | YES | YES | MINOR: no docstring | high |

## Defects

### Item 07 (MATERIAL, vacuous hypotheses)
`critCubic_existsUnique (u w) (hu : -2<u) (h1 : 0<1+u+w) (h2 : u+w < -1)`: h1 says u+w > -1, h2 says u+w < -1. Unsatisfiable, so the theorem proves nothing. Numerical scan (100k random (u,w)): with -2<u and 1+u+w>0 there is always exactly one root >1 (so the claim is true without h2; without hu or h1 the count becomes 0 or 2 in some regions, so those two are the real conditions; h2 is spurious).

### Item 21 (MATERIAL, wrong number)
Using Lean's definitions (logPolyDL3 with lusA2 = ln10(3/2-3/4 Ω), lusA3 = ln10^2(9/8 Ω^2-2Ω+7/6); I verified these equal the exact ln(1+z) expansion coefficients of flat ΛCDM and match Lusso et al. 2019 Eq. 8), mpmath gives 5 log10(d_exact/d_poly) at z=3: Ω=0.2: 0.1746; 0.25: 0.1382; 0.3: 0.1203; 0.35: 0.1153; 0.4: 0.1194. Min on [0.2,0.4] is 0.1153. The claim "> 0.9 mag" (Lean `9/10 <`) is false by a factor ~8; consistent with the original being 1/10. (Lusso/RL19 say the cubic reproduces LCDM to z>5 within a few percent, incompatible with 0.9 mag at z=3.) At z=7 the min is 0.3683 > 0.3, so item 27 is fine.

### Item 29 (MATERIAL, claim/statement mismatch)
Plain words: "FLRW of any spatial curvature K". Lean: `remainderY correctD2y a t0 t` = H0*lumDistFlat - seriesY (correctD2y q j 1) ..., i.e. K=0, Omega0=1 hard-wired, no K variable. Cattoën-Visser Eq. (52) has Omega0 in D2 and is curvature-general, but this theorem is the flat case only (item 25 correctly says "flat FLRW"). A reader would believe a curvature-general theorem was certified.

### Checks that came out clean (evidence)
- Flat ΛCDM/CPL cosmographic coefficients (item 05, 35): recursion C_{n+1}=H C_n-(1+z)H C_n' symbolically equals every printed-corrected coefficient; paper arXiv:1104.3096 Eq. (22) has (7-Ω)w_a without the 9, (21) has dropped minus before 27/4; toy values 0.245,-0.93,-0.41 confirmed in the paper.
- Bamba et al. (10.38)-(10.63) series recomputed for general K: DL1-3z, DA1-3z printed correct; D4_L,z and D4_A,z miss +k^2/120 (items 09, 11, 41); D2_L,y printed has wrong overall sign (29, 39); D3_L,y needs +(Ω-1)(3q-2)/6; D4_L,y needs + (Ω-1)^2/120 + 5q(Ω-1)/12 (item 43); D3_A,y needs +q(Ω-1)/4 and D4_A,y printed differs by x(j/12-3q^2/8+q/6+x/120) (items 01, 47).
- Cattoën-Visser dQ: (1-y)^{3/2}-expansion gives 1/24 (item 25); printed Eq. (59) has 1/12.
- F(R) (items 13, 15, 17, 31): I re-derived F(R0), F'', F''' from Friedmann + master equation and its derivative with a 5-jet of a(t); eta20Of, eta30Of, P0..Q3 match, but printed R (11.31) does not (true R = -(3j^2q+10j^2-jl+11jq^2+4jq-2js-18j+lq+2l+3q^4+34q^3+6q^2 s+180q^2+50qs+246q+3s^2+40s+104)... difference from printed = -2(3j^2q+10j^2+11jq^2+4jq+90q^2)). d eta20/d eps and d eta30/d eps at 0 equal correct20/correct30; printed20-correct20 = 8(27Ω²+24Ω-32)(54Ω²-29Ω-2)/[...] confirming item 13's exception set. Paper (11.13) also has a sign error in the 2(q0+4)j0 term (true R''' = -6H0^5[l-s-2(q+4)j-6(3q+8)q-24]... not used by Lean items).
- Hypotheses and sign conventions of FRSecondEq/MasterEq/FriedmannEq checked against De Felice-Tsujikawa under R -> -R (item 37, 17).
