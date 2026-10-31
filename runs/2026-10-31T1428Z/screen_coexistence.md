# SCREEN: van der Waals vapour–liquid coexistence (p_s/P_c, v_l/v_c, v_g/v_c, ω, parametric and asymptotic forms)

Run 2026-10-31T1428Z. Comparison key: the 40-digit Maxwell table in `scripts/vdw_table.out`.

How the checks were done:
- Independent Maxwell solver (Newton on P(v_l)=P(v_g) plus equal area, 50 digits). It reproduces every key entry to within 2.4e-15 relative, which is the key's own rounding.
- Separate fugacity-equality solver for general two-parameter cubics. It gives vdW p_s(0.7) = 0.200458467081936, identical to the key.
- sympy series for every printed asymptotic formula. Low-T checks use the closed-form inversion y(τ) = (27+16τ+27√(1−32τ/27))/(32τ) of τ = 27(y−1)/(4(2y−1)²).

Scripts are in `/tmp/screen_work/` (outside the repo): `vdwlib.py`, `check_*.py`, `sym_*.py`, `cubics.py`. Downloads and renders are in `/tmp/screen/`. Crops are in `typeset/`.

Not screenable:
- Lekner, Am. J. Phys. 50, 161 (1982) is paywalled. A third-party copy was blocked, so it was not used. Lekner's formulas were checked through Johnston's typeset transcription (Eqs. 78–79), which reproduces the key to 1e-15.
- Berberan-Santos et al., J. Math. Chem. 43, 1437 (2008) is paywalled.

Shamsundar & Lienhard (1983) and Dong & Lienhard (1986) were read from author-hosted scans on J. H. Lienhard's University of Houston site (engines.egr.uh.edu).

## Table

| # | Source | Location | Printed value / formula | Key / exact value | Verdict | Crop |
|---|---|---|---|---|---|---|
| 1 | Johnston, arXiv:1402.1205v1 (only version) | Table IV p.36 (85 T rows, 0.99–0.15) | p_X/p_c, V_G (liq), V_C (gas), V_F, V_D, 4 s.f. e.g. 0.50: 2.779e-02, 0.4068, 4.598e+01; 0.70: 2.005e-01, 0.4672, 7.811e+00; 0.95: 8.119e-01, 0.6841, 1.727e+00 | key 0.0277887/0.406753/45.9838; 0.200458/0.467193/7.81114; 0.811879/0.684122/1.72707 | **All 340 p, V_G, V_C, V_F entries correctly rounded.** 3 of 85 V_D (gas-side spinodal) entries are 1 ulp high from double rounding (T=0.77: 2.049 vs 2.048473; 0.62: 2.823 vs 2.822473; 0.35: 5.699 vs 5.698489) | screen_johnston1402.1205v1_p36_tableIV.png |
| 2 | Johnston 1402.1205v1 | Table VI p.38 (45 rows, y=10^(m/20)) | τ_X, p_X, dp/dτ, ΔV, n_g, n_l, Δn, n_ave, ΔS, L (5 s.f.) | independent Maxwell solution at τ(y); ΔS=ln[(3v_g−1)/(3v_l−1)]; L=τ(dp/dτ)ΔV | **All 450 entries within ½ ulp** | screen_johnston1402.1205v1_p38_tableVI.png |
| 3 | Johnston 1402.1205v1 | Eqs. (78a,b), (79a–l) p.17 (Lekner parametrisation) | f=(y cosh y−sinh y)/(sinh y cosh y−y), g=1+2f cosh y+f², τ=27f(f+cosh y)/(4g²), p=27f²(1−f²)/g², V_g,l=(1+e^{±y}/f)/3, dp/dτ=16y(y coth y−1)/(sinh2y−2y) | key at all 7 T_r | **Exact** (≤2.4e-15 vs key, 1e-50 internal); (78a)≡(78b) | screen_johnston1402.1205v1_p17_eq79_lekner.png |
| 4 | Johnston 1402.1205v1 | Eqs. (82a,b), (83a–f, i–l) p.19 (near-critical series) | e.g. p−1 = −4t+24t²/5−816t³/875; y = 3t^{1/2}+81t^{3/2}/50+50403t^{5/2}/35000 | sympy series of Lekner forms | **Agree** term by term | screen_johnston1402.1205v1_p19_eq83g-h.png |
| 5 | Johnston 1402.1205v1 | Eq. (83g) p.19 | v_0X = 4y/3+16y³/45+**32**y⁵/1575 = 4t^{1/2}+294t^{3/2}/25+**196081**t^{5/2}/8750 | 4y/3+16y³/45+**64**y⁵/1575 = … +**239281**t^{5/2}/8750 | **ERROR**: last coefficient (y-form and t-form consistent with each other, both wrong). Size ≈4.94 t^{5/2} (0.003 at T_r=0.95) | same |
| 6 | Johnston 1402.1205v1 | Eq. (83h) p.19 | V̂_X = 2+4y²/5+68y⁴/525+**32y⁵/1575** = 2+36t/5+15984t²/875+**864t^{5/2}/175** | V_g+V_l is even in y: 2+4y²/5+68y⁴/525+O(y⁶) = 2+36t/5+15984t²/875+871056t³/21875 | **ERROR**: spurious odd term | same |
| 7 | Johnston 1402.1205v1 | Eqs. (86), (87), (88a), (88e) p.20 (low-T) | τ=27/(16y)−27/(64y³)−27/(64y⁴); y=27/(16τ)−4τ/27−64τ²/729; V_l=1/3+8τ/81+128τ²/2187+2560τ³/59049 | sympy | **Agree** | screen_johnston1402.1205v1_p20_eq88.png |
| 8 | Johnston 1402.1205v1 | Eq. (88c) p.20 | p̂_X = (1594323/(256τ³)+98415/(64τ²)−5103/(4τ)) e^{−27/(8τ)} | p̂_X = (27 − 8τ − 32τ²/27 − 1280τ³/2187 …) e^{−27/(8τ)}; at τ=0.2: exact 1.18909e-6, correct series 1.18911e-6, (88c) gives 3.80e-2 | **ERROR, gross**: prefactor wrong by factor ~10⁴–10⁵ at τ=0.1–0.3 (the left-hand closed form 108(y−1)²e^{−2y}/(2y−1)² is right) | same |
| 9 | Johnston 1402.1205v1 | Eq. (88d) p.20 | V̂_g = (8τ/81+**128**τ²/2187+**2560**τ³/59049)e^{27/(8τ)} | (8τ/81+**64**τ²/2187+**256**τ³/19683+…)e^{27/(8τ)}; τ=0.3: exact 2505.86, correct 2507.40, (88d) 2772.88 | **ERROR**: drops the e^{−2δy} correction (the text says only the leading y is put in the exponent). 11% error at τ=0.3 | same |
| 10 | Johnston 1402.1205v1 | Eq. (88f) p.20 | n̂_g = 6(27/(16τ)−1−4τ/27−64τ²/729)e^{−27/(8τ)} | (81/(8τ) − 3 − 4τ/9 − 160τ²/729)e^{−27/(8τ)} | **ERROR** (same cause; −6 should be −3) | same |
| 11 | Johnston 1402.1205v1 | Eqs. (88g), (88h) p.20 | n̂_l = 3−8τ/9 **+**64τ²/243−…; n̂_ave = 3/2−4τ/9 **+**32τ²/243−… | n̂_l = 3−8τ/9 **−**64τ²/243−1024τ³/6561; n̂_ave = 3/2−4τ/9 **−**32τ²/243−512τ³/6561 | **ERROR**: sign of τ² term (contradicts the paper's own (88e)) | same |
| 12 | Johnston 1402.1205v1 | Eq. (88b) p.20 | L/(p_cV_c) = 9−64τ²/81−1024τ³/2187−**8192**τ⁴/59049 | … −**20480**τ⁴/59049 | **ERROR** in τ⁴ coefficient (size 0.2τ⁴) | same |
| 13 | Johnston 1402.1205v1 | Eq. (77) + Table II p.17 (9th-order fit of ln p in 1/τ) | c0…c9 | max rel. error 4.9e-4 on τ∈[0.15,0.99]; implied ω = −0.30197 (vs −0.302024) | Approximation only; fine as a fit | (text-layer only, not a candidate) |
| 14 | Cardoso, Ibarra-Sierra, Sandoval-Santana, Kunold, arXiv:2601.04296v1 | Table 2 p.19 | Maxwell p_s: 0.504, 0.647, **0.812** (T=0.85, 0.90, 0.95); v_r2 = **1.144**, 1.091, **1.043** | p_s 0.504492, 0.646998, 0.811879; middle root at exact p_s: 1.14531, 1.09053, 1.04247 | p_s correct. v_r2 at 0.85 and 0.95 are 1 ulp off because they were computed from the 3-digit p_s (at p=0.504: 1.14442; at 0.812: 1.04294) | screen_cardoso2601.04296v1_p19_table2.png |
| 15 | Cardoso et al. 2601.04296v1 | Table 3 p.21 | Maxwell p_s(0.95) = **0.811**; p_s0=t⁴, p_s1, p_s2 = 0.522/0.496/0.509 etc.; %err 3.57, 1.59, 0.99 … | 0.811879 → 0.812 (contradicts their Table 2); approximations reproduce (0.52201, 0.49597, 0.50922); exact %err 3.47, 1.69, 0.94 | **Truncation** of p_s(0.95). %err values are computed from rounded inputs | screen_cardoso2601.04296v1_p21_table3.png |
| 16 | Cardoso et al. 2601.04296v1 | Eqs. (68), (70), (76), (77), (78) | dp/dt = p/t+3/(v_l v_g t); p_s2 = 16t[15 exp(9/√2 (t^{−1/2}−1))+1]^{−1} | numeric dp/dt; sympy ODE residual | **Agree**: (68)/(70) exact identities; (78) solves (77) exactly. The text layer reads 25 for 2⁵ in (77); the typeset shows 2⁵ | screen_cardoso2601.04296v1_p21_eq78.png |
| 17 | Liu, arXiv:2208.10485v1 | Eq. (13) p.4; (A5)–(A8), (A14), (A15) p.15–16; (9)–(11) | ρ_M = 1−4t/5−256t²/875−272t³/3125+0.06976t⁵+0.20804t⁷; ρ_g = 1−2t^{1/2}+2t/5+13t^{3/2}/25+128t²/875; v_L = 9/(16T)[1−(1−32T/27)^{1/2}]; v_V = (3v_L−1)/3·exp(1+3v_L/(3v_L−1)) | sympy series; exact | Series terms **exact**. Eq. (13): AAD 0.0037% on 0.30–0.99 (claimed 0.003%), max 0.07% at 0.30. (A14)/(A15) rel. error 4e-12 (T=0.1), 2.4e-5 (0.2), 2.9e-3 (0.3). (8T=∏(3−ρ_i), order-parameter formula exact) | screen_liu2208.10485v1_p4_eq13.png, screen_liu2208.10485v1_p16_eqA14-A15.png |
| 18 | Liu, arXiv:2010.14739v1 | Table S1 p.12 | "Exact" v_l, v_g: 0.4: 0.386408, 203.629; **0.46: 0.398100, 77.220**; 0.55: 0.418840, 26.610; 0.7: 0.467193, 7.8111; 0.8: 0.5174093, 4.1725 | 0.46: v_l = **0.398074**, v_g = 77.2194; others correct | **ERROR** at T_r=0.46: "exact" v_l off by 26 units in the last place (the true value appears in their "analytic" column); v_g 1 ulp high | screen_liu2010.14739v1_p12_tableS1.png |
| 19 | Liu 2010.14739v1 | p.12 text, T_r=0.35 | v_l=0.377716, v_g=592.607, P=0.001567305; (S7)=0.377720, (S8)=**598.776**; P(analytical)=0.001567304; P(0.46)=0.0154512 exact / 0.0154511 analytic | 0.3777161, 592.6073, 0.00156730483; (S7) 0.3777204, (S8) 598.7767; P(0.46) 0.01545122 | Agree, except (S8) is truncated (598.777). P(analytical) is reproduced only with the Eq.(14) branch (0.0015673045); with the (S7)/(S8) volumes Eq.(15) gives 0.00156722 | screen_liu2010.14739v1_p12_T035values.png |
| 20 | Liu 2010.14739v1 | Eq. (14) + Table 1 p.5 | 𝒮 = ln(3v_M−1) = Σ_{0..5} a_i T^i + a_6 ln T, a = (2.966426, −5.641512, 6.539612, −4.763370, 1.920965, −0.328973, −0.386595) | rebuilt analytic column: 0.46 → v_l 0.398074, v_g 76.966, P 0.0154511 | Transcription confirmed (reproduces their analytic column to ≤5e-3 in v_g) | screen_liu2010.14739v1_p5_eq14.png |
| 21 | Cui & Fan, arXiv:2506.20959 **v1** | Eq. (16) p.5 | 6(φ−z²)((6z−1)φ−z²)+(z−3φ)(3z−1) ln[(3φ−z)²/(z²(3z−1)²)] = 0 | residual at exact coexistence: 2.8e3 (T=0.5, z=v_l), −3.8e7 (z=v_g), 97 (T=0.7) | **ERROR in v1** (equation not satisfied by the true coexistence) | screen_cuifan2506.20959v1_p5_eq16.png |
| 22 | Cui & Fan, arXiv:2506.20959 **v2** | Eqs. (15), (16), (19), (20) p.6–7 | x=(3z_s−1)/(3z_l−1); z*=(x−1)(x−ln x−1)/[3(x+1)ln x−6(x−1)]; t*, p* closed forms | key | **Exact** (1e-48). Equivalent to Lekner with x=e^{±2y}. v2 corrects v1's Eq. (16) | screen_cuifan2506.20959v2_p7_eq19-20.png, screen_cuifan2506.20959v2_p7_eq16.png |
| 23 | Gui, arXiv:cond-mat/0404667 v1–v3 | Eq. (11) p.4 (same in v1 and v3) | P* = [3n_g*² e^{E} − **n_l*²**]/(1−e^{E}), E = 9(n_l−n_g)/(4T) − 3(n_l²−n_g²)/(8T) | correct: [3n_g² e^E − **3**n_l²]/(1−e^E) (reproduces key to 1e-12). Printed form gives 0.0218 vs 0.0869 (T=0.6), negative at 0.95 | **ERROR**: missing factor 3 | screen_gui0404667v3_p4_eq11.png |
| 24 | Gui cond-mat/0404667 | Eqs. (6)–(9) p.3, accuracy claim p.4, Eq. (12) | n_l,g* = 1+0.497s^{1.086} ∓0.56s^{1.53} ±2s^{0.5}; "(7) <0.1% for T*>0.71"; ln P* = 3.5204−3.5660/T* | (6): ≤0.07% for T*≥0.6 (claim holds); (7): 0.13% at 0.75, 0.21% at 0.90, 0.22% at 0.95; (12): −2.8% … +3.4% … −4.1% (0.5–0.99) | (6) OK. **(7) accuracy claim violated** (×2). (12) is a crude fit | screen_gui0404667v3_p3_eq6-9.png, screen_gui0404667v3_p4_accuracy_claim.png, screen_gui0404667v3_p4_eq12.png |
| 25 | James & Mathis, arXiv:1402.1435v1 | p.7, T=0.85 | ρ⁻=**0.581079**, ρ⁺=**1.488804**, ρ1*=**0.319729**, ρ2*=1.807140, p=0.504492, μ=**3.977178** | 0.5810799, 1.4888047, 0.3197300, 1.8071403, 0.5044916; μ (their Eq. 4, reduced a=3, b=1/3, R=8/3) = **−3.977179** | ρ⁻, ρ⁺, ρ1* **truncated** (1 ulp low). μ magnitude right but sign missing | screen_jamesmathis1402.1435v1_p7_T085.png |
| 26 | Shamsundar & Lienhard, Can. J. Chem. Eng. 61, 876 (1983), author-hosted scan | p.1 text | "ω = −0.302 for a van der Waals fluid, or 0.058 for a Redlich–Kwong fluid" | vdW −0.302024405; RK (α=T_r^{−1/2}) computed **0.058280** | **Agree** (both rounded) | screen_shamsundarlienhard1983_p1_omega.png |
| 27 | Shamsundar & Lienhard 1983 | Table 1 p.878, T = 0.98…0.06 (47 rows) | p_sat, v_f, v_g, h_fg, s_fg, u_fg (5 s.f.), e.g. 0.70: 0.20046, 0.46719, 7.8111, s_fg=4.0229; 0.50: 0.27789e-1, 0.40675, 45.984 | key; s_fg=2y; h=Ts; u=h−(3/8)pΔv | **All 47 p_sat agree.** 10 other cells differ only by a scan-ambiguous glyph (3↔8, 5↔6, 0↔3) and match exactly if that glyph is read the other way (e.g. v_f(0.82) 0.5305[3/8] vs 0.530581). Unresolved last-digit cells: s_fg(0.54) 5.8611 vs 5.861150 (half-ulp tie), v_f(0.22) 0.3584[5/6] vs 0.358461, v_f/v_g(0.06). Not candidates | screen_shamsundarlienhard1983_p878_table1_cols1-8.png |
| 28 | Dong & Lienhard, Can. J. Chem. Eng. 64, 158 (1986), author-hosted scan | Eq. (6) p.159; text "van der Waals value of −0.302" | ln p_r,sat = 5.37270(1−1/T_r)+ω(7.49408−11.18177T_r³+3.68769T_r⁶+17.92998 ln T_r) (fitted with the S–L vdW data included; rms 0.42% in T_r) | at ω=−0.302024: rel. error in p vs vdW: −12.9% (0.3), +12.2% (0.4), +11.1% (0.5), +4.3% (0.6), 0 (0.7), −0.2% (0.8), +1.6% (0.9), +1.7% (0.95); 1.2–1.6% in T_r at 0.3–0.5 | Internally consistent with the ω definition at 0.7. For the vdW member the error exceeds the quoted rms. Not a defect, but **not usable for vdW p_s** | screen_donglienhard1986_p159_eq6.png |
| 29 | Wikipedia "Acentric factor" (raw wikitext read via action=raw on 2026-10-31; not a stable citation; cites #26) | sentence 1 of "can be predicted analytically" para | vdW "acentric factor of about −0.302024" | −0.3020244050 | Agree (6 d.p.) | — (wikitext) |
| 30 | Giglio, Landolfi, Moro, arXiv:1602.03975v1 | p.6–7 | SRK: T_c=0.2027 a_c/(bR), P_c=0.01756 a_c/b², v_c=3.847b; PR: 0.1701, 0.01324, 3.951b; Soave α with m=0.480+1.574ω−0.176ω²; H₂ ω=−0.22 (empirical) | Ω_b/Ω_a=0.202680, Ω_b²/Ω_a=0.017560, 1/(3Ω_b)=3.84732; PR 0.170145, 0.013237, 3.95132 | Agree (PR line text-layer only). No coexistence values | screen_giglio1602.03975v1_p6_SRKcrit.png |
| 31 | Brody & Hook, arXiv:0809.1166v1 | Eqs. (134)–(135) p.24 | Landau-expanded vdW: p_s = P_c(1−4(T_c−T)/T_c), v−1 = ±2√(−t) | leading order of (83c)/(83e) | Agree to leading order only (at T_r=0.95: 0.800 vs 0.8119) | — (text layer, not a candidate) |
| 32 | Barra & Moro, arXiv:1412.1951 v1, v2 | v2 p.6 | critical point x_c=−1/(8b), t_c=27b/(8a), v_c=3b (x=−P/T, t=1/T); Rankine–Hugoniot ≡ Clapeyron | standard | Agree. No coexistence numbers | — |
| 33 | Li, Li, Mi, Li, arXiv:1701.05669v1 | — | black-hole analogue of Lekner; no vdW numbers printed | — | Screened, nothing to compare | — |

### Implied acentric factors of two-parameter cubics (computed with `cubics.py`, fugacity equality, ω = −log₁₀ p_r(0.7) − 1)

| EoS | Ω_a, Ω_b, Z_c | implied ω | printed |
|---|---|---|---|
| vdW | 27/64, 1/8, 3/8 | −0.302024404958 | −0.302 (#26, #28); −0.302024 (#29) |
| Redlich–Kwong (α = T_r^{−1/2}) | 0.42748023, 0.08664035, 1/3 | **0.0582800011** | 0.058 (#26) |
| RK form, a constant | same | −0.29357 | none found |
| PR form, a constant | 0.45723553, 0.07779607, 0.30740131 | −0.24735 | none found |
| SRK at ω_in = 0, 0.1, 0.3, 0.5 | RK constants | 0.000134, 0.100100, 0.300290, 0.500151 | none found (consistent by construction to ≤3e-4) |
| PR at ω_in = 0, 0.1, 0.3, 0.5 | PR constants | −0.002812, 0.100064, 0.301592, 0.496272 | none found |

## Candidates, ranked by consequence

1. **Johnston 1402.1205v1, Eq. (88c)**: the low-temperature saturation-pressure asymptote is wrong by a factor of about 10⁴–10⁵ (τ⁻³ prefactor instead of 27 − 8τ − 32τ²/27 − …). Anyone taking a low-T p_s from this formula gets a wrong number. The same derivation flaw (only leading y kept in the exponential) also breaks:
   - Eq. (88d) for V_g: τ² coefficient 128 → 64; 11% error at τ=0.3.
   - Eq. (88f) for n_g: −6 → −3.
   - Eqs. (88g)/(88h): sign of the τ² term.
   - Eq. (88b): τ⁴ coefficient 8192 → 20480.

   The paper's own Tables IV and VI are fully correct: 872 of 875 entries checked are within ½ ulp (Table IV: 425, Table VI: 450). The only exceptions are 3 spinodal V_D cells that were double-rounded.
2. **Liu 2010.14739v1, Table S1 at T_r=0.46**: the "exact" liquid volume is printed as 0.398100; the true value is 0.398074. A user taking it as a benchmark would be off by 2.6e-5, which is more than 20 units in the printed last place.
3. **Cui & Fan 2506.20959v1, Eq. (16)**: not satisfied by the true coexistence. v2 corrects it, and v2's closed parametric form (19)–(20) is exact. Cite v2 only.
4. **Gui cond-mat/0404667 (all versions), Eq. (11)**: a factor 3 is missing on the n_l² term, which makes the vapour-pressure expression wrong (negative at T*=0.95). Its accuracy claim for Eq. (7) (<0.1% for T*>0.71) is violated; the actual error is up to 0.22%.
5. **Johnston 1402.1205v1, Eqs. (83g)/(83h)**: the near-critical t^{5/2} coefficients are wrong. (83g) should be 239281/8750 (y⁵: 64/1575). (83h) should have no odd term. The effect is about 3e-3 at T_r=0.95.
6. **Cardoso et al. 2601.04296v1**: Table 3 gives p_s(0.95) as 0.811, a truncation (correct 0.812, which their own Table 2 prints). Table 2 v_r2 values at 0.85 and 0.95 are 1 ulp off because they were computed from 3-digit p_s. The %err columns use rounded inputs.
7. **James & Mathis 1402.1435v1**: three densities at T=0.85 are truncated rather than rounded. μ is printed as +3.977178; with their Eq. (4) it is −3.977179.
8. Liu 2010.14739v1: (S8) value 598.776 is a truncation of 598.7767. P(analytical) at 0.35 is reproducible only via the Eq.(14) branch, not via (S7)/(S8) as the text implies.
9. Shamsundar–Lienhard 1983 Table 1: all p_sat agree. A few last-digit cells cannot be resolved because of the scan quality; none is known to be wrong.

Confirmed in agreement, with no change needed:
- Key p_s, v_l, v_g at T_r = 0.5–0.95: Johnston Table IV, Shamsundar–Lienhard Table 1, Liu Table S1 (except 0.46), Cardoso p_s, James–Mathis.
- Lekner parametrisation (Johnston 79) and Cui–Fan v2 (20).
- ω_vdW = −0.302024 and ω_RK = 0.058 (0.058280).
