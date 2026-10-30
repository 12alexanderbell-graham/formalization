# Screen 2: Capozziello, D'Agostino, Luongo, "Extended gravity cosmography", IJMPD 28, 1930016 (2019)

arXiv:1904.01427 **v1** (the only version; `arxiv.org/pdf/1904.01427` serves v1, header "arXiv:1904.01427v1 [gr-qc] 1 Apr 2019").
Typeset route: PDF to /tmp/screen2_1628, 200 dpi renders, crops here (all ≤ 60 KB). Every printed formula below was read from a crop.
Conventions (checked from crops/text): metric f(R) section uses R = −6(Ḣ+2H²) (38), signature (+−−−), κ = 1, ρ_m = 3H₀²Ω_m(1+z)³; Palatini section uses R = +6(Ḣ+2H²) (231); f(T): T = −6H² (143), ρ_T = Tf′ − f/2 − T/2 (146); q, j, s as usual (162); flat throughout.
None of the items below is among F1–F11.

## Candidates (DISAGREES)

| Eq. (page) | Printed | Derived | Verdict | Consequence | Crop |
|---|---|---|---|---|---|
| (246) (p. 59), H(z) to z³ | z³/6 · (−3q₀² − 3q₀³ + j₀(3+4q₀) + s₀) | z³/6 · (3q₀² + 3q₀³ − j₀(3+4q₀) − s₀), as the paper's own (165d) and (204) print; ΛCDM check E₃ = 3Ω(27Ω²−36Ω+8)/8; EdS E₃ = −3/8 (printed +3/8) | **DISAGREES** (overall sign of the z³ term) | **Numbers affected.** (a) The z(T) inversion (264)–(269) inverts the *printed* H exactly (`check_zT.py`: z(T(z₀)) = z₀ for the printed H, 0.986 at z₀ = 1 for the correct H), so f(T) (265), ρ_T, p_T (270)–(280), Figs. 30–35 use the wrong H. (b) (262) (A,B,C) = (−5.022, 8.577, 0.532) is reproduced only with the printed sign: (−5.023, 8.580, 0.532); the correct sign gives (−5.029, 8.743, 0.490) (`repro_fT_fit.py`). (c) Sec. 6.1 also solves (210) with (246) and the Taylor fit (214), where Q = 0.369 (vs 0.039 in Sec. 7): Figs. 18–21 and λ ≳ 1196 (228) are probably affected (not reproduced). Upstream: CDL 2017, arXiv:1706.02962v1, Eq. (26) already has this sign, plus a 1/6 prefactor and −3q₀(1+q₀) for −3q₀²(1+q₀) | p59_eq246.png, p30_eqs165-168.png, p39_eq204.png, p64_eqs264-266.png, p65_eqs267-269.png, p65_eqs268-269.png, upstream_1706.02962_p4_eqs26-30.png |
| (250) (p. 60), the "G_eff = G" initial condition | df/dz\|_{z=0} = 1 | G_eff = G means f_T(T₀) = 1, so df/dz\|₀ = T_z(0) = −12H₀²(1+q₀) (= −2.61 in h units at (256)) | **DISAGREES** | **Numbers affected.** (261) (−5.024, 8.651, 0.512) is reproduced (−5.025, 8.655, 0.511) only with f_z(0) = 1 used literally. With f_z(0) = 1, f_T(T₀) = 1/T_z(0) = −0.38, i.e. G_eff = G/f_T < 0. The ODE (249) is the z-derivative of (144), so the solution satisfies (144) with an effective ρ_m0 = f₀/2 − T₀f_T(T₀) = −3.56h² instead of 3h²Ω_m = +0.415h²: the reconstructed f(z), (261)–(262), and the f(T) of Figs. 28–35 do not satisfy the paper's own Friedmann equation. (251) is derived assuming f_T = 1 and does not match (250). The correct condition gives (−5.469, −4.519, 0.065). Upstream 1706.02962v1 Eq. (31) is identical | p60_eqs247-251.png, upstream_1706.02962_p5_eqs31-32.png |
| (211) (p. 44), metric f(R) initial condition | f₀ = R₀ + 6H₀²(Ω_m0 − 1) | from the paper's (39)+(41) at z = 0 with f′(R₀) = 1 and the f″ term dropped: f₀ = R₀ + 6H₀²(1 − Ω_m0), i.e. f = R + 2Λ for R = −6(Ḣ+2H²). The paper's own (223) at f′(R₀) = 1 gives the same | **DISAGREES** (sign of the Λ term; the (−+++) formula carried into the (+−−−) section; (237) in the Palatini section, where R > 0, is correct) | The initial condition of the Padé f(R) reconstruction: Figs. 8–13, (221)–(222), λ ≳ 19.3 (227). Effect not reproduced (undetermined) | p44_eqs211-212.png, p48_eqs223-224.png |
| (249) (p. 60), ODE for f(z) | RHS = (1/H)(dH/dz)⁻¹[3H_z + (1+z)H_zz] | RHS = H (dH/dz)⁻¹[3H_z + (1+z)H_zz] (the printed form has the wrong dimension, and ΛCDM f = T + 6H₀²(Ω−1) fails it) | **DISAGREES** (misprint) | Presentational: (261) is reproduced only with the corrected RHS (printed RHS gives (−7.617, 37.29, −0.016)). Upstream 1706.02962v1 Eqs. (29)–(30) are identical | p60_eqs247-251.png |
| (248) (p. 60) | ∂/∂T = −12HH′ d/dz | ∂/∂T = −(12HH′)⁻¹ d/dz (T = −6H²) | **DISAGREES** (inverted) | Presentational, as far as checked; upstream (28) is identical | p60_eqs247-251.png |
| (166)–(168) (p. 30) | q = −1 − Ḣ/H; j = 1 + (Ḣ+Ḧ)/H²; s = 1 + (2/H²)(3Ḣ+2Ḧ) + (3H² + H⃛)/H⁴ | q = −1 − Ḣ/H²; j = 1 + 3Ḣ/H² + Ḧ/H³; s = 1 + 6Ḣ/H² + 3Ḣ²/H⁴ + 4Ḧ/H³ + H⃛/H⁴ | **DISAGREES** ((166) right only if H = 1; (167), (168) wrong even at H = 1) | Presentational: the ΛCDM values (194) that follow are correct | p30_eqs165-168.png |

## Checked and AGREE

| Eq. (page) | What | Crop |
|---|---|---|
| (163) (p. 29) | flat d_L to z⁴ (= Checked DL1z…DL3z at k = 0) | p29_eq163.png |
| (165b–d), (204) (pp. 30, 39) | H(z) coefficients E₁, E₂, E₃ | p30_…, p39_eq204.png |
| (193) c₀…c₄ (p. 35) | exact Chebyshev coefficients of (163) (also a numerical check of the projection integral (181)) | p35_eq193_c0-c4.png |
| (194)–(195) | ΛCDM q₀, j₀, s₀; values −0.55, 1, −0.35 | (text p. 35–36) |
| (199), (200), (202) (p. 37) | ρ_R11 = \|−3·8c₁/(48c₂)\| = 1/\|b₁\| from (C.1); 1.014, 1.290, 0.775 reproduced | p37_eqs199-202.png |
| (B.1)–(B.6) (p. 73) | all six Padé approximants match (163) through z^{n+m} | p73_B1-B6.png, p73_B6.png |
| (C.1), (C.3) (pp. 73–74) | equal the rational Chebyshev approximants R₁,₁ and R₂,₁ built from c₀…c_{n+m} (truncated) via (184)–(186) | p73_C1b.png, p74_C3.png |
| (207) (p. 44) | H₂₁ = [d/dz(P₂,₁/(1+z))]⁻¹ exactly | p44_eq207-209.png |
| (209) | ∂/∂R = R_z⁻¹ d/dz for R = −6(Ḣ+2H²) | p44_eqs209-212.png |
| (223) (p. 48) | f₀ = f′(R₀)(6H₀²+R₀) − 6H₀²Ω_m0 (from (39)+(41), f″ term dropped as in (211)) | p48_eqs223-224.png |
| (251), (283a,b), (237), (232), (245) | f(T₀) = 6H₀²(Ω_m0−2) given f_T = 1; ABCL c₀, c₁ consistent; Palatini f₀ from (65) at z = 0; R(z); w_eff | p60_… |
| (252)–(254) (p. 60) | f(T) cosmography q₀, j₀, s₀ in terms of Ω̃, F̃₂…F̃₄: derived from (143)–(146) | p60_eqs252-254.png |
| (264)–(269) | correctly invert the *printed* (246) (see above) | p64/p65 crops |

**AMBIGUOUS / not checked:** (201) "convergence radius" (1−q₀)/2 of the 2nd-order Taylor polynomial is undefined (a polynomial has infinite radius); 0.775 follows the printed formula. Not checked: (210) (one denominator prints H²_zz where the others have H_zz), (C.2), (C.4), (270)–(280). Table 3 spot-checked against Table 2 (H₀ 3.19 %, q₀ 16.8 %, s₀ 32.2 %, consistent within rounding).

## Lean routes for the DISAGREES rows

* **(246):** no Checked theorem states the H(z) series directly. Corollary route: `CCSLookback.lookback_fifth_order` (t_L to z⁵; dt_L/dz = 1/((1+z)H), so D₁…D₃ fix E₁…E₃), or an Einstein–de Sitter witness a = t^{2/3} (E₃ = −3/8, printed +3/8). De Sitter does not separate the two signs.
* **(211):** `FRCosmo.lcdm_witness` / `exists_LCDM_model`. `FriedmannEq` is the paper's (39)+(41) verbatim (R = −6(Ḣ+2H²), κ = 1). It gives F(R) = R + 6H₀²(1−Ω) with F′(R₀) = 1 and F″ = 0, so f₀ = R₀ + 6H₀²(1−Ω) ≠ printed for every Ω ≠ 1.
* **(248)–(250), (166)–(168):** nothing in Checked covers f(T) or these identities. Each needs a new elementary lemma, for example ΛCDM f = T − 2Λ for (249)/(250) and EdS for (167)/(168).

## Scripts (sympy/scipy; run with `python3 -I`; outputs `*.out.txt`)
`check_series.py` (H(z), d_L, (166)–(168), ΛCDM); `check_pade_cheb.py` (c_n, ρ, B.x, C.1, C.3, (207)); `check_zT.py` ((264)–(269) vs (246)); `check_fT.py` ((248)–(254)); `repro_fT_fit.py` (reproduces (261), (262)); `check_fR_ic.py` ((211) vs (223)); `crop.py`.
