import Mathlib

/-!
# Independent second transcription of printed cosmographic coefficients

Each definition below is a literal transcription of a printed coefficient, keeping the
printed grouping. Conventions:
* `q j s l` stand for `q₀ j₀ s₀ l₀`; a printed `j²` (no subscript) is read as `j₀²`.
* A line break of the form `… +` (newline) `− x` is read as `− x`.
* In Bamba et al. Sec. X (z-series), `k := K c² / (H₀² a₀²)`; the printed
  `K c² / (a₀² H₀²)` is the same quantity and is also written `k`.
* `Ω` stands for the printed `Ω₀` (Bamba et al.: `Ω₀ = 1 + K c² / (H₀² a₀²)`).
-/

namespace Checked.Trust.SecondReading

/-! ## (A) Capozziello, Cardone, Salzano 2008, arXiv:0802.1583, Appendix A, Eq. (A2)

`D(z) = (c z / H₀) {D⁰_z + D¹_z z + D²_z z² + D³_z z³ + D⁴_z z⁴}`.
Read from arXiv v2, page 16 (rendered at 300 dpi), and the repo crops
`runs/2026-10-30T0628Z/typeset/C3_ccs2008_v2_p16_A2.png`,
`runs/2026-10-30T0220Z/typeset/C3_ccs2008_A2_Dz4.png`.
Note: the arXiv v1 PDF contains no Appendix A / Eq. (A2) at all (checked the full v1
text: 15 pages, it ends with Conclusions and references); only v2 has it. -/

/-- CCS 2008 (arXiv:0802.1583v2), Eq. (A2), `D¹_z = −(1 + q₀/2)`. Page 16. -/
noncomputable def D1 (q : ℝ) : ℝ := -(1 + q / 2)

/-- CCS 2008 (arXiv:0802.1583v2), Eq. (A2), `D²_z = 1 + q₀ + q₀²/2 − j₀/6`. Page 16. -/
noncomputable def D2 (q j : ℝ) : ℝ := 1 + q + q ^ 2 / 2 - j / 6

/-- CCS 2008 (arXiv:0802.1583v2), Eq. (A2),
`D³_z = −(1 + (3/2)q₀ + (3/2)q₀² + (5/8)q₀³ − (1/2)j₀ − (5/12)q₀j₀ − s₀/24)`.
Page 16; the large parenthesis spans both printed lines. -/
noncomputable def D3 (q j s : ℝ) : ℝ :=
  -(1 + 3 / 2 * q + 3 / 2 * q ^ 2 + 5 / 8 * q ^ 3
      - 1 / 2 * j - 5 / 12 * q * j - s / 24)

/-- CCS 2008 (arXiv:0802.1583v2), Eq. (A2), printed `D⁴_z`
(three lines, no outer bracket):
`1 + 2q₀ + 3q₀² + (5/2)q₀³ + (7/2)q₀⁴ − (5/3)q₀j₀ − (7/8)q₀²j₀ − j₀ + j₀²/12
 − (1/8)q₀s₀ − s₀/6 − l₀/120`. Page 16; both repo crops agree. -/
noncomputable def printedD4 (q j s l : ℝ) : ℝ :=
  1 + 2 * q + 3 * q ^ 2 + 5 / 2 * q ^ 3 + 7 / 2 * q ^ 4
    - 5 / 3 * q * j - 7 / 8 * q ^ 2 * j - j + j ^ 2 / 12
    - 1 / 8 * q * s - s / 6 - l / 120

/-! ## (B) Bamba, Capozziello, Nojiri, Odintsov 2012, arXiv:1205.3421v3, Sec. X,
y-redshift luminosity distance, Eqs. (10.52)–(10.57), page 111 (rendered at 200 dpi),
crop `runs/2026-10-30T0628Z/screen_bamba/crop_p111_eq10.54-57_DLy.png`;
`Ω₀ = 1 + Kc²/(H₀²a₀²)` defined on page 110 (just below Eq. (10.51)). -/

/-- Bamba et al. v3, Eq. (10.53), `D¹_{L,y} = −(1/2)(−3 + q₀)`. Page 111. -/
noncomputable def D1y (q : ℝ) : ℝ := -(1 / 2) * (-3 + q)

/-- Bamba et al. v3, Eq. (10.54), `D²_{L,y} = −(1/6)(12 − 5q₀ + 3q₀² − j₀ − Ω₀)`. Page 111. -/
noncomputable def printedD2y (q j Ω : ℝ) : ℝ :=
  -(1 / 6) * (12 - 5 * q + 3 * q ^ 2 - j - Ω)

/-- Bamba et al. v3, Eq. (10.55),
`D³_{L,y} = (1/24)[52 − 20q₀ + 21q₀² − 15q₀³ − 7j₀ + 10q₀j₀ + s₀ − 2Ω₀(1 + 3q₀)]`.
Page 111. -/
noncomputable def printedD3y (q j s Ω : ℝ) : ℝ :=
  1 / 24 * (52 - 20 * q + 21 * q ^ 2 - 15 * q ^ 3 - 7 * j + 10 * q * j + s
    - 2 * Ω * (1 + 3 * q))

/-- Bamba et al. v3, Eqs. (10.56)–(10.57),
`D⁴_{L,y} = (1/120)[359 − 184q₀ + 186q₀² − 135q₀³ + 105q₀⁴ + 90q₀j₀ − 105q₀²j₀ − 15q₀s₀ +`
(newline) `− 57j₀ + 10j² + 9s₀ − l₀ − 5Ω₀(17 − 6q₀ + 9q₀² − 2j₀)]`.
Page 111. Reading choices: line break `+`/`−` read as `− 57j₀`; printed `j²` read as `j₀²`. -/
noncomputable def printedD4y (q j s l Ω : ℝ) : ℝ :=
  1 / 120 * (359 - 184 * q + 186 * q ^ 2 - 135 * q ^ 3 + 105 * q ^ 4 + 90 * q * j
    - 105 * q ^ 2 * j - 15 * q * s
    - 57 * j + 10 * j ^ 2 + 9 * s - l - 5 * Ω * (17 - 6 * q + 9 * q ^ 2 - 2 * j))

/-! ## (C) Same review, y-redshift angular diameter distance, Eqs. (10.58)–(10.63),
page 111 of v3 (rendered at 200 dpi), crop
`runs/2026-10-30T0628Z/screen_bamba/crop_p111_eq10.61-63_DAy.png`. -/

/-- Bamba et al. v3, Eq. (10.59), `D¹_{A,y} = −(1/2)(1 + q₀)`. Page 111 (rendered). -/
noncomputable def DA1 (q : ℝ) : ℝ := -(1 / 2) * (1 + q)

/-- Bamba et al. v3, Eq. (10.60), `D²_{A,y} = −(1/6)(−q₀ − 3q₀² + j₀ + Ω₀)`.
Page 111 (rendered). -/
noncomputable def DA2 (q j Ω : ℝ) : ℝ := -(1 / 6) * (-q - 3 * q ^ 2 + j + Ω)

/-- Bamba et al. v3, Eq. (10.61),
`D³_{A,y} = −(1/24)(−2q₀ + 3q₀² + 15q₀³ − j₀ − 10q₀j₀ − s₀ + 2Ω₀)`. Page 111. -/
noncomputable def printedDA3 (q j s Ω : ℝ) : ℝ :=
  -(1 / 24) * (-2 * q + 3 * q ^ 2 + 15 * q ^ 3 - j - 10 * q * j - s + 2 * Ω)

/-- Bamba et al. v3, Eqs. (10.62)–(10.63),
`D⁴_{A,y} = −(1/120)(1 − 6q₀ + 9q₀² − 15q₀³ − 105q₀⁴ + 10q₀j₀ + 105q₀²j₀ + 15q₀s₀ +`
(newline) `− 3j₀ − 10j² + s₀ + l₀ + 5Ω₀)`.
Page 111. Reading choices: line break `+`/`−` read as `− 3j₀`; `j²` read as `j₀²`. -/
noncomputable def printedDA4 (q j s l Ω : ℝ) : ℝ :=
  -(1 / 120) * (1 - 6 * q + 9 * q ^ 2 - 15 * q ^ 3 - 105 * q ^ 4 + 10 * q * j
    + 105 * q ^ 2 * j + 15 * q * s
    - 3 * j - 10 * j ^ 2 + s + l + 5 * Ω)

/-! ## (D) Same review, z-redshift series with curvature, Eqs. (10.38)–(10.51),
page 110 of v3 (rendered at 300 dpi), crops
`runs/2026-10-30T1232Z/typeset/review_v3_p110_eq10.38-44_z_dL.png`,
`runs/2026-10-30T1232Z/typeset/review_v3_p110_eq10.46-51_z_dA.png`.
`k := Kc²/(H₀²a₀²)`. -/

/-- Bamba et al. v3, Eq. (10.40), `D¹_L = −(1/2)(−1 + q₀)`. Page 110. -/
noncomputable def DL1z (q : ℝ) : ℝ := -(1 / 2) * (-1 + q)

/-- Bamba et al. v3, Eq. (10.41), `D²_L = −(1/6)(1 − q₀ − 3q₀² + j₀ + Kc²/(H₀²a₀²))`.
Page 110. -/
noncomputable def DL2z (q j k : ℝ) : ℝ := -(1 / 6) * (1 - q - 3 * q ^ 2 + j + k)

/-- Bamba et al. v3, Eq. (10.42),
`D³_L = (1/24)[2 − 2q₀ − 15q₀² − 15q₀³ + 5j₀ + 10q₀j₀ + s₀ + 2Kc²(1 + 3q₀)/(H₀²a₀²)]`.
Page 110. -/
noncomputable def DL3z (q j s k : ℝ) : ℝ :=
  1 / 24 * (2 - 2 * q - 15 * q ^ 2 - 15 * q ^ 3 + 5 * j + 10 * q * j + s
    + 2 * k * (1 + 3 * q))

/-- Bamba et al. v3, Eqs. (10.43)–(10.44),
`D⁴_L = (1/120)[−6 + 6q₀ + 81q₀² + 165q₀³ + 105q₀⁴ − 110q₀j₀ − 105q₀²j₀ − 15q₀s₀ +`
(newline) `− 27j₀ + 10j² − 11s₀ − l₀ − 5Kc²(1 + 8q₀ + 9q₀² − 2j₀)/(a₀²H₀²)]`.
Page 110. Reading choices: `+`/`−` line break read as `− 27j₀`; `j²` read as `j₀²`;
`Kc²/(a₀²H₀²)` written `k`. -/
noncomputable def printedDL4z (q j s l k : ℝ) : ℝ :=
  1 / 120 * (-6 + 6 * q + 81 * q ^ 2 + 165 * q ^ 3 + 105 * q ^ 4 - 110 * q * j
    - 105 * q ^ 2 * j - 15 * q * s
    - 27 * j + 10 * j ^ 2 - 11 * s - l - 5 * k * (1 + 8 * q + 9 * q ^ 2 - 2 * j))

/-- Bamba et al. v3, Eq. (10.47), `D¹_A = −(1/2)(3 + q₀)`. Page 110. -/
noncomputable def DA1z (q : ℝ) : ℝ := -(1 / 2) * (3 + q)

/-- Bamba et al. v3, Eq. (10.48), `D²_A = (1/6)[11 + 7q₀ + 3q₀² − j₀ − Kc²/(H₀²a₀²)]`.
Page 110. -/
noncomputable def DA2z (q j k : ℝ) : ℝ := 1 / 6 * (11 + 7 * q + 3 * q ^ 2 - j - k)

/-- Bamba et al. v3, Eq. (10.49),
`D³_A = −(1/24)[50 + 46q₀ + 39q₀² + 15q₀³ − 13j₀ − 10q₀j₀ − s₀ − 2Kc²(5 + 3q₀)/(H₀²a₀²)]`.
Page 110. -/
noncomputable def DA3z (q j s k : ℝ) : ℝ :=
  -(1 / 24) * (50 + 46 * q + 39 * q ^ 2 + 15 * q ^ 3 - 13 * j - 10 * q * j - s
    - 2 * k * (5 + 3 * q))

/-- Bamba et al. v3, Eqs. (10.50)–(10.51),
`D⁴_A = (1/120)[274 + 326q₀ + 411q₀² + 315q₀³ + 105q₀⁴ − 210q₀j₀ − 105q₀²j₀ − 15q₀s₀ +`
(newline) `− 137j₀ + 10j² − 21s₀ − l₀ − 5Kc²(17 + 20q₀ + 9q₀² − 2j₀)/(a₀²H₀²)]`.
Page 110. Reading choices: `+`/`−` line break read as `− 137j₀`; `j²` read as `j₀²`;
`Kc²/(a₀²H₀²)` written `k`. -/
noncomputable def printedDA4z (q j s l k : ℝ) : ℝ :=
  1 / 120 * (274 + 326 * q + 411 * q ^ 2 + 315 * q ^ 3 + 105 * q ^ 4 - 210 * q * j
    - 105 * q ^ 2 * j - 15 * q * s
    - 137 * j + 10 * j ^ 2 - 21 * s - l - 5 * k * (17 + 20 * q + 9 * q ^ 2 - 2 * j))

/-! ## (E) Cattoën & Visser 2007, arXiv:0710.1887v1 (only version on arXiv), Eq. (59) -/

/-- Cattoën & Visser 2007 (arXiv:0710.1887v1), Eq. (59), page 13 (rendered at 300 dpi;
crop `runs/2026-10-30T0220Z/typeset/C1_cv2007_eq58_60.png`):
`d_Q(y) = d_H y {1 − (q₀/2) y + (1/12)[3 − 2q₀ + 12q₀² − 4(j₀ + Ω₀)] y² + O(y³)}`.
This def is the `y²` coefficient `(1/12)[3 − 2q₀ + 12q₀² − 4(j₀ + Ω₀)]`. -/
noncomputable def printedQ2 (q j Ω : ℝ) : ℝ :=
  1 / 12 * (3 - 2 * q + 12 * q ^ 2 - 4 * (j + Ω))

/-! ## (F) Demianski, Piedipalumbo, Sawant, Amati 2017, arXiv:1609.09631, page 3
(v1 rendered at 300 dpi; v2 text layer identical on these lines), crops
`runs/2026-10-30T1628Z/referee_c15/dem17_p3_eqs13-23.png`,
`runs/2026-10-30T1628Z/referee_c15/dem17_p3_eqs21-23.png`,
`runs/2026-10-30T1628Z/screen/DEM17b_p3_eqs13-23.png`. -/

/-- Demianski et al. 2017, D⁴_L of the `d_L(z)` series (Eq. (13); the D⁴_L line follows
Eq. (17) and carries no number of its own), page 3:
`D⁴_L = (1/120)(−6 + 6q₀ + 81q₀² + 165q₀³ − 105q₀⁴ − 110q₀j₀ +`
(newline) `− 105q₀²j₀ − 15q₀s₀ − 27j₀ + 10j² − 11s₀ − l₀)`.
Reading choices: `+`/`−` line break read as `− 105q₀²j₀`; `j²` read as `j₀²`.
The `q₀⁴` coefficient is printed with a MINUS sign (−105q₀⁴), unlike Bamba Eq. (10.43)
(+105q₀⁴); checked at 300 dpi. No curvature term printed. -/
noncomputable def demDL4 (q j s l : ℝ) : ℝ :=
  1 / 120 * (-6 + 6 * q + 81 * q ^ 2 + 165 * q ^ 3 - 105 * q ^ 4 - 110 * q * j
    - 105 * q ^ 2 * j - 15 * q * s - 27 * j + 10 * j ^ 2 - 11 * s - l)

/-- Demianski et al. 2017, Eq. (23), page 3:
`D⁴_A = (1/120)(274 + 326q₀ + 411q₀² + 315q₀³ + 105q₀⁴ −`
(newline) `−210q₀j₀ − 105q₀²j₀ − 15q₀s₀ + 137j₀ + 10j₀² − 21s₀ − l₀)`.
Reading choice: the first line ends with `−` and the second begins with `−210q₀j₀`
(repeated-operator line break); read as a single `− 210q₀j₀`, NOT as `− (−210) = +210`.
Note `+137j₀` is printed with a PLUS (Bamba Eq. (10.51) has `− 137j₀`); `j₀²` printed with
subscript here. No curvature term printed in D⁴_A (whereas Demianski's D³_A, Eq. (22),
does print a `−2kc²(5 + 3q₀)/(H₀²a₀²)` term). -/
noncomputable def demDA4 (q j s l : ℝ) : ℝ :=
  1 / 120 * (274 + 326 * q + 411 * q ^ 2 + 315 * q ^ 3 + 105 * q ^ 4
    - 210 * q * j - 105 * q ^ 2 * j - 15 * q * s + 137 * j + 10 * j ^ 2 - 21 * s - l)

end Checked.Trust.SecondReading
