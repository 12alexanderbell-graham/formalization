# NOTES_A (blind second reading, reader A)

All readings from 200-dpi renders of arXiv PDFs (temp dir outside repo); crops in this folder. No repository file other than the brief was opened.
Lean file compiles (only a deprecation warning for the Mathlib import path).

## 1. Aviles et al., arXiv:1204.2007, Eq. (15), p. 10 (v1 and v2 both p. 10; pixel-identical text)
Printed (crop_aviles_v2_eq15.png):
q0 = -1 + (3/2)Ωm ; j0 = 1 ; s0 = 1 - (9/2)Ωm ;
l0 = 1 + 3Ωm - (27/2)Ωm² ;
m0 = 1 - (27/2)Ωm² - 81Ωm² - (81/2)Ωm³   (two separate Ωm² terms, as printed).
Internal check (flat LCDM, Ωm=1 = Einstein-de Sitter, using a ~ t^(2/3)): q0=1/2 OK, j0=1 OK, s0=-7/2 OK,
but true l0 = 35/2 and true m0 = -7280/64 = -113.75, whereas the printed l0 = -19/2 and m0 = -134 at Ωm=1.
So printed l0 and m0 look wrong (or use a different convention); reported as printed. (Capozziello et al. Eq. (22) below gives 35/2 at Ωm=1, consistent with EdS.)

## 2. Capozziello, Lazkoz, Salzano, arXiv:1104.3096, Eq. (22), p. 4 (v1 and v2 identical)
Printed (crop_cls_v1_eq22.png, crop_cls_v2_eq22.png):
l0 = 35/2 + (1-Ωm)/4 [213 + (7-Ωm) wa] wa
 + (1-Ωm)/4 [489 + 9(82-21Ωm) wa] w0
 + (9/2)(1-Ωm) [67 - 21Ωm + (3/2)(23-11Ωm) wa] w0²
 + (27/4)(1-Ωm)(47-24Ωm) w0³
 + (81/2)(1-Ωm)(3-2Ωm) w0⁴.
Checks: at Ωm=1 gives 35/2 = EdS value (OK). Not otherwise verified. (Note: printed s0 Eq. (21) has an odd "... w0² 27/4 ..." juxtaposition, not part of this task.)
Lean uses `(1 - Ω) / 4 * (...) * wₐ` keeping printed grouping.

## 3. Capozziello, Cardone, Salzano, arXiv:0802.1583, Eq. (A2), p. 15 of v2
v1 (15 pages) has no Appendix A (no distance formulas); v2 (18 pages) has it; Eq. (A2) is on p. 15 (the coefficients 𝒟^n_z, A2 continuation, on p. 16).
Printed (crop_ccs_v2_A2.png): D(z) = (c z / H0) { 𝒟⁰_z + 𝒟¹_z z + 𝒟²_z z² + 𝒟³_z z³ + 𝒟⁴_z z⁴ }.
ccsA2Prefactor = 1, ccsA2Last = 4. (Coefficients 𝒟⁰..𝒟⁴ are listed on p. 16, consistent: five coefficients.)

## 4. Cattoën & Visser, arXiv:0710.1887, Eq. (59), p. 13 (only v1 exists)
Printed (crop_cv_v1_eq58_60.png): d_Q(y) = d_H y { 1 - (q0/2) y + (1/12)[3 - 2q0 + 12q0² - 4(j0+Ω0)] y² + O(y³) }.
cvdQ59Prefactor = 1, cvdQ59Last = 2.

## 5. Demianski et al., arXiv:1609.09631, Eqs. (13)-(23), p. 3 (v1 and v2 identical on this page)
Printed (crops crop_dem_v1/v2_eq13_23.png):
d_L(z) = (cz/H0)(𝒟⁰_L + 𝒟¹_L z + 𝒟²_L z² + 𝒟³_L z³ + 𝒟⁴_L z⁴ + O(z⁵)), Eq. (13);
d_A(z) = (cz/H0)(𝒟⁰_A + 𝒟¹_A z + 𝒟²_A z² + 𝒟³_A z³ + 𝒟⁴_A z⁴ + O(z⁵)), Eq. (18).
demDLPrefactor = 1, demDLLast = 4, demDAPrefactor = 1, demDALast = 4.
Spatial curvature: the d_L coefficients (14)-(17) and the printed 𝒟⁴_L contain NO curvature term. The d_A series contains one, only in 𝒟³_A (Eq. 22): the term -2kc²(5+3q0)/(H0²a0²) inside the bracket (printed as "... - s0 + [new line] - 2kc²(5+3q0)/(H0² a0²)"), whole bracket multiplied by -1/24. 𝒟⁰_A..𝒟²_A and 𝒟⁴_A (Eq. 23) have no k term. (Compare: CCS 2008 has k terms in d_L coefficients 𝒟²_L, 𝒟³_L, 𝒟⁴_L; the Demianski d_L omits them.)
