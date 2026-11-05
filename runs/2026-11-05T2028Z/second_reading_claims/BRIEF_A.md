(Agent prompt for reader A, verbatim apart from line wrapping; the reader also read BRIEF_COMMON.md.)

Output folder: runs/2026-11-05T2028Z/second_reading_claims/A/; files SecondReadingClaimsA.lean and NOTES_A.md.
Items (names and argument orders are fixed; you supply the bodies by reading the source):
1. Aviles, Gruber, Luongo, Quevedo, PRD 86, 123516 (2012), arXiv:1204.2007, Eq. (15) (p. 10 of v2; check all versions). Eq. (15) gives the cosmographic parameters of the spatially flat ΛCDM model as functions of the matter density today Ω_m. Write `avilesL0 (Ω : ℝ) : ℝ` = the printed l₀ (fifth-order cosmographic parameter), with Ω = Ω_m; `avilesM0 (Ω : ℝ) : ℝ` = the printed m₀ (sixth-order parameter). Report them exactly as printed, even if you believe they are wrong. Crop: runs/2026-10-30T0220Z/typeset/C2_aviles_v2_p10_eq15.png.
2. Capozziello, Lazkoz, Salzano, PRD 84, 124061 (2011), arXiv:1104.3096, Eq. (22): flat model, matter Ω_m, CPL w(z) = w₀ + w_a z/(1+z). Write `clsL0 (Ω w₀ wₐ : ℝ) : ℝ` = the printed l₀. Crops C4_cls2011_eq19_22_v1.png, _v2.png.
3. Capozziello, Cardone, Salzano, PRD 78, 063504 (2008), arXiv:0802.1583, Appendix A, Eq. (A2): `ccsA2Prefactor : ℕ` = power of z in the factor multiplying the bracket; `ccsA2Last : ℕ` = highest power of z inside the bracket with a printed coefficient. Crops C3_ccs2008_v2_p16_A2.png, C3_ccs2008_A2_Dz4.png.
4. Cattoën & Visser 2007, arXiv:0710.1887, Eq. (59), d_Q in y = z/(1+z): `cvdQ59Prefactor : ℕ`, `cvdQ59Last : ℕ` (an O(·) term does not count). Crop C1_cv2007_eq58_60.png.
5. Demianski, Piedipalumbo, Sawant, Amati 2017, arXiv:1609.09631, Eqs. (13)–(23): `demDLPrefactor`, `demDLLast`, `demDAPrefactor`, `demDALast`; say whether either series has a curvature term and where. Crop runs/2026-10-30T1628Z/screen/DEM17b_p3_eqs13-23.png.
Conventions: q₀, j₀, s₀, l₀, m₀ = deceleration, jerk, snap, lerk, sixth-order parameter. Keep the printed grouping.
