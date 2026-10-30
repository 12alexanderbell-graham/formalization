# Referee report: C15 and C16 (Work/Cosmography/DemianskiZ.lean, commit ab63005)

Referee: annex XLV, run 2026-10-30T1628Z. Approach: attack.

## Verdicts
- **C15** (Demianski 2017 flat D⁴_L has −105q₀⁴, correct value +105q₀⁴, reprinted in Lusso 2019): **STANDS-WITH-CORRECTIONS**. The mathematics is right. The citation of Lusso "Eq. (7)" is wrong, and the stated consequences need to be phrased with care.
- **C16** (Demianski 2017 Eq. (23) D⁴_A has +137j₀, correct value −137j₀): **STANDS-WITH-CORRECTIONS**. The mathematics is right. The "verbatim" claim hides a reading choice at the line break (see I3).

## 1. Fresh derivation (derive.py, derive_out.txt)
- Method: a generic a(t) to T⁶ in the papers' convention, which is Eqs. (2)–(6) and (11) of Demianski 2017. There q = −äa/ȧ², and j, s, l are all a⁽ⁿ⁾aⁿ⁻¹/ȧⁿ with a + sign. Then 1+z = 1/a, χ = ∫dt/a, T(z) by series reversion, d_L = (1+z)χ and d_A = χ/(1+z).
- Result: D⁰…D³ of d_L and of d_A agree with every printed coefficient in Demianski (13)–(22) and Lusso (2)–(6).
- Only discrepancies:
  - D⁴_L: correct − printed = **(7/4)q₀⁴**.
  - D⁴_A: correct − printed = **−(137/60)j₀**.
  - All other D⁴ coefficients agree.
- Conventions:
  - Demianski Eqs. (3)–(6) and (9)–(10), crop dem17_p2_eqs2-11.png, are the standard Visser signs. Lusso Eq. (1) is the same a(t).
  - Checked `cosmoCoeff n = a⁽ⁿ⁾/(a Hⁿ)` and `decel` match these.
  - Probes s→−s, l→−l, both, j→−j, q→−q: none makes either printed D⁴ correct. Each one also breaks the printed D³ or adds other terms. **No convention reading rescues −105q₀⁴ or +137j₀.**
- Lean spot check (RefCheck.lean): verbatim copies of `demDL4`/`demDA4` against Checked `correctDL4z`/`correctDA4z` at k = 0. `flat_corrections` closes by `unfold; ring`, and the file compiles cleanly. The frozen file also elaborates, with 7 sorries only.

## 2. Fidelity issues (Lean)
- **I1 (minor, citation; fix in docstrings and module doc):** the D⁴_L display has no equation number in either paper.
  - Demianski: it sits between (17) and (18).
  - Lusso, all of v1–v4: it follows (6).
  - **Lusso Eq. (7) is the log-polynomial fit function.** It reads `log[D_L(z)] = …` in v1/v2 and `D_L(z) = …` in v3/v4. So "Lusso et al. 2019 (7)" in `demDL4`'s docstring and "Eqs. (2)–(7)" in the module doc are wrong. Fix: "Eqs. (2)–(6) and the unnumbered display after (6)". Likewise for Demianski: "unnumbered display after (17)".
- **I2 (minor, versions):** state which arXiv versions were read.
  - Demianski: 1609.09631 v1 and v2 are identical here; the errors are in both. No v3.
  - Lusso: 1907.07692 v1–v4 all carry −105q₀⁴. v3 changed Eq. (7) but not D⁴_L.
- **I3 (minor, reading):** Eq. (23) is printed as "…+105q₀⁴−" and then, on the next line, "−210q₀j₀…" (crop dem17_p3_eqs21-23.png). That is literally a double minus.
  - The paper's line-break convention elsewhere is "+ / −", which means "−".
  - `demDA4` takes −210q₀j₀. That is the charitable reading and the correct coefficient.
  - Read literally, it gives +210q₀j₀, an extra −(7/2)q₀j₀ error. This is checked in RefCheck.lean as `demDA4lit`.
  - The module doc quote "+ 105q₀⁴ − 210q₀j₀" is therefore not verbatim. Record the reading explicitly, as is done for "j²" and for "+ / −".
- **I4 (none):** the claims are fine.
  - Flat reading: the d_L series has no curvature terms, and K = 0 is used.
  - o(z⁵) for H₀d_L − z[…]: the printed bracket O(z⁵) gives O(z⁶), so o(z⁵) is weaker and makes the refutation strong.
  - Reusing `remLz`/`remAz` at K = 0 is fine: `curvK` = 0 makes `DL2z…DA3z` the printed flat ones, and the `_` slot ignores k.
  - The fail theorems' hypotheses (C⁵, a(t₀) ≠ 0, H₀ ≠ 0, q₀ ≠ 0 or j₀ ≠ 0) match `lumDist_z_fifth_order`.
  - The global claims are refutable by a(t) = eᵗ, which is analytic and positive with H = 1, q = −1, j = 1.
  - No junk-value loophole found: `cosmoCoeff`/`decel` divide by quantities that are nonzero under the hypotheses.

## 3. Provenance
- Correct in the predecessor and sister papers:
  - Demianski, Piedipalumbo, Rubano, Scudellaro 2012 (arXiv:1206.7046), Eqs. (41) and (47): +105q₀⁴ and −137j₀.
  - Piedipalumbo et al. 2015 (arXiv:1509.08793), same.
  - Capozziello, Lazkoz, Salzano 2011 (arXiv:1104.3096), Eq. (B5): +105q₀⁴.
  - Bamba et al. 2012, (10.43)/(10.50): correct.
- The errors are **new in Demianski 2017b**. The 2017 text copies the 2012 equations, but the lines are broken in different places: 2012 has "…−15q₀s₀ + / −137j₀", while 2017 has "105q₀⁴− / −210…+137j₀". So the errors look like transcription slips made while re-wrapping.
- Demianski 2017a (1610.00854) has no series.
- Lusso 2019 reprints D⁰…D⁴_L verbatim from 2017b ("fully described in Demianski et al. 2017b").
- No reprint found in Bargiacchi+21 (2111.02420), Bargiacchi+21b (2101.08278), Lusso+20 (2008.08586), Benetti+25 (2506.21477), Demianski+21 (1911.08228) or 1802.01694.
- No erratum found for either paper.

## 4. Consequence (severity: low for reported numbers)
- Lusso 2019 §3.1/§4.1:
  - Data: SN+QSO+GRB μ(z) only, so d_L only.
  - Fit: "fifth order std cosmography" (green line, "equation 2"). The text also says they use y = z/(1+z), so the variable is ambiguous.
  - Table 1 reports q₀, j₀, s₀ only; l₀ is not reported.
  - In the z-series, l₀ enters only D⁴_L, linearly as −l₀/120. Printed(q,j,s,l′) = correct(q,j,s,l) exactly when **l′ = l − 210q₀⁴**. That map has unit Jacobian.
  - The same holds for a y-series obtained from the printed z-series: both l₀ and the error enter only the y⁴ coefficient.
  - So with a flat, wide l₀ prior, the posteriors of q₀, j₀, s₀ (and the >4σ j₀ result) are **unchanged**. Only the (unreported) l₀ shifts: by −87 at q₀ = −0.80, −27 at −0.6, −11 at −0.48.
  - The §3.2/§4.2 log-polynomial >4σ result does not use D⁴_L at all.
- Demianski 2017:
  - Tables 3–5 report h, q₀, j₀, s₀; "l₀ unconstrained".
  - The fits are joint with H(z) and BAO. The d_A error would need l′ = l + 274j₀ (+186 at j₀ = 0.68), which is incompatible with the d_L shift. Any correct H(z) series that contains l₀ also breaks the reparametrisation.
  - So the effect on q₀, j₀ is **not provably zero**, but it is plausibly small given that l₀ is unconstrained. It is unquantifiable without their code: the variable (z or y), the l₀ prior, and whether BAO uses the printed D⁴_A are unknown.
- The mismatch at fixed parameters is not small: (7/4)q₀⁴ = 0.72 in the bracket at q₀ = −0.8, z = 1. Anyone who reuses the printed formula with independently fixed l₀ (for example, plotting a model curve) gets wrong distances.

## 5. Prior art
- Not found. Yang–Banerjee–Ó Colgáin (arXiv:1911.01681) critique Lusso 2019's log-polynomial and the convergence of the expansion, not this coefficient.
- Heinesen–Korzyński (2406.06167) list other authors' typos, but not these.

## Required corrections (before promotion)
1. Replace "Lusso (7)" and "Eqs. (2)–(7)" with "(2)–(6) + unnumbered display after (6)". Note that the Demianski D⁴_L is unnumbered (after (17)).
2. Record the "105q₀⁴− / −210q₀j₀" reading as charitable; the literal reading is an additional error.
3. Cite versions: 1609.09631 v1/v2, 1907.07692 v1–v4.
4. In the consequence text, say the D⁴_L error is absorbed exactly by l₀ in d_L-only fits (Lusso). It does not affect the reported q₀, j₀, s₀ or the 4σ claim under a flat l₀ prior. Its effect on the Demianski joint fits is undetermined but likely small.

## Files (runs/2026-10-30T1628Z/referee_c15/)
- derive.py, derive_out.txt: fresh sympy derivation, convention probes, LCDM check.
- RefCheck.lean: Lean check of `flat_corrections` and the literal-reading variant; compiles.
- Crops: dem17_p2_eqs2-11.png (definitions and a(t)), dem17_p3_eqs13-23.png, dem17_p3_eqs21-23.png, lus19_p2_eqs1-7.png (§3.1 and Eq. (1)), lus19_p2_eqs2-7.png (Eqs. (2)–(6) and the unnumbered D⁴_L).
- Downloads and text dumps are in /tmp/ref_c15 (outside the repo).
