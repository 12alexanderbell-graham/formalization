# Referee report: `Work.Cosmography.B1A3Bound.third_coefficient_lower_bound`

Referee run on 2026-11-21. Files read: `Work/Cosmography/B1A3Bound.lean`, `Checked/Cosmography/Lookback.lean`,
`Checked/Cosmography/BambaDLy.lean`, `Checked/Cosmography/B1Truncation.lean` (lines 1-567, which contain
`logPolyDL3` and the bridge lemma `lumDistFlat_flatLCDM`). No other repository file, no `runs/` content, no `*.md`,
no git. Scripts are outside the repository, in
`/tmp/claude-0/-home-claude-formalization/c31ce731-a301-50b9-94eb-c837b247fd1d/scratchpad/ref/`
(`lp.py`, `scan.py`, `variants.py`, `witness.py`).

Elaboration check: `lake build Work.Cosmography.B1A3Bound` succeeds, with only the expected `sorry` warning. A scratch
`#print` confirmed which definitions the statement uses: `logPolyDL3` is `Checked.Cosmography.B1.logPolyDL3`,
`lumDistFlat` and `comoving` are the `BambaY` definitions, and `hubble` and `redshift` are the `Checked.Cosmography`
definitions. The import of `B1FitRL19` shadows none of them. Axioms: `propext`, `sorryAx`, `Classical.choice`,
`Quot.sound`.

## 1. Is it true? Yes, with a margin of 0.0435 (1.7 %)

**Reduction.** For a source at redshift z, the hypotheses and the checked bridge `lumDistFlat_flatLCDM`, applied on
`[t_k, t₀] ⊆ [t₅, t₀]`, give

  d_L = (1+z)/H₀ · ∫_{(1+z)^{-1/2}}^{1} 2 dv / √(Ω + (1−Ω)v⁶) =: D_Ω(z)/H₀.

The fit is `ln10/H · P(x)`, with `P(x) = x + a₂x² + a₃x³` and `x = log₁₀(1+z)`. At the three sources
x = ½L, 3/2·L, 5/2·L, where L = log₁₀2, so the sources are equally spaced in x. The ratio d_L/fit is
`(H/(H₀ ln10)) · D_i/P_i`. Because H is free, the offset c is redundant. The three conditions say that all
`log₁₀(D_i/P_i)` lie in a common interval of width 2·(1/20)/5 = 0.02 dex. With s > 0 a free scale and
ρ = 10^0.02, this is the same as

  s·D_i/ρ ≤ x_i + a₂x_i² + a₃x_i³ ≤ s·D_i   (i = 1, 3, 5).

Positivity of the fit follows from s > 0. For fixed Ω, minimising a₃ is therefore a linear programme in (a₂, a₃, s).
I solved it exactly by enumerating all vertices: three active constraints out of six, linear solves at 40 digits.
The D_i were computed with `mpmath.quad` at 30–40 digits. They agree with the independent form
`(1+z)∫₀^z dz'/E(z')` to better than 1e−40, and at Ω = 1 they agree with the closed form 2(1+z)(1−(1+z)^{-1/2})
exactly. `scipy.optimize.linprog` (HiGHS) reproduces the optimum to 8 digits at Ω = 0, 0.3, 0.5 and 1.

**Results** (infimum of a₃ over all admissible a₂, H, c; the optimum is attained with s > 0):

| Ω | min a₃ |
|---|---|
| 0 | 13.832 |
| 0.1 | 7.817 |
| 0.2 | 5.353 |
| 0.3 | 4.286 (the ΛCDM Taylor value is 3.541) |
| 0.5 | 3.367 |
| 0.7 | 2.969 |
| 0.8 | 2.834 |
| 0.9 | 2.728 |
| 1 | **2.643524732639437371** (the ΛCDM Taylor value is 1.546) |

The minimum decreases strictly in Ω on a 201-point grid of [0, 1]. On a 101-point grid of [0.99, 1] it is also
strictly monotone. The minimum over Ω ∈ [0, 1] is therefore attained at Ω = 1 (Einstein–de Sitter):

- a₃_min = 2.64352473263943737128…
- the optimal a₂ = 1.88365380030162922724…
- the optimal s = 0.4705…
- the margin above 13/5 is 0.0435247 (1.67 %)

At the optimum the residuals equioscillate: +0.05, −0.05, +0.05 mag about c, at z₁, z₃, z₅. The infimum is attained,
so the strict inequality `13/5 < a₃` is the right form. This matches the docstring's unchecked float scan ("near
2.64, at density one").

## 2. Near-misses

**The constant.** The statement becomes false for every constant ≥ 2.6435247…. The smallest round constant is
**53/20 = 2.65** (2.644 already fails).

**Witness for 53/20:**

- Ω = 1, a(t) = t^(2/3), t₀ = 1, so H₀ = 2/3.
- t₁ = 2^(−3/4) ≈ 0.594604, t₃ = 2^(−9/4) ≈ 0.210224, t₅ = 2^(−15/4) ≈ 0.0743254, which give 1+z = √2, 2√2, 4√2.
- a₂ = 18733/10000, a₃ = 53/20, H = 7049/10000, c = 0.
- Fit polynomial P at the sources: 0.20199, 1.07747, 2.94308. All are positive.
- Residuals 5 log₁₀(d_L/fit) − c: **+0.049487, −0.049745, +0.049493**. All are within 1/20.

With a₃ = 2.644 an a₂ still exists (a₂ = 1.8829): the peak-to-peak spread is 0.09994 ≤ 0.1.

**Dropping Ω ≤ 1 changes the answer.** The minimum keeps decreasing for Ω > 1. For Ω ≤ 30 the integrand stays
well defined on [w, 1], so the hypotheses remain satisfiable.

| Ω | min a₃ |
|---|---|
| 1.05 | 2.6078 |
| 1.1 | 2.5754 |
| 1.25 | 2.4947 |
| 1.5 | 2.3975 |
| 2 | 2.2785 |
| 5 | 2.0696 |
| 30 | 1.9433 |

The critical density is **Ω ≈ 1.0616**. Above it the bound 13/5 fails. The hypothesis Ω ≤ 1 is therefore essential.

**Dropping Ω ≥ 0 does not matter, as far as can be tested.** For slightly negative Ω the minimum rises:
14.00 at Ω = −0.002 and 14.29 at Ω = −0.005. Below about −0.0055 the expansion law has a negative radicand inside
the range and junk-valued square roots.

**Widening 1/20 changes the answer.** The minimum over Ω, always attained at Ω = 1:

| window δ | min a₃ |
|---|---|
| 0.03 | 2.962 |
| 0.04 | 2.808 |
| 0.05 | 2.6435 |
| 0.051 | 2.6265 |
| 0.052 | 2.6093 |
| 0.055 | 2.557 |
| 0.06 | 2.468 |
| 0.075 | 2.181 |
| 0.1 | 1.630 |
| 0.2 | −3.53 (at Ω ≈ 0.32) |

The critical window is **δ ≈ 0.052537 mag**. Widening 1/20 by about 5 % makes the statement false.

## 3. Meaning and junk values

- **Quantifiers.** The statement is ∀Ω ∈ [0, 1], ∀a, ∀t₅ ≤ t₃ ≤ t₁ ≤ t₀ satisfying the model hypotheses, ∀a₂ a₃ H c
  with H > 0 and the six fit hypotheses, ⊢ a₃ > 13/5. This is the claim in words: a₂ is universal ("whatever the
  second coefficient"), and H and c are free.
- **Times and redshifts.** `hz₁`, `hz₃`, `hz₅` tie each time to its redshift. The expansion law `hH`, positivity
  `hpos` and differentiability `hdiff` hold on `Icc t₅ t₀`, which contains every `[t_k, t₀]`. That is exactly what
  the bridge lemma needs. The order hypotheses are in fact redundant: the radicand is positive, so a is strictly
  increasing. They are not contradictory.
- **Interval orientation.** `comoving a t₀ t = ∫ s in t..t₀, 1/a s` with t ≤ t₀ is the positive comoving distance.
  The redshifts are positive, which forces t_k < t₀ strictly, so d_L > 0.
- **No junk values are reachable.**
  - `redshift` divides by a t > 0.
  - `√(Ω(1+z)³ + 1 − Ω)` has a positive argument for Ω ∈ [0, 1] and 1+z > 0.
  - `Real.logb 10 (1+z)` is evaluated at √2, 2√2, 4√2, all > 1.
  - The ratio inside the distance-modulus `logb` is (positive d_L)/(positive fit, by `hp₁`, `hp₃`, `hp₅`), so the
    `logb |x|` convention never applies.
  - `hubble` uses `deriv`, but `hdiff` guarantees a genuine derivative.
- **H vs H₀.** H in `logPolyDL3` is a free normalisation and is not tied to `hubble a t₀`. This is intended: it
  makes c redundant, and it means the bound concerns shape only.
- **Non-vacuity.** EdS with t₀ = 1, as in the witness above, meets every model hypothesis:
  - hubble = 2/(3s)
  - H₀ · √((1+z)³) = (2/3) · s^(−1) ✓
  - the redshift values are exact ✓
  The fit hypotheses are satisfiable for a₃ just above 2.6435. The statement is therefore not vacuous, and the
  constant is near-sharp.
- **Fidelity to the docstring.** The docstring is accurate. One wording nit: "matches an exact flat ΛCDM distance
  modulus over the quasar range" means matching at three points (z ≈ 0.414, 1.83, 4.66) with ±0.05 mag about a
  common offset, not over the whole range. The 1+z values are geometric, so the points are equally spaced in x.

## 4. Prior art and consequence

What I checked (arxiv.org/pdf only, read through a summarising fetch tool; quotations below are the tool's
extraction, not my own reading of the PDFs):

- **Yang, Banerjee & Ó Colgáin 2020 (1911.01681v2).** They fit the log polynomial to exact ΛCDM points
  (Ω_m = 0.3, z = 0…6) and report only that a₂ and a₃ land 6.6σ and 10.4σ from the Taylor values
  (2.9358, 3.5412). They print no fitted values and no inequality.
- **Banerjee et al. 2021 (2009.04109).** Mock fits with Ω_m = 0.1 and 0.9. They give the Taylor (a₂, a₃) relations
  and the "variable yardstick" / "phantom tension" argument. They report no numerical fitted a₃ and no bound.
- **Risaliti & Lusso 2019 (1811.02590).** Quasar range 0.04 < z < 5.1, a ~4σ tension, and the Methods formulas. The
  best-fit (a₂, a₃) appear only in figures (Extended Fig. 5). I could not extract numbers from the text.
- **Lusso et al. 2019 (1907.07692).** Table 2 gives fourth-order fits, for example SNe+QSO
  a₃ = 4.466 (+1.013/−1.040) and SNe+QSO+GRB a₃ = 3.564 (+0.92/−0.94), together with the "few per cent" remark. These
  are not cubic fits, so they are not directly comparable.
- **Bargiacchi et al. 2021 (2101.08278).** Orthogonal 4th- and 5th-order fits only. No cubic coefficients from ΛCDM
  and no bound on a₃.

I did not check the remaining Bargiacchi papers, the published versions, or any figure-digitised values.

**Conclusion on novelty.** I found no published lower bound of this kind. The idea that the cubic coefficients
fitted to exact ΛCDM are displaced from the Taylor point is known (Yang et al. 2020; Banerjee et al. 2021). A
certified Ω-uniform statement of the form "every cubic matching to 0.05 mag at these three redshifts has a₃ > 2.6"
appears to be new, but it is a modest quantitative refinement of a known mechanism.

**What it implies.** For every flat ΛCDM model with 0 ≤ Ω ≤ 1, any cubic that tracks it to ±0.05 mag (0.1 mag peak
to peak) at those three redshifts has a₃ > 2.6. For Ω near 0.3 the true minimum is about 4.29, above the Taylor
value 3.54.

**What it does not imply.**
- Nothing about a χ² or least-squares fit to real data with errors and scatter.
- Nothing about the significance of the RL19 or Lusso tension, or whether a published a₃ is "consistent with ΛCDM".
- Nothing about other redshifts or other windows.

A best-fit a₃ ≤ 2.6 from data would not contradict ΛCDM through this theorem alone. It would only say that the
best-fit cubic deviates from every ΛCDM curve, at one of these three points, by more than 0.05 mag about any common
offset. Whether that matters depends on the data errors, which the theorem does not model.

## 5. Verdict: **STANDS WITH CAVEATS**

The statement is true. The infimum is 2.643525, attained at Ω = 1, a margin of 0.0435 above 13/5. It is correctly
formalised, non-vacuous, and free of junk-value loopholes.

Caveats:
1. **Thin margin.** The margin is 1.7 %. It disappears for any constant ≥ 2.6436 (for example 53/20), for Ω above
   about 1.062, or for a window above about 0.05254 mag. A proof needs tight certified integrals near Ω = 1. There the
   integrals are elementary: D = 2(1+z)(1 − (1+z)^(−1/2)).
2. **Weak constraint at relevant densities.** The binding case is the Ω = 1 edge. At observationally relevant
   Ω ≈ 0.3 the true bound (about 4.29) is much stronger than 13/5.
3. **Scope.** The result concerns three points and a uniform 0.05 mag window, not fits to data. Claims about the
   published fits must not be drawn from it.
4. **Docstring wording.** "Over the quasar range" should read "at three redshifts spanning the quasar range".
