VERDICT: STANDS-WITH-CORRECTIONS

The statement is true, with a large margin, and it is non-vacuous. The Lean statement matches its theorem docstring. The corrections concern framing. The frozen claim cannot support "the RL19/Lusso deviation is of the size that exact ΛCDM itself forces on a cubic fit", for three reasons:
- the ΛCDM-forced displacement points the opposite way to the RL19 offset;
- the two-point criterion at z = 3 and z = 7 is not what a fit over the quasar range does;
- the "size" idea (and the mock-based version of it) is prior art (Banerjee et al. 2021).

Referee: independent, 2026-10-31.
Scripts are outside the repository, in /tmp/referee_b1sep/scripts/ (sep.py, sep2.py, fit.py, fit2.py, extra.py). Downloads are in /tmp/referee_b1sep/dl/.

## 1. Truth and margin

1. **Reduction.** H, H₀ and c all drop out. Whether some c satisfies both |Δμ₃ − c| ≤ 0.05 and |Δμ₇ − c| ≤ 0.05 is exactly the condition |Δμ₇ − Δμ₃| ≤ 0.1. In terms of the polynomials, with x₃ = log₁₀4, x₇ = log₁₀8, P(x) = x + a₂x² + a₃x³ and R(Ω) = d_L(7)/d_L(3), this reads:

   P₇/P₃ ∈ [R·10^(−0.02), R·10^(+0.02)].

   For H > 0 and both values positive, the feasible set is a convex cone in the (a₂, a₃) plane. Its apex is at the point where P₃ = P₇ = 0, namely (−2.768, 1.839). Its edges are the two lines P₇ = ρ±P₃. The Taylor point is outside this cone: its shape mismatch 5log₁₀(R/(P₇/P₃)) lies between 0.2446 and 0.2683 mag, which is more than 0.1.

2. **True minimum.** I computed with mpmath (30 digits), using a grid of 401 values of Ω plus root refinement. The minimum over Ω ∈ [0.2, 0.4] of the Euclidean distance is **1.97826, at Ω = 0.31380**. Its square is 3.9135, against the frozen (5/4)² = 1.5625. The distance is 2.1697 at Ω = 0.2 and 2.0274 at Ω = 0.4.

   The margin is 0.728 in distance: 5/4 is 63% of the truth. 19/10 would still hold (margin 0.078). 7/4 is a comfortable stronger choice.

3. **Positivity side conditions and non-vacuity.** At Ω = 0.3 the nearest feasible point is (1.771, 5.142), with P₃ = 2.37 and P₇ = 6.13. Both are positive, so the positivity hypotheses never bind at the optimum. This point, with H = 1 and a suitable c, is a non-vacuity witness. The model a ∝ sinh^{2/3} supplies the cosmology.

4. **Junk branches and the role of `hHp`.** None of these branches comes close to 5/4. Minimum distances over Ω ∈ [0.2, 0.4]:

   | Branch | What it covers | Min distance |
   |---|---|---|
   | Lines P₇ = −ρ±P₃ | `logb` taking the absolute value when exactly one value is negative | ≥ 5.07 |
   | Line P₃ = 0 | `logb 0 = 0` junk at z = 3 | ≥ 5.28 |
   | Line P₇ = 0 | `logb 0 = 0` junk at z = 7 | ≥ 4.81 |
   | Apex | P₃ = P₇ = 0 | ≥ 5.63 |
   | Opposite half-cone | H < 0 with both polynomial values negative | ≥ 5.6 (it lies beyond the apex) |

   Consequences:
   - **`hHp` is not needed for truth.**
   - The statement stays true if any single one of {`hHp`, `hp₃`, `hp₇`} is kept and the other two are dropped.
   - It becomes false only if all three are dropped. Then H = 0 makes `logPolyDL3 = ln10/0 · P = 0`, so both Δμ = 0 and every (a₂, a₃) is admissible.

   See 2.3 for what this means for CI.

5. **Range of Ω.** The bound also holds for Ω ∈ [0.1, 1]. The distance is 2.14 at Ω = 0.5, 2.22 at 0.58, 2.15 at 0.9 and 1.95 at 1.0. This matters because RL19 tests against the whole ΛCDM curve. The point of the Taylor curve closest to the RL19 contour centre is at Ω ≈ 0.58, which lies outside the frozen range (see 3.4).

6. **Proof-route note.**
   - The constraint is linear once R is bounded: P₇ ≥ ρ₋P₃ with P₃ > 0. So the distance is exactly |P₇(T) − ρP₃(T)| / |n(ρ)|, the distance from the Taylor point T to a line.
   - Reaching 5/4 needs a certified lower bound R ≥ 2.697 at Ω = 0.2, R ≥ 2.648 at Ω = 0.3 and R ≥ 2.602 at Ω = 0.4. That is about 2.4–2.9% below the true R.
   - Equivalently, the needed shape-miss certificate is about 0.185 mag at Ω = 0.2, 0.195 at 0.3 and 0.206 at 0.4.
   - **The existing `cubic_shape_miss` certificate (0.18) is not enough on its own.** A sharper bracketing is needed (more Ω sub-intervals).
   - A Lipschitz route around the disk fails: it would need a certificate above 0.268 at Ω = 0.4, while the true value is 0.2683.

## 2. Fidelity of the Lean statement

1. **The statement matches the docstring.**
   - Quantifiers: c is a universally bound argument appearing only in hypotheses, which is equivalent to "for some offset c".
   - Constants: 1/20 = 0.05 mag. `5 * Real.logb 10` is the distance-modulus convention. The inequality (5/4)² < … is strict, as the docstring says.
   - Units: `lusA2`/`lusA3` (log₁₀ units, L19 Eq. (8)) and `logPolyDL3` (log₁₀ x with an ln10 prefactor) use the same convention, so there is no ln/log₁₀ mismatch.
   - The cosmology hypotheses are copied from `cubic_shape_miss`, which the docstring promises, and the bridge needs every one of them.
   - Junk values: `lumDistFlat > 0` follows from the bridge, and the junk branches cannot make the conclusion true for the wrong reason (1.4).

2. **The module docstring overstates.**
   - "a cubic that *reproduces* [ΛCDM]": the hypothesis is only a two-point ratio condition, a single scalar constraint on P₇/P₃. It says nothing about any other redshift, and z ≤ 3 is completely unconstrained.
   - "where does a cubic … land?": the theorem gives only a lower bound on the distance, not the location or direction of the landing point. Section 3 shows that the direction is the scientifically decisive part.
   - Suggested wording: "agrees with the exact distance modulus, up to a common offset, within 0.05 mag at z = 3 and at z = 7".

3. **Unused-hypothesis risk.** CI rejects unused binders, and PROMPT.md asks for minimal hypotheses at freeze time.
   - `hHp` is not needed for truth (1.4). The proof uses it only if it gets P₃ > 0 from H > 0, which is the natural route.
   - A prover who derives P₇/P₃ > 0 from `hp₃` and `hp₇` alone, and handles the negative half-cone separately, would leave `hHp` unused, and CI would then force a relock.
   - Decide now:
     - (a) keep all three and require the proof to go through H > 0 ⇒ P₃, P₇ > 0 (simplest; this route uses `hHp`, `hp₃` and `hp₇`); or
     - (b) drop `hHp` and prove the negative half-cone case. That case is easy, since it lies at distance ≥ 5.6, but it is extra work.
   - Keeping `hp₃` and `hp₇` is defensible on modelling grounds, as the docstring says. Note, though, that they are also logically redundant once `hHp` is present.

4. Every other hypothesis is needed through the bridge (`h₇₃`, `h₃₀`, `hpos`, `hdiff`, `hH₀`, `hH`, `hz₃`, `hz₇`, `hΩ₁`, `hΩ₂`). I found no vacuity and no quantifier errors.

## 3. Scientific relevance and framing

1. **The two-point criterion is not what a fit over the quasar range does.** I fitted P with a free magnitude offset, by least squares, to exact flat ΛCDM with Ω = 0.3:

   | z range | weighting | (a₂, a₃) | distance from Taylor (2.936, 3.541) | max \|res\| | shape(7) − shape(3) |
   |---|---|---|---|---|---|
   | 0.01–5 | uniform in z | (2.296, 4.929) | 1.53 | 0.069 | 0.134 |
   | 0.01–5 | uniform in ln(1+z) | (2.470, 4.773) | 1.32 | 0.051 | 0.150 |
   | 0.01–7 | uniform in z | (1.905, 5.349) | 2.08 | 0.127 | 0.094 |
   | 0.01–7 | uniform in ln(1+z) | (2.221, 5.135) | 1.75 | 0.084 | 0.119 |

   - The fits over the quasar range (z ≤ 5; RL19 quasars reach 5.1) **do not satisfy the theorem's hypothesis**: their shape is 0.13–0.15 mag, above 0.1.
   - Their distance from the Taylor point (1.3–1.5) is also **below** the theorem's true minimum of 1.98.
   - So the theorem neither covers these fits nor bounds them. z = 7 is outside the RL19 data range.
   - Sensitivity to weighting (z ≤ 5): weights exp(−z), exp(−z/2), ×5 above z = 1.4, and a quasar-like log-normal give distances of 0.95–1.81.
   - A minimax version (sup over [0.01, 5] of |Δμ − c| ≤ 0.05) gives a separation of only ≈ 0.99. Its nearest point is (2.79, 4.52). With ε = 0.03 no cubic is feasible at all.

2. **Direction: the decisive objection.**
   - The RL19 Fig. 3 filled-contour centre is at about (3.45, 1.6), as read in rl19_numbers.md. I confirmed this on the crop `typeset/rl19_p9_fig3.png`. Its offset from the Taylor point is (+0.51, −1.94), a length of 2.01.
   - Every ΛCDM-forced displacement I computed points to smaller a₂ and larger a₃. The cosine of the angle with the RL19 offset is between −0.966 and −1.000 for every weighting and range tried. The two displacements are **antiparallel**.
   - The theorem's feasible cone lies on the same side. Its boundary line at Ω = 0.3 has unit normal (−0.588, 0.809). The signed distance to that line is −1.98 for the Taylor point and −3.85 for the RL19 centre. So the RL19 centre lies 1.87 further *outside* the feasible set than the Taylor point does.
   - The RL19 centre cubic has shape(7) − shape(3) = 0.434 mag, against 0.249 for the Taylor point. Its residual spread over [0.01, 5], with the best offset, is 0.63 mag, against 0.25 for the Taylor point.
   - Banerjee et al.'s own mocks show the same direction. Their Fig. 3, p. 4 of the arXiv PDF, shows the Ωm = 0.1 ellipses at about (2.9, 7.9) against the curve point at (3.28, 5.19), and the Ωm = 0.9 ellipses at about (1.6, 2.6) against (1.90, 1.47).

3. **The proposed sentence would mislead.** "The RL19/Lusso deviation is of the size that exact ΛCDM itself forces on a cubic fit" is true only in Euclidean magnitude: forced ≥ 1.98 (two-point) or 1.3–1.5 (least squares, z ≤ 5), against an RL19 offset of 2.0. That match is a coincidence of magnitudes with opposite sign. Read naturally, the sentence implies the tension is a truncation artefact. With uniform-type weights, moving the reference from the Taylor point to the "ΛCDM as seen by a fitted cubic" point **increases** the Euclidean separation.

   With the whole ΛCDM curve as reference (as RL19 do):
   - distance from the RL19 centre to the Taylor curve: 1.09, closest at Ω ≈ 0.58;
   - distance to the least-squares-fitted ΛCDM curve (z ≤ 5, uniform): 2.67, closest at Ω ≈ 0.68.

   Caveats:
   - Both displacements lie close to the long, degenerate axis of the RL19 ellipse (slope about −3 to −4). So Euclidean distance roughly tracks significance here, but a proper σ statement needs the data covariance, which is not printed.
   - The real fit weights (SNe dominate at z < 1.4) are not reproduced here.

4. **What the sentence would need, if any version survives.**
   - A theorem about fits over the data range: the least-squares or minimax cubic on [z_min, 5.1] under a stated weighting, not a two-point condition at z = 7.
   - A **direction** clause, for example the half-plane statement "every matching (a₂, a₃) satisfies n·(a − T) ≥ δ", with n pointing toward smaller a₂ and larger a₃.
   - Coverage of the whole ΛCDM curve that RL19 actually test against (Ω up to about 1).
   - The RL19 covariance, to convert distances into σ.

   On present evidence, the honest sentence is the opposite one: "Truncation moves ΛCDM's cubic image away from, not toward, the RL19 contour. Therefore the RL19/L19 4σ is not explained by the truncation of the cubic. It may still be mis-calibrated, because the Taylor point is not ΛCDM's fitted image (the variable-yardstick point)."

5. **Recommended additions** (all true by the numbers above):
   - raise the bound to 7/4;
   - add the half-plane/direction conclusion;
   - optionally widen Ω to [0.1, 1].

   Re-label the theorem as a "two-point (z = 3, 7) separation", not as a statement about fits.

## 4. Prior art

1. **Yang, Banerjee & Ó Colgáin 2020** (arXiv:1911.01681, PRD 102, 123532; read the arXiv PDF).
   - Fig. 1 plots the 4th-order log polynomial against exact ΛCDM: deviation stays under 1% up to z ≈ 4.3 for Ωm = 0.3, and appears at z ≈ 1–2 for other Ωm.
   - Their mock flat-ΛCDM data (Ωm = 0.3, 4th order) displace H₀, a₂ and a₃ by about 2σ.
   - They do not treat the cubic, make no Ω-uniform bound and give no direction analysis.

2. **Banerjee et al. 2021** (arXiv:2009.04109, PLB; read the arXiv PDF).
   - Fig. 1: Δd_L for n = 3, 4, 5 over Ωm = 0.1–0.9.
   - Fig. 3: **n = 3 fits to flat-ΛCDM mocks miss the ΛCDM curve by 8σ (Ωm = 0.1) and 6σ (Ωm = 0.9)**. They call these "phantom tensions", "simply an artifact of the expansion".
   - This is exactly the "cubic fitted to exact ΛCDM lands far from the ΛCDM point" claim, made with realistic RL19-like redshift distributions and errors. The direction in their figure matches mine (3.2), but they never compare it with the RL19 offset.

3. **Pourojaghi, Zabihi & Malekjani 2022** (arXiv:2212.04118) restate the point qualitatively ("cannot recover the flat-ΛCDM model at higher redshifts") but use z-, y- and Padé expansions. Bargiacchi et al. 2021 (arXiv:2101.08278) introduced orthogonal log polynomials partly in response; the earlier referee_b1.md §5 reports mock shifts of a₃ and a₄ by 0.7σ and 1.5σ.

4. **Novelty.**
   - The *phenomenon* is not new: a cubic matching ΛCDM sits far from the Taylor point. Banerjee et al. 2021 Fig. 3 shows it with mocks.
   - What is new: a **certified, Ω-uniform, offset-free** lower bound, and the explicit cone geometry.
   - The antiparallel direction relative to the RL19 contour (3.2) is something I did not find stated in these papers. It is the more interesting result and deserves its own statement.
   - The write-up must credit 2009.04109 for the mechanism.

Sources (arXiv only): https://arxiv.org/abs/1911.01681 , https://arxiv.org/pdf/1911.01681 , https://arxiv.org/pdf/2009.04109 , https://arxiv.org/pdf/2212.04118 . RL19 Fig. 3 was read from the repository crop runs/2026-10-31T0428Z/typeset/rl19_p9_fig3.png.
