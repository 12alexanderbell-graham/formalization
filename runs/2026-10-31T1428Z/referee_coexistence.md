# Referee report: `Work/Chemistry/Coexistence.lean` (frozen in run 2026-10-31T1228Z, commit 1432f15)

Referee under annex XL/XLVII.2. I did not read `runs/2026-10-31T1228Z/`. Scripts are in
`runs/2026-10-31T1428Z/referee/`: `certify_vdw.py`, `lean_certificate.py`, `lekner_check.py`, `junk_cases.py`
and `junk_checks.lean`, a Lean scratch file that compiles against the repo's Mathlib.
Downloads (Johnston arXiv:1402.1205 and a scan of Lekner 1982) are in `/tmp/referee`, outside the repository.

**VERDICT: STANDS-WITH-CORRECTIONS.** Neither statement has a Translation error. Both are true. The printed
decimals hold with margin. The requested corrections are two docstring wordings (item 6). Item 4 recommends
optional strengthenings, which the freeze rule allows at proof time.

Notation used below: x = v/b and π = p/P_c. Under the statement's hypotheses, R·T = 28a/(135b) and
P(v) = P_c·g(v/b), where

    g(x) = (28/5)/(x−1) − 27/x²   (= 8T_r/(3v_r−1) − 3/v_r², with v_r = x/3 and T_r = 0.7),
    G(x) = (28/5)·log(x−1) + 27/x  (an antiderivative of g on x > 1).

---

1. **The statements are faithful.**
   - **Equation of state.** `cubicP R a b 0 0 T v` = `R*T/(v−b) − a/(v^2 + 0*b*v + 0*b^2)`, which is the
     van der Waals equation RT/(v−b) − a/v². The argument order (R a b u w T v) is correct.
   - **Critical constants.** RT_c = 8a/(27b) and P_c = a/(27b²) follow from `vdW_constants`:
     Ω_a/Ω_b = a/(b·RT_c) = (27/64)/(1/8) = 27/8, and P_c = RT_c/(8b).
     The value `7/10*(8*a/(27*R*b))` is therefore 0.7 T_c.
   - **Maxwell construction.** `IsMaxwellCoexistence` is Maxwell's rule as printed by Lekner, Am. J. Phys.
     50, 161 (1982), eqs. (2)–(4): equal pressures, plus ∫_{v_l}^{v_g} P dv = p_e(v_g − v_l).
   - **Acentric factor.** `acentric` is Pitzer's ω = −log₁₀(p_r^sat)|_{T_r=0.7} − 1, with `Real.logb 10`
     equal to log/log 10.
   - **Literals.** `0.20046` and `-0.3020` elaborate to exact rationals.
   - **Junk at log.** `Real.logb` of a nonpositive argument would give log|x| (or 0 at x = 0). In the
     existence statement it is harmless, because `RoundsTo (ps/P_c) 0.20046 5` forces ps/P_c > 0.

2. **Junk values cannot produce spurious coexistence states.** I classified every triple
   (x₁ < x₂, π) on all of ℝ that satisfies `IsMaxwellCoexistence` for g. Lean's junk values are
   g(1) = −27 and g(0) = −28/5, since t/0 = 0. The interval integral of a non-integrable function is 0
   (`intervalIntegral.integral_undef`). 1/(x−1) is not integrable on any interval with 1 in [x₁, x₂]
   (`intervalIntegrable_sub_inv_iff`), and 27/x² is not integrable on any interval containing 0.
   - (a) **[x₁, x₂] contains 0 or 1, including as an endpoint.** The integral is 0, so π(x₂ − x₁) = 0 and π = 0.
     The zeros of g are 1.4156692 and 3.4057594, both above 1, and the junk values −27 and −28/5 are not 0.
     So there is no such state.
   - (b) **x₁ < x₂ < 0.** Here g′ = −2(14x³ − 135x² + 270x − 135)/(5x³(x−1)²) < 0, so g is strictly
     monotone and g(x₁) = g(x₂) is impossible.
   - (c) **0 < x₁ < x₂ < 1.** g has exactly one critical point in (0, 1), at 0.7787 (a maximum), so g is
     unimodal there. Then g > π strictly on (x₁, x₂), the integral exceeds π(x₂ − x₁), and the equal-area
     condition fails.
   - (d) **1 < x₁ < x₂.** Only the genuine solution survives (item 7).

   The same reduction works for any R ≠ 0, b ≠ 0 and a ≠ 0. A sign of a scales p_s and P_c together.
   b < 0 reflects the volume axis (x = v/b, and the order of the pair reverses).

3. **Uniqueness is not vacuous.** `vdW_coexistence_exists` supplies a state with v_l > b, so the
   hypothesis of `vdW_coexistence_unique` is satisfiable.

4. **Hypotheses: those in `vdW_coexistence_unique` are stronger than needed.** Uniqueness holds with `ha`
   alone, and even with only a ≠ 0.
   - `0 < a` is needed. At a = 0, P ≡ 0, so any v_l < v_g with ps = 0 satisfies the hypothesis, and
     ps/P_c = 0/0 = 0 does not round to 0.20046. `junk_checks.lean` proves that the statement fails at a = 0.
   - `hR` is not needed. If R ≠ 0, then R·T = 28a/(135b) whatever the sign of R. If R = 0, the junk value
     T = 8a/0 = 0 makes the isotherm −a/v² (Lean-checked). That isotherm is strictly monotone on each side
     of 0, and pairs across 0 fail as in 2(a), so the statement is vacuous.
   - `hb` is not needed. If b = 0, again T = 0 and the isotherm is −a/v², which is vacuous. If b < 0, the
     coexistence states lie at v < b, so `hl` makes the statement vacuous. Without `hl` it is still true,
     with the same π.
   - `hl : b < vl` is not needed, by item 2 (cases a–c).

   **Recommendation:** at proof time, drop `hR`, `hb` and `hl` from `vdW_coexistence_unique`. The theorem
   then says "every Maxwell coexistence state of the isotherm". The extra proof cost is the case analysis
   in item 2, plus `intervalIntegral.integral_comp_mul_left` for the scaling. If the author keeps them, a
   natural proof does use them (to cancel R and to stay on v > b), so the unused-hypothesis CI will not
   reject them. Either way, the docstring must match the hypotheses that remain.

   **In `vdW_coexistence_exists` every hypothesis is needed**, at least in a weak form:
   - R = 0 gives no coexistence state at all.
   - b ≤ 0 gives no state with v_l > b.
   - `0 < R` and `0 < a` could be weakened to `≠ 0`. This is optional; the positive versions are the
     physical ones.

5. **(Optional, for reuse) `IsMaxwellCoexistence` has no `IntervalIntegrable p volume vl vg` conjunct.**
   This is harmless for van der Waals at T_r = 0.7 (item 2). If the predicate is reused for another
   isotherm, two zeros of the isotherm on either side of a pole would satisfy it with ps = 0, because the
   junk integral is 0. Add the conjunct, or restrict to v > b, before reusing it for RK, PR or other
   temperatures. This is Underspecified (latent), not a defect in this file.

6. **Docstring corrections (Underspecified, wording only).**
   - **"Determined".** The module docstring says "the saturation pressure is determined, not just one
     solution". The theorem only pins every solution into a window of width 10⁻⁵. Either say "determined
     to five decimals", or add the exact statement: two Maxwell states at T = 0.7 T_c have equal ps. That
     exact statement comes free from the monotonicity argument in item 7.
   - **"From floating-point root finding".** "Textbooks quote ω ≈ −0.302 from floating-point root finding"
     attributes a method that no source states. Drop the clause or say "uncertified".
   - Everything else in the theorem docstrings matches the statements exactly.

7. **Plain-words uniqueness proof, organised for Lean.**
   - **Shape of the isotherm.** g′ = 0 ⇔ 14x³ − 135x² + 270x − 135 = 0. On (1, ∞) its roots are
     x_min = 1.7376044 and x_max = 7.1265424; the third root, 0.7787, is below 1. So g decreases on
     (1, x_min], increases on [x_min, x_max] and decreases on [x_max, ∞), with g → +∞ as x → 1⁺ and
     g → 0⁺ as x → ∞. The spinodal values are g(x_min) = −1.3504162 < 0 (negative minimum pressure)
     and g(x_max) = 0.3824298.
   - **The roots form an outer pair.** Write φ = g − π. A Maxwell pair 1 < x₁ < x₂ has φ(x₁) = φ(x₂) = 0
     and ∫φ = 0. φ has finitely many zeros: for x > 1, φ = 0 ⇔ c_π(x) := 5πx³ − (5π+28)x² + 135x − 135 = 0.
     So φ must change sign inside (x₁, x₂), which gives a third zero x_m. Then c_π has three roots above 1.
     That forces π ≠ 0, and π > 0 because the product of the roots is 27/π. By the shape of g, there is one
     root on each monotone piece, so x₁ = x₁(π) < x_min < x_m < x_max < x₂ = x₃(π) and π ∈ (0, g(x_max)).
   - **The residual is strictly decreasing (the lobe argument, no derivatives).** Write
     F(π) = ∫_{x₁}^{x₃}(g − π) = A(π) − B(π), where A = ∫_{x₂}^{x₃}(g − π) ≥ 0 is the upper lobe and
     B = ∫_{x₁}^{x₂}(π − g) ≥ 0 is the lower lobe. Take π < π′ and compare roots on each monotone piece:
     x₁′ < x₁, x₂′ > x₂ and x₃′ < x₃. Hence [x₂′, x₃′] ⊂ [x₂, x₃] and [x₁, x₂] ⊂ [x₁′, x₂′], so
     A(π′) < A(π) and B(π′) > B(π). This is just `integral_mono_on` plus monotonicity of the interval.
   - **Conclusion.** It is enough to certify F(0.200455) > 0 and F(0.200465) < 0. If π < 0.200455, then
     0 = F(π) ≥ F(0.200455) > 0, a contradiction; the upper side is symmetric. So π ∈ [0.200455, 0.200465].
     This needs only the reference roots at those two values of π, never the roots at the unknown π.

8. **Numbers, enclosed with interval arithmetic** (`certify_vdw.py`). Roots are bracketed by exact
   rational bisection; logarithms use `mpmath.iv` with outward rounding at 300 bits.

   | quantity | enclosure / value | rounding margin |
   |---|---|---|
   | F(0.200455) | +7.638705376·10⁻⁵ | > 0 |
   | F(0.200465) | −1.43929114·10⁻⁴ | < 0 |
   | p_s/P_c | [0.2004584670819355147329121, 0.2004584670819355147329122] | 3.467·10⁻⁶ above 0.200455; 6.533·10⁻⁶ below 0.200465 (half-unit 5·10⁻⁶) |
   | ω | −0.30202440495821074565… | 2.5595·10⁻⁵ above −0.30205; 7.4405·10⁻⁵ below −0.30195 |
   | v_l/b | 1.40157931456 (v_l/v_c = 0.4671931) | |
   | v_g/b | 23.4334171544 (v_g/v_c = 7.8111391) | |

   The 4-decimal rounding of ω already follows from the 5-decimal rounding of p_s/P_c: ω rounds to
   −0.3020 for all p_s/P_c in [0.2004241, 0.2004703], which contains [0.200455, 0.200465].

   Cross-checks:
   - Lekner's parametric solution (`lekner_check.py`) gives y* = Δs/2 = 2.011450951957963684 and the same
     p_s/P_c to 22 digits.
   - My transcription of the formulas (taken from Johnston's eqs. 78–79) reproduces Johnston's printed
     Table VI row y = 1: τ 0.90088, p 0.64971, n_g 0.42793, n_l 1.6543.
   - It also reproduces Johnston's printed Table IV row T/T_c = 0.70: p_X/p_c 2.005e−01, V_G/V_c 0.4672,
     V_C/V_c 7.811, V_F/V_c 0.5792, V_D/V_c 2.376 (the last two are the spinodals).
   - It reproduces Lekner's own printed limits (eq. 17): T* → 1 − Δs²/36 and p* → 1 − Δs²/9.

9. **The cheapest rigorous Lean route.**
   - **Uniqueness.**
     - Rescale to (x, π).
     - Do the junk case analysis (only needed if `hl`, `hb` and `hR` are dropped).
     - Prove the three-root structure and the lobe comparison (item 7).
     - Prove two numeric inequalities with the explicit rational certificate in `lean_certificate.py`.
       For each π ∈ {0.200455, 0.200465}, decimal brackets of width 10⁻⁸ for x₁ and x₃ are checked by
       `norm_num` signs of c_π. For example, at 0.200455: x₁ ∈ [1.40157954, 1.40157955] and
       x₃ ∈ [23.4339173, 23.4339174].
     - Then, writing x₁ ∈ [a₁, b₁] and x₃ ∈ [a₃, b₃]:

           F(π_lo) ≥ G(a₃) − G(b₁) − π_lo(a₃ − b₁) − (b₁ − a₁)(π_lo − g(b₁))
           F(π_hi) ≤ G(b₃) − G(a₁) − π_hi(b₃ − a₁) + (b₃ − a₃)(π_hi − g(b₃))

       These bounds hold because x₁ minimises and x₃ maximises Φ(s, t) = ∫_s^t(g − π), and g is
       monotone on the bracket. The bounds evaluate to +7.6387·10⁻⁵ and −1.4393·10⁻⁴.
     - The only transcendental input is one log per bound, log(55.864…), needed to about 1.3·10⁻⁵
       absolute. That is reachable from `Real.log_two_near_10` plus a few terms of the atanh series.
     - FTC applies with `G` on [x₁, x₃] ⊂ (1, ∞), via `integral_eq_sub_of_hasDerivAt`.
   - **Existence.**
     - Use Lekner's parametrization: x_g = 1 + e^{y}/f(y) and x_l = 1 + e^{−y}/f(y), with
       f(y) = (y cosh y − sinh y)/(sinh y cosh y − y), T_r(y) = 27f(f + cosh y)/(4g²) and
       p_r(y) = 27f²(1 − f²)/g², where g = 1 + 2f cosh y + f².
     - With E = e^y, both pressure equalities and the equal-area identity are rational identities in E and y.
       The log collapses exactly: log((x_g − 1)/(x_l − 1)) = log E² = 2y. All of this is checked in sympy
       in `lekner_check.py`.
     - Lean then needs `field_simp`/`ring` plus one IVT for T_r(y) = 0.7 on a bracket around
       y* = 2.0114510, using exp bounds. f > 0 for y > 0 gives b < v_l < v_g.
     - The rounding of ps and ω is then a corollary of uniqueness, plus log₁₀ bounds at 0.200455 and
       0.200465. No numerics on p_r(y) are needed.
   - **Not recommended:** implicit differentiation in π, i.e. dF/dπ = −(x₃ − x₁).

10. **Prior art and novelty.**
    - **The numbers are not new.** Wikipedia ("Acentric factor") prints ω ≈ −0.302024 for the
      van der Waals fluid, and corresponding-states talk slides from U. Houston quote ω = −0.302.
      Johnston, arXiv:1402.1205, Table IV, prints p_X/p_c = 2.005e−01 at T/T_c = 0.70, with v_l, v_g and
      the spinodals.
    - **The mathematics is classical.** Lekner 1982 (parametric in Δs), building on Gibbs/Wilson,
      Benson–Copeland 1955 and Rowlinson 1958, gives exact parametric coexistence. Monotonicity of the
      equal-area residual is the standard textbook argument.
    - **Rigorous numerics exist for related problems.** Hua, Brennecke and Stadtherr (1996–98) used
      interval-Newton methods to certify phase stability for cubic EOS mixtures. They do not report a
      certified vdW p_s(0.7 T_c) or ω.
    - **No proof-assistant work found.** Searches of Lean/Isabelle/Coq work found no machine-checked
      Maxwell construction, coexistence uniqueness or acentric factor:
      - Bobbin et al., Digital Discovery 2024 (Langmuir/BET, gas laws), and the LeanChemicalTheories
        library: no EOS or phase equilibrium.
      - Josephson, AIChE 2025: Helmholtz energy and ideal gas only.
      - LeanLJ (arXiv:2505.09095): Lennard-Jones energies.
      - arXiv:2201.04009 analyses vdW roots but assumes the Maxwell rule and has no formal proof.
    - **Assessment.** A Lean-certified vdW saturation pressure and acentric factor, with uniqueness of the
      Maxwell pressure, appears new as a formalization; the claim should be worded "to our search". It is
      not new as mathematics or as a number. The printed −0.302 (and −0.302024) agree with the certified
      value, so there is no Source error.
