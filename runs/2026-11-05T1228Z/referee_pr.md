**Verdict: STANDS-WITH-CORRECTIONS.** Both frozen statements say what the module doc says they say. They can be satisfied, are not vacuous and are true. Both rounding claims hold, and the Maxwell state is unique. The corrections are to the prose only:
- The finding is qualitatively in print, though I did not find the exact number.
- The question as framed in the doc tests the 1976 correlation outside the range where Robinson and Peng (1978) replaced it.

# Referee report: Work/Chemistry/PRAcentric.lean (frozen, run 2026-11-05T1228Z)

Files read:
- `Work/Chemistry/PRAcentric.lean`
- `Checked/Chemistry/CubicEOS.lean`, for `cubicP`, `IsCriticalIsotherm` and, for context, `isCritical_iff` and `pr_constants`
- `Checked/Chemistry/Coexistence.lean`, for `IsMaxwellCoexistence` and `acentric`
- `Checked/Records/Basic.lean`, for `RoundsTo`
- `runs/2026-11-04T1828Z/referee_rk.md`, for comparison

I did not read `runs/2026-11-05T1228Z/scripts/pr_float.py`, so my numerics are independent of it.

Scripts are in `runs/2026-11-05T1228Z/referee/`:
- `pr_routeA_fugacity.py`
- `pr_routeB_dimensional.py`

## 1. Fidelity

### What the Lean expressions say

- **Equation of state.** `cubicP R a b 2 (-1) T v = R*T/(v-b) - a/(v^2 + 2bv - b^2)` is Peng–Robinson.
- **κ(1).** `0.37464 + 1.54226 * 1 - 0.26992 * 1 ^ 2` is the PR 1976 κ(ω) at ω = 1. The decimal literals are exact rationals, and `^` binds tighter than `*`, so κ = 1.64698 exactly.
- **Attraction at 0.7 T_c.** `ac * (1 + κ (1 - √(7/10)))^2` is Soave's α at T_r = 0.7, with the correct sign.
- **Attraction at T_c.** On the critical isotherm the attraction is `ac`, which is α(1) = 1. This is correct.
- **Temperature.** The isotherm is taken at `7/10 * Tc`.
- **Critical pressure.** P_c is `cubicP R ac b 2 (-1) Tc vc`, the pressure at the critical point that `hc` asserts.
- **Critical-point condition.** `IsCriticalIsotherm` uses `deriv` in v at fixed T, so a(T) is constant there. That is the physical definition. T_c is fixed implicitly by `hc`, as in the RK file.
- **Coexistence.** `IsMaxwellCoexistence` is v_l < v_g, P(v_l) = P(v_g) = p_s and ∫_{v_l}^{v_g} P = p_s(v_g − v_l). This is the equal-area rule, valid at fixed T for any a(T).
- **Acentric factor and rounding.** `acentric ps pc = -logb 10 (ps/pc) - 1` is Pitzer's ω. `RoundsTo x d k` is |x − d| ≤ ½·10⁻ᵏ, so:
  - p_s/P_c ∈ [0.01135, 0.01145];
  - ω ∈ [0.9415, 0.9425].

### Quantifiers

- `pr_omega1_unique` is universal over R, a_c, b, T_c, v_c, v_l, v_g, p_s.
- `pr_omega1_exists` is universal over R, a_c, b, T_c, v_c, with ∃ v_l v_g p_s.

Both match the docstrings and the module doc.

### Hypotheses: minimal, and the essential ones block real junk

1. **No sign on R or T_c: correct, and a genuine strengthening.**
   - At v_c > b we have D = v_c² + 2bv_c − b² > 2b² > 0. So `isCritical_iff` applies and gives R·T_c·D² = a_c(v_c−b)²(2v_c+2b) > 0.
   - R and T_c enter only through R·T. `cubicP` uses `R * T`, and with T = 7/10·T_c this is (7/10)·R·T_c > 0.
   - α at 0.7 T_c uses the constant √(7/10), not T/T_c, so the sign of T_c never enters α.
   - The case R < 0, T_c < 0 is therefore the same fluid, and the conclusion is the same.
   - P_c > 0 follows from `pr_constants` (Z_c = 0.3074) and R·T_c > 0.
2. **`hac` is essential.**
   - With a_c = 0, `hc` forces R·T_c = 0, so both isotherms are identically 0.
   - Every v_l < v_g with p_s = 0 is then a "Maxwell state", and p_s/P_c = 0/0 = 0 in Lean, which falsifies the conclusion.
   - Without `hac` the uniqueness statement would be false.
3. **`hvc` is essential**, for the same reason as in the RK file.
   - At v = b, Lean's R·T/0 = 0 makes p non-differentiable, so `deriv p b = 0`.
   - `deriv (deriv p) b = 0` for the same reason.
   - So v = b would be a junk critical point for any T_c.
   - The pole of the attraction term, at v = (√2 − 1)b < b, is excluded too.
4. **`hl` is essential.**
   - If v_l < b < v_g, the integrand ~ RT/(v − b) is not integrable, and Mathlib's interval integral returns 0.
   - The "Maxwell" condition then demands p_s = 0. Pairs with P(v_l) = P(v_g) = 0 and v_l < b < v_g exist, which would give p_s/P_c = 0.
   - With v_l > b the integrand is continuous on [v_l, v_g], so all values are genuine.
5. **`hb`** is needed for D > 0 and for the scaling. It is physically natural.
6. **Junk values.**
   - Division by P_c is genuine, since P_c > 0.
   - `Real.logb` uses |x|. The first conjunct forces p_s/P_c ∈ [0.01135, 0.01145], so p_s/P_c > 0 and the log is genuine.
   - `Real.sqrt (7/10)` is genuine.
7. **Not vacuous.** Route B below solves the critical point from scratch (R = 8.314462618, a_c = 0.6, b = 4.5·10⁻⁵):
   - T_c = 272.849;
   - v_c/b = 3.9513730356;
   - Z_c = 0.3074013087, Ω_b = 0.0777960739, Ω_a = 0.4572355289.

   These agree with the closed forms, so the hypotheses are satisfiable. No junk value makes either conclusion automatic.

**Nothing is missing for truth.** The only extra assumptions a reader might expect are R > 0 and T_c > 0, and they are not needed (item 1).

## 2. Independent numerics (mpmath, 40–50 digits)

**Route A** (`pr_routeA_fugacity.py`) uses equal fugacity on the PR Z-cubic in (A, B) form, with no Maxwell areas and no reduced volumes:
- Z³ − (1−B)Z² + (A − 2B − 3B²)Z − (AB − B² − B³) = 0, with A = Ω_a·α·P_r/T_r² and B = Ω_b·P_r/T_r.
- ln φ = Z − 1 − ln(Z−B) − A/(2√2B)·ln[(Z+(1+√2)B)/(Z+(1−√2)B)].
- Ω_a and Ω_b come from the closed form X = [−1 + (6√2+8)^{1/3} − (6√2−8)^{1/3}]/3, with Ω_b = X/(X+3) and Ω_a = 8(5X+1)/(49−37X).
- The unknown is P_r, solved for ln φ_liq = ln φ_vap.

**Route B** (`pr_routeB_dimensional.py`) works in dimensional variables:
- The critical point comes from numerical first and second derivatives (no Ω constants).
- At 0.7 T_c the outer roots of the pressure cubic are found and ∫(P − p_s)dv is computed by quadrature.
- The equal-area p_s is the root of that integral.

| quantity | Route A | Route B |
|---|---|---|
| α(0.7) | 1.6104058455 | same |
| p_s/P_c | 0.011418053759550 | 0.011418053759550 (agrees to all 40 digits) |
| ω_out | 0.942407916538556 | 0.942407916538556 |
| v_l/b, v_g/b | | 1.214818057, 775.350409 |

The module doc's 0.9424, "≈ 0.058 short" (exactly 0.05759) and "≈ 14 % too high" (exactly 14.18 %) are all correct.

**Margins against the frozen windows:**

- **p_s/P_c ∈ [0.01135, 0.01145]:**
  - 6.81·10⁻⁵ above the lower end;
  - 3.19·10⁻⁵ below the upper end (relative 2.8·10⁻³).
- **ω ∈ [0.9415, 0.9425]:**
  - 9.08·10⁻⁴ above the lower end;
  - **9.21·10⁻⁵ below the upper end.**
- **The binding constraint is the ω upper end.** In pressure terms it needs p_s/P_c ≥ 10^{−1.9425} = 0.0114156330. The true value exceeds this by only **2.42·10⁻⁶**, a relative margin of 2.1·10⁻⁴. The proof's interval enclosure of p_s/P_c must be tighter than about 0.02 %, roughly 3× tighter than the RK proof needed (6.6·10⁻⁴).

### Uniqueness at 0.7 T_c: yes, the Maxwell state is unique for v_l > b

- **Spinodals.** On (b, ∞), P′ = 0 has exactly two roots:
  - v/b = 1.53417, with P_min/P_c = −10.668;
  - v/b = 21.6549, with P_max/P_c = 0.197654.
- **At most three crossings.** P = p_s is a cubic in v after clearing denominators, so it has at most 3 roots.
- **Equal area needs the outer roots.** ∫(P − p_s) = 0 forces P − p_s to change sign on [v_l, v_g]. So (v_l, v_g) must be the outer roots of a level with three roots in (b, ∞). This excludes consecutive-root pairs and tangent levels.
- **p_s ≤ 0 is excluded.**
  - P → 0⁺ as v → ∞, so a level p_s ≤ 0 has only 2 roots in (b, ∞), with P < p_s between them.
  - At p_s = 0 the cubic degenerates to a quadratic.
  - Checks at p_s = 0, P_min/2 and 0.99·P_min all gave 2 roots, with P − p_s < 0 in between.
- **Monotone area function.** The outer-root area function has derivative −(v_g − v_l) < 0 in p_s.
- **Scan.** 399 levels across (0, P_max) showed exactly one sign change.

So uniqueness is genuine, not weakened by spurious states.

## 3. Prior art

**Qualitative answer: yes, in print.** The statement that the 1976 κ(ω) gives too high a vapour pressure, i.e. too small an ω, for heavy compounds with large ω is published.

- **Robinson & Peng (1978), GPA Research Report RR-28.** It introduced κ = 0.379642 + 1.48503ω − 0.164423ω² + 0.016666ω³ for ω > 0.491, fitted to the vapour pressures of heavy components.
  - My computation: this κ at ω = 1 (1.716915) gives ω_out = **1.000089**.
  - The κ that reproduces ω = 1 exactly in PR is κ* = 1.716808.
  - So PR78 is, in effect, exactly the correction of the defect stated here.
  - I could not read RR-28 (not online).
- **DWSIM PR78 documentation** (dwsim.org/help/api/property-packages/peng-robinson-1978.html, read in full) says verbatim: "The 1976 m(ω) gives too high a vapor pressure for compounds with large acentric factors (alkanes heavier than n-decane, petroleum pseudocomponents), so they come out too volatile". This is web documentation, not peer-reviewed.
- **Pina-Martinez, Privat, Jaubert et al., Fluid Phase Equilib. 2019** ("Updated versions of the generalized Soave α-function…").
  - The abstract (ScienceDirect preview) reports "a substantial improvement … for heavy molecules with an acentric factor larger than 0.9".
  - The preview says Soave's 1972 m values were set to "exactly reproduce reduced vapor pressures at Tr=0.7", Pr^sat = 10^(−ω−1).
  - It does not say in the preview that PR76 fails at Tr = 0.7.
  - The full text (HAL hal-02136163) is behind a bot wall, so I could not read it.
- **Stryjek & Vera (1986), PRSV.** κ₀ = 0.378893 + 1.4897153ω − 0.17131848ω² + 0.0196554ω³ (coefficients confirmed at pychemqt.readthedocs.io).
  - The κ₁ term vanishes at T_r = 0.7.
  - My computation: κ₀(1) gives ω_out = **1.000114**, so this correlation is also self-consistent at ω = 1.
  - I could not read the paper's text: the scribd copy was denied by the permission classifier.

**Exact number in print: not found.** I searched for ω_out ≈ 0.942, the 0.058 shortfall and the 14 % excess at T_r = 0.7 for PR76 at ω = 1, including on arXiv. None of them appears in any source I could read. This is "not found", not "proved new": RR-28, the full Pina-Martinez 2019 text and Stryjek–Vera 1986 were unreadable, and any of them could tabulate this.

**Bookkeeping recommendation:** record this as a certified known effect, not a new result. At most, the specific number (0.942 at ω = 1) is "not located in print".

**Unverified recollection.** From memory, and not checked in this session: Peng & Robinson (1976) fitted κ to vapour pressures from the normal boiling point to the critical point, not at T_r = 0.7 specifically. If so, the doc's "κ(ω) is meant to make the equation reproduce that vapour pressure" overstates the design intent of PR76. That intent is Soave's for SRK.

## 4. Near misses (all confirmed false by Routes A/B)

| mutation | computed value | rounding window | false by |
|---|---|---|---|
| ω_out = 0.943 (3 dp) | 0.9424079 | [0.9425, 0.9435] | 9.2·10⁻⁵ (close, but false) |
| p_s/P_c = 0.0115 (4 dp) | 0.0114181 | [0.01145, 0.01155] | 3.2·10⁻⁵ |
| κ at ω = 0.5 instead of 1, claim 0.942 | ω_out = 0.496272 | | p_s/P_c = 0.031895 |
| SRK form (u = 1, w = 0) with PR κ(1), claim 0.942 | ω_out = 0.812803 | | p_s/P_c = 0.015389 |
| PR78 κ(1) = 1.716915, claim 0.942 | ω_out = 1.000089 | | |

The 0.943 mutation is false by less than 10⁻⁴. The proof's enclosure must separate it, which is the 2.4·10⁻⁶ margin from §2.

Context: ω_out for PR76 is
- −0.0028 at ω = 0;
- 0.2016 at ω = 0.2;
- 0.4963 at ω = 0.5;
- 0.7719 at ω = 0.8;
- 0.9424 at ω = 1.0;
- 1.1003 at ω = 1.2;
- 1.3104 at ω = 1.5.

The deficit grows past the 1978 switch point ω = 0.491. PR78 stays within 1.2·10⁻⁴ of ω over 0–1.5.

## 5. Verdict: STANDS-WITH-CORRECTIONS

1. **Both statements stand as frozen.**
   - They are faithful to PR with Soave α, PR76 κ(1), Pitzer ω at 0.7 T_c and Maxwell equal area.
   - The hypotheses are minimal. Not assuming signs for R and T_c is sound.
   - `hac`, `hvc` and `hl` each block a real junk counterexample.
   - Neither statement is vacuous or trivial.
2. **Both roundings are true.**
   - p_s/P_c = 0.01141805 rounds to 0.0114.
   - ω = 0.94240792 rounds to 0.942.
   - Proof work must enclose p_s/P_c from below to within 2.4·10⁻⁶, because ω is only 9.2·10⁻⁵ from 0.9425.
3. **Uniqueness is genuine:** there is exactly one Maxwell state with v_l > b at 0.7 T_c.
4. **Prose correction (prior art).** Do not book this as new. In print:
   - the qualitative effect (PR76 κ makes heavy compounds too volatile);
   - its fix, Robinson–Peng 1978 κ for ω > 0.491, which gives ω_out = 1.0001;
   - PRSV κ₀ also gives 1.0001.

   The module doc should:
   - cite Robinson & Peng 1978 (GPA RR-28);
   - say the computation evaluates the 1976 correlation outside the range where its authors replaced it;
   - present 0.942 as a certified value whose exact figure was not located in print.
5. **Prose correction (framing).** "The correlation κ(ω) is meant to make the equation reproduce that vapour pressure" should be softened to "κ(ω) was fitted to vapour pressures (Soave's construction matches T_r = 0.7 exactly)". It must not imply that PR76 was fitted at T_r = 0.7. That claim rests on my recollection of PR 1976 (see §3) and needs checking against the paper before it is printed.
