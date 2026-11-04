# Referee report: Work/Chemistry/RKAcentric.lean (frozen, run 2026-11-04T1828Z)

Files read: `Work/Chemistry/RKAcentric.lean`; `cubicP`, `IsCriticalIsotherm` (Checked/Chemistry/CubicEOS.lean);
`IsMaxwellCoexistence`, `acentric` (Checked/Chemistry/Coexistence.lean); `RoundsTo` (Checked/Records/Basic.lean).
I also looked at the `rk_constants` statement in CubicEOS.lean to see what the critical hypothesis pins down.

**Verdict: STANDS-WITH-CORRECTIONS.** The two Lean statements are faithful, can be satisfied and are true.
The corrections are to the prose only: the number is already in the literature (item 9).

## 1. Fidelity

- `cubicP R a b 1 0 T v = R*T/(v-b) - a/(v^2 + b*v)`. With a = A/√T this is RK, P = RT/(v−b) − A/(√T·v(v+b)). The
  critical isotherm uses `A / Real.sqrt Tc` at temperature `Tc`. The coexistence isotherm uses
  `A / Real.sqrt (7/10*Tc)` at `7/10*Tc`. Both match the module doc.
- P_c is `cubicP R (A/√Tc) b 1 0 Tc vc`, the pressure at the critical point that `hc` asserts. Correct.
- `IsCriticalIsotherm` takes `deriv` in v at fixed T, so a(T) is constant there. That is the physical definition of the
  critical point for a T-dependent attraction parameter. T_c is fixed implicitly by `hc` rather than by a formula,
  which is the stronger and more faithful form.
- `IsMaxwellCoexistence` is v_l < v_g, P(v_l) = P(v_g) = p_s, and ∫_{v_l}^{v_g} P = p_s(v_g − v_l). This is the
  standard equal-area rule, and it is valid at fixed T for any a(T).
- `acentric ps pc = -logb 10 (ps/pc) - 1` is Pitzer's ω. `RoundsTo x d 3` means |x − d| ≤ 5·10⁻⁴. The literals
  0.087 and 0.058 are exact rationals.
- Quantifiers: (1) holds for all R, A, b, T_c, v_c, v_l, v_g, p_s under the hypotheses. (2) holds for all
  R, A, b, T_c, v_c under the hypotheses, with ∃ v_l v_g p_s. Both are what the docstrings say.

## 2. Hypotheses and junk values

1. `hvc : b < vc` is **essential**, not decoration. At v = b, Lean's `RT/0 = 0` makes p non-differentiable, so
   `deriv p b = 0`. `deriv (deriv p) b = 0` for the same reason. Without `hvc`, v = b would be a junk "critical
   point" for every T_c. The same applies at v = 0 and v = −b. With v_c > b, p is smooth on the open set (b, ∞),
   so both derivatives are genuine.
2. `hl : b < vl` is **essential**. For v_l ≤ b the integrand is not integrable across b, Mathlib's interval
   integral returns junk, and spurious "coexistence states" could follow. With v_l > b > 0 the integrand is
   continuous on [v_l, v_g].
3. `hR` is redundant. R·T_c > 0 follows from `hc`, A > 0 and T_c > 0 (`rk_constants`, Z_c = 1/3). `hA` is
   implied by `hc` in practice. `hTc` is needed for √T_c. All of these are physically natural and none is too
   strong. A scientist would read the statement the same way.
4. Division: P_c = R·T_c/(3·v_c) > 0, so p_s/P_c is genuine. Log: `Real.logb` uses |x|, so the ω conjunct alone
   would not exclude p_s < 0. The first conjunct does exclude it, since it forces p_s/P_c ∈ [0.0865, 0.0875].
5. Not vacuous. From `rk_constants`, a = Ω_a(RT_c)²/P_c and b = Ω_b·RT_c/P_c. So T_c^{3/2} = Ω_b·A/(Ω_a·R·b)
   has exactly one positive solution, and v_c = 3.8473221·b. I solved the two derivative equations
   numerically from scratch for R = 8.314462618, A = 1.5e6, b = 3e-5. The result was v_c/b = 3.84732210,
   Z_c = 0.333333…, so the hypotheses are satisfiable.
6. Not trivially true. No junk value makes either conclusion automatic.

## 3. Independent numerics (mpmath, 40 digits; script in the session scratchpad, not in the repository)

- Route A: equal fugacity on Z³ − Z² + (A_r − B_r − B_r²)Z − A_r·B_r = 0 with Ω_a = 1/(9(2^{1/3}−1)),
  Ω_b = (2^{1/3}−1)/3, A_r = Ω_a·P_r/T_r^{2.5}, B_r = Ω_b·P_r/T_r, and ln φ = Z − 1 − ln(Z−B) − (A/B)·ln(1+B/Z).
- Route B: dimensional variables with the critical point solved from numerical derivatives (no Ω constants).
  Coexistence came from outer roots of the pressure cubic and adaptive quadrature of ∫(P − p_s) dv.

| quantity | Route A | Route B |
|---|---|---|
| p_s/P_c | 0.0874420 (0.08744198319) | 0.0874420 (agrees to 38 digits) |
| ω | 0.0582800 (0.05828000112) | 0.0582800 |
| v_l/b, v_g/b | | 1.394793, 84.38901 |

Margins to the frozen windows:
- p_s/P_c ∈ [0.0865, 0.0875]: 5.80·10⁻⁵ to the upper end (relative 6.6·10⁻⁴) and 9.42·10⁻⁴ to the lower end.
- ω ∈ [0.0575, 0.0585]: 2.20·10⁻⁴ to the upper end and 7.80·10⁻⁴ to the lower end.

Both are correct. The p_s/P_c window is tight at the top, so the proof needs interval bounds better than about 0.06%.
The module doc's values 0.08744 and 0.0583 agree with mine.

Cross-check: Soave's m(ω) = 0.480 + 1.574ω − 0.176ω² gives α(0.7) = 0.7^{−1/2} when m = 0.570988, that is
ω = 0.05819. This is consistent, as expected, because Soave fitted α to p_s(0.7 T_c) = P_c·10^{−1−ω}.

**Other Maxwell states (v_l > b)?** None. On this isotherm P′ = 0 has exactly two roots in (b, ∞): v/b = 1.82206
(P_min/P_c = −3.40904) and v/b = 12.8007 (P_max/P_c = 0.299359). P = p_s is a cubic, so it has at most 3 roots.
If ∫(P − p_s) = 0 over [v_l, v_g], then P − p_s must change sign inside, so v_l and v_g must be the outer roots of a
3-root level. That rules out consecutive-root pairs, tangent levels and p_s ≤ 0 (for p_s ∈ (P_min, 0] the two roots
enclose P < p_s). The outer-root area function has derivative −(v_g − v_l) < 0, so it is strictly decreasing in p_s.
A 399-level scan over (0, P_max) found exactly one sign change. The physical state is the only one, so the
uniqueness theorem is not weakened by spurious solutions.

## 4. Prior art

- **Published.** N. Shamsundar and J. H. Lienhard, "Saturation and Metastable Properties of the van der Waals
  Fluid", *Can. J. Chem. Eng.* 61 (Dec 1983) 876–880, gives in passing "ω = −0.302 for a van der Waals fluid,
  0.058 for a Redlich-Kwong fluid". The paper also uses Z_c = 1/3 for RK. Source: open PDF at
  engines.egr.uh.edu/sites/engines/files/talks/correspondingstatesspinodal.pdf (OCR text).
  - The paper does not write out the RK temperature dependence.
  - A single ω for "the RK fluid" can only mean the original A/√T form, since SRK takes ω as an input.
  - The OCR snippet confirms the value; I did not read the full context.
- Qualitative: Wikipedia's Redlich–Kwong article attributes to Barner et al. (1966) that RK "worked best for
  molecules with an acentric factor (ω) close to zero", and says Schmidt–Wenzel reduces to RK at ω = 0.
- Implied: Soave (1972)'s m(ω) correlation puts the RK α at T_r = 0.7 at ω ≈ 0.058 (my computation above, not a
  printed statement I could verify).
- Blocked, not read:
  - Soave 1972 PDF at lab.semi.ac.cn: denied by the permission classifier.
  - scribd copies: denied.
  - hal.univ-lorraine.fr/hal-02136163: bot wall.
  - en.wikipedia.org/wiki/Redlich-Kwong_equation_of_state: the permission request timed out. The %E2%80%93 URL
    worked.
- No arXiv sources were used.

**Conclusion:** both the 3-decimal answer ω = 0.058 and the qualitative answer (RK suits nearly simple fluids,
ω ≈ 0.06) were published by 1983. The contribution here is a certified bound and uniqueness, not a new number.

## 5. Verdict: STANDS-WITH-CORRECTIONS

1. Both statements stand as frozen. They are faithful to RK, Pitzer ω at 0.7 T_c and Maxwell equal area. The
   hypotheses are natural, `hvc` and `hl` block real junk, and the statements are not vacuous and not trivial.
2. Both rounding claims are true: p_s/P_c = 0.0874420 → 0.087 and ω = 0.0582800 → 0.058. Proof work should note
   the tight upper margin of 5.8·10⁻⁵ on p_s/P_c.
3. Uniqueness is genuine: there is exactly one Maxwell state with v_l > b at 0.7 T_c.
4. Correction (docs only): the module doc should cite Shamsundar & Lienhard (1983), who give ω = 0.058 for the RK
   fluid. It should also cite Barner et al. (1966, via Wikipedia) for the qualitative "ω ≈ 0" suitability. The doc
   must not present the value as new; the result certifies a known number.
5. Optional: `hR` (and arguably `hA`) is redundant given `hc` and `hTc`. It is harmless and can stay frozen.
