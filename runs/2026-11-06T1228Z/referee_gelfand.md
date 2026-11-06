# Referee report: `Work.Math.Gelfand.gelfand_ball_critical` (frozen)

**Verdict: STANDS.** The statement is true. Its hypotheses can be met and determine w uniquely,
and there is no junk-value loophole. The stated intervals contain the true values, with about
3e-10 to spare below and 7e-10 above. The module doc is accurate. Section 1e lists what the
statement leaves out; these are notes, not corrections.

## 1. Attack on the statement

**a. The hypotheses determine the Emden solution (not vacuous, not contradictory).**
- φ is continuous on [0,S] (hφ, hφ0). On (0,S], (s²φ)' = −s²e^w; integrating and letting
  s₀ → 0 gives s²φ(s) = −∫₀^s t²e^{w}dt, so φ(0) = 0 (the doc's "w'(0) = 0 follows").
- Hence w(s) = −∫₀^s t⁻²∫₀^t r²e^{w} dr dt; since |Δφ(s)| ≤ (s/3)·sup|Δe^w|, Picard/Gronwall
  gives a unique w on [0,S].
- Existence for every S: the true Emden solution has φ < 0, so w ≤ 0 and |φ| ≤ s/3. It is
  therefore global on [0,∞) and meets every hypothesis, with one-sided derivatives at 0 and S.
  The conclusion is thus a statement about one function.

**b. Junk values: none.** 2/s is used only for s ∈ Ioc 0 S, so 2/0 never enters.
HasDerivWithinAt on Icc 0 S (S > 0) fixes a unique one-sided derivative at both ends. No
derivative of φ at 0 is needed (see a). The decimals elaborate (OfScientific) to exact rationals.

**c. Is the maximum global on [0,S] for every S ≥ 41/10? Yes.** Use t = ln s, v = s w' and
z = s²e^w (= Λ). Then z' = z(2+v) and v' = −v − z.
The only interior equilibrium is (−2, 2), a stable focus (trace −1, det 2); the regular orbit
leaves (0,0) as t → −∞. Lyapunov function: L = (v+2)²/2 + g(z), g(z) = z − 2 − 2 ln(z/2), with
dL/dt = (v+2)(−v−z) + (z−2)(2+v) = −(v+2)² ≤ 0. This vanishes only on v = −2, which holds no
orbit but the equilibrium, so L strictly decreases. g is convex, min 0 at z = 2, increasing on [2,∞).
Proof that the first maximum is global:
- On (0,s₁), where s₁ is the first zero of 2+v, z is strictly increasing.
- At s₁, z'' = z(2−z), and z₁ = z(s₁) ≈ 3.32 > 2.
- For s > s₁: g(z(s)) ≤ L(s) < L(s₁) = g(z₁). If z(s) ≥ 2 this gives z(s) < z₁. If z(s) < 2,
  then z(s) < 2 < z₁.
- So s₁ is the unique global maximiser on [0,∞); the conclusion holds for all S ≥ s₁ (41/10 > s₁).
- The successive local maxima strictly decrease towards 2. Numerically they are 3.3220 (at s =
  4.07), 2.1085 (at s = 429) and 2.0100 (at s = 4.9e4); the minima are 1.6642 and 1.9675.
- For S < s₁ the claim is false (the maximum would sit at S). The values S ∈ [s₁, 4.1) are true
  but not stated, which is harmless.
- This argument is elementary. It is probably the shortest route to the global part of the Lean
  proof: monotonicity of L plus a certified enclosure near s₁.

**d. Does it capture λ\* of the Gelfand problem in the 3-D ball?** Yes, as max_{s>0} s²e^{w(s)},
through the classical reduction in the doc:
- Every classical solution of Δu + λeᵘ = 0 in B₁ ⊂ ℝ³ with u = 0 on ∂B is positive (maximum
  principle) and radial (Gidas–Ni–Nirenberg 1979).
- So u(r) = w(sr) − w(s), λ = Λ(s), and the solvable set is Λ((0,∞)) = (0, λ*].

**e. What the statement does not capture.**
1. The PDE itself, and the identification λ* = sup{λ : a solution exists}: the scaling, the
   maximum principle, and GNN symmetry. Non-radial solutions are excluded only by GNN, which is
   not formalised.
2. Existence of w. The doc says this explicitly. Without existence the theorem would be vacuous,
   so a companion statement is needed before "λ* certified" can be claimed. Global existence is
   easy (see a).
3. w given only on [0,S] with S < s₁. The conclusion fails there, and hS excludes it.
4. Uniqueness of the maximiser. It is true (by c), but the conclusion only asserts ∃.
5. The bifurcation picture (infinitely many turning points about λ = 2, Joseph–Lundgren 1973).
6. Weak/extremal solutions (irrelevant for N = 3 < 10); δ_c = λ* only for radius 1 (standard).

## 2. Independent computation (python3, mpmath 1.3.0)

**Method A** (variable s): power series w = Σ aₙ s^{2n}, 80 terms, from aₙ₊₁(2n+2)(2n+3) = −bₙ
and n bₙ = Σ k a_k b_{n−k}, started at s₀ = 0.25; then mpmath.odefun (adaptive Taylor, degree 40,
tol 1e-42, 45 digits) and findroot on 2 + s w'(s). Series and ODE agree at s = 0.5 within 1e-47.

**Method B** (Emden–Fowler variables): own fixed-step Taylor integrator for (v, z), order 60,
step 1/16, 50 digits, with z_{k+1} = (2z_k + Σ z_j v_{k−j})/(k+1), v_{k+1} = −(v_k + z_k)/(k+1).
Start at t₀ = −12 from the exact series; v = −2 found by Newton on the local Taylor polynomial.

Results (A and B agree in all 35 printed digits):
```
s₁ = 4.0714968442981393476012090333447161
λ* = 3.3219921183398239884164780820029956
θ_m,c = −w(s₁) = ln(s₁²/λ*) = 1.6074567750838420289…
```

| quantity | above lower end | below upper end |
|---|---|---|
| s₁ | 2.98e-10 | 7.02e-10 |
| λ* | 3.40e-10 | 6.60e-10 |

Both intervals are correct but tight (relative width about 2.5e-10). The Lean proof therefore
needs certified error below about 3e-10 for both s₁ and λ*. Rational Taylor models with explicit
remainders can do this; it is the hard part of the formal proof.

## 3. Prior art (web search, 2026-11-06)

**Qualitative answer: in print, from numerical computation only.**
- [Wikipedia, Frank-Kamenetskii theory](https://en.wikipedia.org/wiki/Frank-Kamenetskii_theory)
  (raw wikitext checked) gives the sphere value "δ_c = 3.3220 … from numerical solution". It also
  gives θ_m,c = 1.6079, but the true value is 1.60746, so that figure is slightly off.
- [Wikipedia, Liouville–Bratu–Gelfand equation](https://en.wikipedia.org/wiki/Liouville%E2%80%93Bratu%E2%80%93Gelfand_equation)
  gives λ_c = 3.32 for n = 3 and infinitely many solutions for 3 ≤ n ≤ 9. It cites
  Joseph–Lundgren (ARMA 49, 1973, 241–269) and Jacobsen–Schmitt (JDE 184, 2002, 283–298).
- ANZIAM J. 59 (2018) 402–412, Table 1, gives δ_cr = 3.32 for the sphere:
  [PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/76752C3118003321394A8E73D043502F/S1446181117000578a.pdf/calculation_of_critical_parameters_for_spontaneous_combustion_for_some_complex_geometries_using_an_indirect_numerical_method.pdf).
- Two further papers print no high-precision sphere value: Rev. Mex. A&A 51 (2015) 173
  ([PDF](https://www.scielo.org.mx/pdf/rmaa/v51n2/v51n2a3.pdf)) and JNMP 15 S1 (2008) 69
  ([PDF](https://www.atlantis-press.com/article/1611.pdf)).

**Digits.**
- The most digits I could confirm in print are 3.3220 (5 significant figures).
- A search for "3.32199" pointed to two sources I could not open (paywall or client error), so
  6 digits there is possible but **unverified**:
  [Springer chapter 978-3-319-06923-4_21](https://link.springer.com/chapter/10.1007/978-3-319-06923-4_21)
  and the [Jacobsen–Schmitt JDE paper](https://www.sciencedirect.com/science/article/pii/S0022039601941518).
- The value s₁ ≈ 4.0715 did not turn up in any source.

**Rigorous enclosure: none found.**
- Searches for computer-assisted, interval or validated-continuation enclosures of the 3-D radial
  Gelfand fold, or of max ξ²e^{−ψ} for the isothermal sphere, found only unrelated work. Examples:
  [arXiv 1601.01543](https://arxiv.org/abs/1601.01543),
  [JCD 2018](https://www.aimsciences.org//article/doi/10.3934/jcd.2018003) and
  [DCDS-B 2024](https://www.aimsciences.org/article/doi/10.3934/dcdsb.2024181).
- This agrees with the doc's screen, although absence of evidence is not proof of absence.
- The phase-plane setting is classical (Joseph–Lundgren; Chandrasekhar's Milne variables).
  However, I found no printed proof that the first maximum is global together with certified
  digits.
- Not fetched: en.wikipedia.org via WebFetch (permission timeout; raw wikitext read with curl),
  wikiwand, ResearchGate, ScienceDirect (client errors). Downloads: /tmp/claude-0/ref/.
