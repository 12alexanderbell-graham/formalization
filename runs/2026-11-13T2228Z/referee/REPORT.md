# Referee report: run 2026-11-13T2228Z, `bonnor_ebert_global`

(Returned as the referee subagent's final message — the harness refused its own write — and saved here by the main session without edits of substance.)

Files read: only the brief and `runs/2026-11-13T2228Z/lean/BonnorEbertGlobal.lean`. Lean was not run. Scripts in `runs/2026-11-13T2228Z/referee/scripts/`:
- `be_mass.py`: an exact power series for ψ out to ξ = 0.5, then mpmath's Taylor ODE solver at 30 digits.
- `be_global.py`: the (u,v) system, the Lyapunov bound, and the extrema up to ξ = 10⁶, using scipy DOP853 checked against mpmath.
- `xcheck_scipy.py`: an independent float check of ξ₁ and m₁.

## Verdict: **STANDS**

The statement correctly formalises "the critical Bonnor–Ebert sphere has the strictly largest dimensionless mass of all pressure-confined isothermal spheres." The hypotheses are not vacuous, the conclusion is not trivial, and the theorem is true. Its numeric windows hold with margins of about 1e-8 or more. The Lyapunov route the brief suggests closes the range [7, ∞) with a comfortable gap.

## 1. Attack on the statement

- **Sign convention and equation.** With w = −ψ, ψ'' + (2/ξ)ψ' = e^{−ψ} becomes w'' + (2/s)w' + e^{w} = 0; the Lean statement has φ' = −(2/s)φ − e^{w} with w' = φ. w(0) = 0 means ρ(0) = ρ_c.
- **Mass formula.** m = M G^{3/2} P_ext^{1/2} / c_s⁴ with M = 4πρ_c (c²/(4πGρ_c))^{3/2} ξ²ψ' and P_ext = c²ρ_c e^{−ψ} gives m = (4π)^{−1/2} ξ² ψ' e^{−ψ/2} = s²(−φ) e^{w/2} / √(4π), exactly the Lean formula. Check: 4π m² = u v³.
- **φ(0) and uniqueness.** (s²φ)' = −s² e^{w} on (0, S]; φ continuous at 0 ⇒ ε²φ(ε) → 0, so s²φ(s) = −∫₀ˢ t² e^{w}, φ(s) → 0, continuity forces φ(0) = 0. Volterra form w(s) = −∫₀ˢ r^{−2} ∫₀^r t² e^{w(t)} dt dr, Lipschitz bound L s²/6: unique near 0, regular elsewhere: unique on [0, S]. No junk solution meets the hypotheses; `hφ0` closes the singular-data gap. One-sided derivatives within Icc 0 S are harmless.
- **Existence and non-vacuity.** The isothermal solution is global (ψ ≥ 0, ψ' ≤ ξ/3); its restriction to [0, S] meets all hypotheses for every S ≥ 7.
- **Role of S ≥ 7.** Every radius lies in some [0, S] with S ≥ 7, every solution on [0, S] is the restriction of the unique global one; radii with S < 7 are covered by restricting to S = 7. So the statement is equivalent to "every radius of the global solution".
- **Quantifiers.** ξ₁ chosen after S, w, φ: harmless (unique solution, unique strict maximiser).
- **ξ₁ inside the domain.** [6.4507514, 6.4507515] ⊆ [0, 7] ⊆ [0, S].
- **Junk values.** m(0) = 0 < m₁; √(4π) > 0.
- **Triviality.** Not trivial: needs the whole oscillating tail. Docstring matches the formal statement.
- **Corrections needed.** None.

## 2. Independent computation

### First maximum
mpmath (30 digits) and scipy DOP853 agree to ≈ 1e-13.
- ξ₁ = 6.45075144417407 (4.42e-8 above the lower window end, 5.58e-8 below the upper).
- m₁ = 1.18222658849960 (8.85e-8 above the lower end, 1.15e-8 below the upper).
- 4π m₁² = 17.5635098653317.
- On a 2×10⁵-point grid m increases strictly on (0, ξ₁) and decreases strictly on (ξ₁, 8).

### Mass curve and its extrema
dm/dt ∝ uv³(2u − v): extrema where v = 2u. Traced to ξ = 10⁶; first four extrema checked with mpmath.

| ξ | type | m |
|---|---|---|
| 6.4507514442 | max | 1.1822265885 |
| 67.0075487196 | min | 0.6943665211 |
| 733.769243687 | max | 0.8306900583 |
| 7849.63204850 | min | 0.7879941879 |
| 84506.3289757 | max | 0.8009119501 |
| 907946.19 | min | 0.7969621752 |

- Damped oscillation towards the singular sphere's value √(2/π) = 0.7978845608; m(10⁴) = 0.7885175107.
- m(ξ) < m₁ for every ξ ≠ ξ₁: confirmed numerically.
- sup of m on [7, ∞) is m(7) = 1.17824547848; gap m₁ − sup = 0.00398111002.

### Lyapunov function
dV/dt = (1 − 1/u)·u(3 − u − v) + (1 − 2/v)·v(u − 1) = (u − 1)(3 − u − v) + (u − 1)(v − 2) = −(u − 1)² ≤ 0 (checked at 1000 random points, residual ≈ 1e-30). Needs u, v > 0 for ξ > 0, which holds because φ < 0.

At ξ = 7: u = 1.15523994816, v = 2.47174165415, **V(7) = 0.05912184311916**.

Max of uv³ on {V ≤ V(7)}: boundary maximum, Lagrange condition v = 3u − 1, u = 1.15686396322, v = 2.47059188966, **max uv³ = 17.4455765602** (20 000-ray brute force: 17.44557653), below 4π m₁² = 17.5635098653 by **0.1179333051**; i.e. m ≤ 1.17825076801 for all ξ ≥ 7.

## 3. Prior art (values read through WebFetch are UNVERIFIED)

- Chavanis 2002 (arXiv astro-ph/0103159v2, arxiv.org/pdf; UNVERIFIED): Milne variables, spiral around (1, 2), first instability as a local turning point; reportedly no global statement, no Lyapunov function.
- Lombardi & Bertin 2001 (arXiv astro-ph/0106336; UNVERIFIED): M_crit ≈ 1.18223 c_s⁴/√(G³μ³p_ext); no global proof, no Lyapunov function.
- Korman (arXiv 1610.05152; UNVERIFIED): Gelfand problem n = 3, infinitely many turns (Joseph–Lundgren); nothing on the first turn being global for the mass.
- Not read (memory only): Bonnor 1956, Ebert 1955, Chandrasekhar 1939 ch. IV, McCrea 1957 — spiral and mass maximum treated numerically/graphically.
- The Lyapunov function is the classical Volterra/Goh function of the Lotka–Volterra system du/dt = u(3 − u − v), dv/dt = v(u − 1) (Hofbauer–Sigmund); not found applied to the isothermal sphere.
- No rigorous or computer-assisted proof of the global statement found in print (standard-mode searches, not exhaustive).

## 4. Verdict: **STANDS**

Faithful formalization, true claim (gap 0.00398 on [7, ∞)), Lyapunov route with margin 0.118 in uv³. The m₁ window has only 1.15e-8 to spare at its upper end.
