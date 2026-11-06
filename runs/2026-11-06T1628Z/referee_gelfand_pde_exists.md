# Referee report: `Work.Math.GelfandPDEExists.gelfand_pde_radial_exists`

**Verdict: STANDS** (true, not trivial or junk-satisfiable, faithful docstrings). One minor point
for the record: the margin is thin (3.4e-10 absolute) but holds up numerically.

Scope read: the module docstring and the theorem statement (lines 1-58 of
`Work/Math/GelfandPDEExists.lean`), plus Mathlib sources for `Δ`, `laplacian` and `ContDiffOn`.
The proof was not read. The first line of the proof (line 59, an `obtain` from a program lemma)
was visible in the read window and was not used. The companion file was not read: its content is
taken from the brief ("no radial classical solution for λ > 3.321992119").

Statement (verbatim, Mathlib-only definitions):
```
theorem gelfand_pde_radial_exists (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 3.321992118) :
    ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ 2 u (ball 0 1) ∧
      ContinuousOn u (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)
```

## 1. Truth: TRUE

Construction: w solves w'' + (2/s)w' + eʷ = 0 with w(0) = w'(0) = 0. This is the regular
Emden–Chandrasekhar (isothermal-sphere) solution, which is even and real-analytic near 0. Set
F(s) = s²e^{w(s)}. Then u(x) = w(k‖x‖) + log(k²/λ) gives
Δu = k²(w'' + 2w'/r)(kr) = −k²e^{w(kr)} = −λeᵘ. Also u = 0 on the sphere iff F(k) = λ. F is
continuous, F(0⁺) = 0 and F(s₁) = max F, so the intermediate value theorem gives k ∈ (0, s₁] for
every λ ∈ (0, F(s₁)]. The function u is a C^∞ radial function on all of ℝ³ (w is even and
analytic), so all five conjuncts hold.

Numerics:
- mpmath, 40 digits: the Taylor ODE integrator `odefun` (tol 1e-30), started at s₀ = 1e-6 from
  the series.
- Independent cross-check: scipy DOP853 with rtol 1e-13.

| quantity | mpmath | scipy |
|---|---|---|
| s₁ (root of 2 + s w'(s) = 0) | 4.071496844298139347601… | 4.071496844298007 |
| λ* = F(s₁) | **3.321992118339823988416…** | 3.3219921183397654 |

- Margin above the stated bound: λ* − 3.321992118 = **3.398e-10**. This is ~10²⁰ times the
  mpmath error and ~10³ times the scipy error.
- Room below the companion bound: 3.321992119 − λ* = 6.60e-10.
- F is increasing on (0, s₁] on a 20 000-point grid. Monotonicity is not needed for the argument;
  the IVT suffices.

Scripts: /tmp/gref/emden.py and /tmp/gref/check2.py. The bound 3.321992118 is λ* rounded down at
the 9th decimal, so it is as sharp as a 10-significant-digit constant allows. That is tight but
correct.

## 2. Triviality / junk: NOT junk-satisfiable

- **Δ is genuine.** `Δ` is `Laplacian.laplacian`, the scoped notation in
  `Mathlib/Analysis/Distribution/DerivNotation.lean:270`. The only function-space instance is
  `InnerProductSpace.instLaplacian` (`Laplacian.lean:138`), defined as
  `tensorIteratedFDerivTwo ℝ f x (canonicalCovariantTensor E)`, which equals
  ∑ᵢ iteratedFDeriv ℝ 2 f x ![eᵢ, eᵢ] (`laplacian_eq_iteratedFDeriv_orthonormalBasis`). The other
  instances are on 𝓢 and 𝓢′, so they cannot be selected here. It uses the global `fderiv`, so
  for non-differentiable u it would be the junk value 0.
- **ContDiffOn excludes the junk.** `ContDiffOn ℝ 2 u (ball 0 1)` takes
  `n : ℕ∞ω = WithTop ℕ∞`, and the literal `2` is the finite 2. The ball is open, so at each x
  in it u is `ContDiffAt ℝ 2`. Hence u is differentiable on a neighbourhood of x, `fderiv u` is
  C¹ at x, and `fderiv (fderiv u) x` is the true continuous second derivative. So Δu x is the
  classical ∑ ∂ᵢ²u(x) at every point where the equation is imposed, and the fderiv junk value
  cannot be used.
- **Constant witnesses fail.** u ≡ 0 gives Δu + λe⁰ = λ > 0, so it is not a solution. More
  generally, any witness is a genuine classical solution, which carries the full content of the
  near-sharp constant.
- **Radial clause is correct.** ∃ g, u x = g ‖x‖ on the closed ball. In an existence statement
  this extra conjunct only strengthens the claim. u off the closed ball is unconstrained, which
  is harmless.
- **Boundary and continuity are the standard classical setting.** "Zero on the sphere" and
  continuity on the closed ball together give C²(B) ∩ C(B̄).
- **λ ≤ 0 is excluded by `hpos`.** This is a scope restriction, not a defect. The claim would
  also be true there (u = 0 for λ = 0, and a unique solution for λ < 0 by monotonicity), and the
  docstring says so.

## 3. Near misses: CONFIRMED

- **Bound replaced by 3.3219922.** 3.3219922 > 3.321992119, so this λ falls in the companion's
  nonexistence range, and the modified statement is false provided the companion's hypotheses
  match these. The module doc says they do; I did not read the companion. Numerically,
  3.3219922 > λ* = 3.32199211834, so no radial solution exists. This follows from
  Gidas–Ni–Nirenberg plus Joseph–Lundgren, or directly from the ODE: a radial solution forces
  λ = F(k) ≤ max F.
- **Bound replaced by 3.321992119.** Also false, since 3.321992119 > λ*. The existence bound
  cannot be raised at the 9th decimal.
- **Order 2 replaced by 1, or Δ by Δ[s].** Not relevant to truth; the frozen form is the
  stronger, correct one.

## 4. Fidelity: FAITHFUL, no overclaims

- The theorem docstring restates the five conjuncts exactly.
- The module doc's "What is stated here" matches the statement, including "a function of ‖x‖
  alone on the closed ball".
- The claim that the two statements "locate λ* in [3.321992118, 3.321992119]" is correct as a
  combination with the companion: existence for all λ ≤ 3.321992118 gives sup ≥ that bound.
- "Not stated" (number of solutions, non-radial solutions, λ ≤ 0) is accurate.
- "Only Mathlib definitions occur" holds for the statement text. The imports pull in program
  modules (Checked.*, Work.*), but no program definition appears in the statement.
- Small wording nit: "classical solution" in the Question paragraph means C² in the open ball
  plus continuous up to the boundary. That is what is stated, so this is fine.
- Cannot check: "the hypotheses of the companion statement are exactly these". I did not read
  the companion, per scope. The lead referee should diff the two statements.

## 5. Prior art (brief)

- **Classical (from background knowledge, not fetched):**
  - Gelfand (1963): the problem.
  - Chandrasekhar (1939): the isothermal-sphere / Emden equation.
  - Joseph & Lundgren (1973, ARMA 49): the radial bifurcation diagram via the Emden transform.
    For N = 3 it oscillates around λ = 2, with the turning point λ* ≈ 3.32.
  - Gidas–Ni–Nirenberg (1979): positive solutions in a ball are radial.
- **Rigorous / computer-assisted enclosures:** the computer-assisted continuation and
  bifurcation literature exists (e.g. Miyamoto et al. on bifurcation diagrams; rigorous Chebyshev
  continuation). I know of no formal-proof-assistant (Lean/Isabelle/Coq) statement of existence
  up to a 10-digit λ*; this may be novel, but that is not verified.
- **WebSearch results (titles and URLs only; pages not read):**
  - https://arxiv.org/pdf/2309.00990 (Classification of bifurcation diagrams…, critical dimension)
  - https://arxiv.org/pdf/2404.04019 (Bifurcation diagrams… supercritical nonlinearities in two
    dimensions)
  - https://arxiv.org/pdf/2609.22689 (Efficient Rigorous Continuation via Chebyshev Series
    Expansion I)
  - https://arxiv.org/pdf/2207.03166 (Deep spectral computations…)
- **WebFetch:** none attempted.
