# Referee report: Robertson stiff network, certified state at t = 40

Files read: `Work/Sim/Robertson.lean` (frozen statements), `Work/Sim/OneSided.lean` (method). No other repo files.
Scratch: /tmp/referee_rob/ (sci.py: scipy run; gl.py: mpmath Gauss–Legendre collocation solver).

## 1. Attack on the statements

**Mass-action system.** Network: A → B (k₁), B + C → A + C (k₂), 2B → B + C (k₃).
- A → B, rate k₁y₁: −k₁y₁ in y₁, +k₁y₁ in y₂. Matches.
- B + C → A + C, rate k₂y₂y₃: A +1, B −1, C net 0 (catalyst), so +k₂y₂y₃ in y₁, −k₂y₂y₃ in y₂, none in y₃. Matches.
- 2B → B + C, rate k₃y₂²: B net −1, C +1, so −k₃y₂² in y₂, +k₃y₂² in y₃. Matches. This is the standard
  Robertson convention (rate k₃y₂², not 2k₃y₂² or ½k₃y₂²): y₂′ = 0.04y₁ − 10⁴y₂y₃ − 3·10⁷y₂².
- The right-hand sides add to 0, so y₁+y₂+y₃ = 1 is conserved. Constants: 1/25 = 0.04, 10000 = 10⁴,
  30000000 = 3·10⁷. Initial state (1,0,0). The argument order matches its uses.
- `y₂ t ^ 2` parses as `(y₂ t)^2`. There is no division by variables and there are no junk values: only y(0) and y(40) are read.
- Cosmetic only: Hairer–Wanner and the Bari test set call the 2B reaction k₂ = 3·10⁷ and the B+C reaction
  k₃ = 10⁴. The Lean file swaps the labels, but each goes with the right term, so the ODE is identical.

**Hypothesis form.** `HasDerivWithinAt … (Icc 0 T) t` for all t ∈ [0,T] gives the ordinary derivative inside and
one-sided derivatives at 0 and T. It also implies continuity on [0,T]. This reads the IVP faithfully.
- Uniqueness: the field is polynomial, hence locally Lipschitz, so a solution is unique (Grönwall), and "every
  solution" means "the solution".
- Not vacuous: the solution exists on [0,∞). Picard–Lindelöf gives a local solution, the orthant is invariant, and
  with conservation the solution stays in the simplex, so it never blows up.
- Not over-strong: values outside [0,40] are unconstrained.

**Need for `rob_exists`.** Yes. `rob_state40` is universal, so on its own it holds vacuously if no solution exists.
"Certified state at t = 40" therefore means `rob_state40` ∧ `rob_exists`, and both are still `sorry`.
`rob_exists` is true by the argument above, via Mathlib's Picard–Lindelöf plus the a-priori simplex bound. The
claim must not be reported as done until both are proved. Uniqueness is not needed separately.

**Bridge to the method (no defect).** `onesided_cell` and `rob_onesided` use the *reduced* 2-D field with
y₁ = 1 − y₂ − y₃. The proof must (i) derive conservation from `IsRobSolution`, (ii) pass from Icc-within to
`Ici t`-within derivatives for t < 40 (valid, since Icc t 40 ∈ 𝓝[≥] t), and (iii) bound y₁ by |e₁| ≤ |e₂| + |e₃|. All routine.

**Docstring inaccuracy (not the statement).** The docstring says "the Jacobian has an eigenvalue of size ≈ 10⁴ for
most of [0,40]". The computed stiff eigenvalue along the trajectory is −1.7e3 (t = 1e-3), −2.2e3 (t = 0.1–1),
−2.6e3 (t = 10) and −3.4e3 (t = 40), with a slow eigenvalue of about −0.3 to −0.02. Suggested wording: "≈ 2–3·10³".

## 2. Independent numerical derivation of y(40)

(a) scipy 1.18.1 on the full 3-variable system with an analytic Jacobian: Radau, BDF and LSODA at rtol 1e-10, 1e-12
and 1e-13 (atol 1e-14, 1e-20, 1e-14). All nine runs agree to within about 1.3e-10 in y₁ and y₃ and about 5e-15 in y₂.
(b) My own s-stage Gauss–Legendre collocation (implicit, A-stable, order 2s) in mpmath at 40 digits with full Newton
iteration, on a geometric mesh from 1e-9 to 40. I ran (N, s) = (300,4), (1000,4), (2000,4), (2000,5), (4000,5) and
(4000,6). The last three agree to at least 20 digits in y₁ and y₃ and to 15 digits in y₂. Conservation holds to 1e-40.

Converged values: y₁(40) = 0.71582706871940509047, y₂(40) = 9.18553476455776e-6, y₃(40) = 0.28416374574583035176.
The Bari test-set reference [1] lists only t = 1e11 values. I could not access a Hairer–Wanner t = 40 table and
do not quote one from memory.

| comp | frozen interval | true value | lower margin | upper margin |
|---|---|---|---|---|
| y₁ | (0.7158270, 0.7158271) | 0.715827068719405 | 6.87e-8 | 3.13e-8 |
| y₂ | (9.1855e-6, 9.1856e-6) | 9.185534764558e-6 | 3.48e-11 (rel 3.8e-6) | 6.52e-11 |
| y₃ | (0.2841637, 0.2841638) | 0.284163745745830 | 4.57e-8 | 5.43e-8 |

**All three intervals contain the true value.** The numerical error (≤ 1e-15) is far smaller than any margin.

The binding constraint for the proof is y₂. With w = 4900, |e₂| ≤ R/70, so the final radius must satisfy
R(40) ≲ 70 · 3.48e-11 ≈ 2.4e-9. y₁ needs |e₂| + |e₃| < 3.1e-8. This is tight but reachable with high-order
defect-controlled approximants. Since `onesided_cell` requires μ ≥ 0, defects accumulate additively.

## 3. `onesided_cell` statement check

The statement is **true** (I checked the mathematics and read the proof; it has no sorry). The argument:
- Let R(t) = (δ + ε(t−a))e^{μ(t−a)}, so R′ = εe^{μ(t−a)} + μR.
- Where φ = R², f is in the B-ball (because R ≤ B), so the one-sided bound applies. Together with weighted
  Cauchy–Schwarz on the defect it gives φ′ ≤ 2μR² + 2|⟨e,D⟩_w| < 2μR² + 2Rε ≤ (R²)′.
- The strict comparison lemma `image_le_of_deriv_right_lt_deriv_boundary'` closes the argument.

Weaknesses, none of which makes the statement false or vacuous:
- (i) μ ≥ 0 is required, so contraction cannot be exploited and the radius never shrinks across cells. This costs
  sharpness, not soundness.
- (ii) `hos` is centered at g(t) and required only on the B-ball. This is the right, weaker-than-global form, and
  `rob_onesided` discharges it for the reduced field.
- (iii) P and Q must be autonomous. That is fine here.
- (iv) ε, δ > 0 and the strict defect inequality are harmless, since any positive slack works.
- (v) The conclusion holds only in the weighted norm. Coordinate bounds come via `ball_bounds`.
- (vi) The hypotheses are satisfiable for Robertson. The `rob_core` condition Cm² ≤ 4μ(wA − K₀B + wμ) is easy where
  A ≈ 2k₃x₂ + k₂x₃ ≈ 3·10³ (t ≳ 1e-3). Near t = 0, A ≈ 0.04 forces a larger μ, which costs the proof but is not a statement flaw.

## 4. Prior art

- **Floating-point values.** These are in print. Robertson (1966) posed the problem on [0, 40]. The Bari test set [1]
  gives RADAU reference values at 1e11 only. Standard solver demos print 5-digit t = 40 values: SUNDIALS cvRoberts_dns
  and MATLAB hb1ode, which I recall but could not fetch. None is certified. So the values themselves are known, and the
  certified enclosure is the new part.
- **Validated (interval) enclosures of Robertson.** Zhang & Yap, "Covers for Initial Value Problem: Complete Validated
  Algorithms with Complexity Analysis", arXiv:2602.00162 (Feb 2026) [2], treat "Reduced Robertson (2D)" (Eg6) with the
  same constants and an initial box of radius 1e-6.
  They report validated end enclosures **only at T = 1** (their method, VNODE-LP, CAPD; printed (0.97, 0.00) ± (0.00, 0.00)).
  This is validated numerics, not a formal proof, and must be cited. No validated t = 40 enclosure found; [3] omits Robertson.
- **Proof-assistant enclosures.** The precedents are Immler's Isabelle/HOL verified ODE solver for the Lorenz attractor
  [4] and the Coq certified-solver work [5]. I found **no** formally verified enclosure of Robertson or of any stiff
  chemical ODE (web-only search, not exhaustive). A "first" claim needs "to our knowledge" and citations of [2] and [4].

[1] https://archimede.uniba.it/~testset/report/rober.pdf
[2] https://arxiv.org/abs/2602.00162
[3] https://arxiv.org/pdf/2502.00503v1
[4] Immler, "A Verified ODE Solver and the Lorenz Attractor", https://d-nb.info/1154862003/34
[5] "Extraction of a computer-certified ODE solver", https://arxiv.org/abs/2104.02536

## Verdict

**STANDS-WITH-CORRECTIONS.**

What stands:
- The frozen statements are the correct Robertson mass-action IVP; stoichiometry, signs and constants are checked.
- The hypothesis form is faithful and non-vacuous, and there are no junk values.
- All three intervals contain the true y(40), with margins 3.1e-8 (y₁), 3.5e-11 (y₂, rel 3.8e-6) and 4.6e-8 (y₃).
- `onesided_cell` is true and sorry-free.

Corrections:
- (1) The state counts as certified only when *both* `rob_state40` and `rob_exists` are proved. Both are `sorry` now,
  and `rob_state40` alone is vacuously true if no solution exists.
- (2) Fix the docstring's "eigenvalue ≈ 10⁴" to about 2–3.4·10³.
- (3) The writeup must cite Zhang–Yap 2026 (validated Robertson at T = 1 via VNODE-LP/CAPD) and say that t = 40 values
  exist in print from floating-point solvers, none of them certified.
