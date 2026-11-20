# Referee report: `Work.Math.GelfandPDEBound.gelfand_pde_bound`

File: `Work/Math/GelfandPDEBound.lean` (statement and docstring only; proof is `sorry`; nothing else read; no Lean run).

## 1. Fidelity
- Types and quantifiers: `lam : ℝ` and `u : EuclideanSpace ℝ (Fin 3) → ℝ` are universally quantified, and the conclusion is
  `lam ≤ 3.321992119`. That matches "every classical solution has λ ≤ λ*", with the decimal upper bound in place of λ*.
- Domain: `ball 0 1` and `closedBall 0 1` use the metric of `EuclideanSpace` (PiLp 2), so they are the Euclidean balls.
  `hb` covers every x with `‖x‖ = 1`, which is exactly the unit sphere. The same L2 norm is used throughout.
- Regularity: `ContDiffOn ℝ 2 u (ball 0 1)` means C² on the open ball. The literal `2` is the finite order
  `(2 : WithTop ℕ∞)`, not ω or ∞. `ContinuousOn u (closedBall 0 1)` gives continuity up to the boundary. This is the
  classical C²(B) ∩ C(B̄) setting, with no symmetry and no sign assumption on u.
- Laplacian: `Δ` (`InnerProductSpace.Laplacian`) is the trace of `iteratedFDeriv ℝ 2 u x` over an orthonormal basis. On
  `EuclideanSpace ℝ (Fin 3)` that is Σᵢ ∂²u/∂xᵢ². The ball is open and u is C² there, so at every x in the ball u is
  `ContDiffAt` order 2. The second derivative depends only on the germ at x, so `Δ u x` is the genuine Laplacian.
- Outside the closed ball: u is unconstrained there, and no hypothesis or conclusion depends on those values. This is harmless.
- Sign: `Δ u x + lam * exp (u x) = 0` is Δu + λeᵘ = 0, the Gelfand–Bratu convention, so λ > 0 is the interesting case.
- λ ≤ 0: the conclusion holds trivially, which is fine. All of ℝ is allowed for λ, as intended.
- Literal: `3.321992119 : ℝ` elaborates through `OfScientific` to the exact rational 3321992119/10⁹. It is not a float.
- Caveat: the file imports `Checked.Math.GSymFree`, which I did not inspect. If that module redefined `Δ`, added
  instances, or added notation, the reading above could change. I recommend a check that it only adds lemmas.

## 2. Junk values and satisfiability
- The junk value of `iteratedFDeriv` (0 where u is not twice differentiable) cannot occur inside the ball, because of `hu`
  on an open set. `hpde` quantifies only over the open ball, so the boundary is not involved. No hypothesis is vacuous.
- Mathematical truth: suppose λ > 0. Then Δu = -λeᵘ < 0, so by the maximum principle u ≥ 0 (in fact u > 0). So u is a
  supersolution and 0 is a subsolution. Monotone iteration (uₖ₊₁ solves -Δuₖ₊₁ = λe^{uₖ} with zero boundary values)
  stays radial and stays ≤ u, and gives a minimal radial classical solution. A regular radial solution is a rescaled
  Emden solution, so λ = s²e^{w(s)} for some s, and hence λ ≤ λ*. No GNN or boundary-C² regularity is needed.
- Satisfiable for positive λ: let w solve w'' + (2/s)w' + eʷ = 0 with w(0) = w'(0) = 0. Its profile is even and
  smooth. For any s > 0 put u(x) = w(s‖x‖) − w(s) on all of ℝ³ and λ = s²e^{w(s)}. Then u is smooth and u = 0 on
  ‖x‖ = 1. Also Δu = s²(w'' + 2w'/(s r)) = −s²eʷ = −λeᵘ. Every λ in (0, λ*] is attained, including λ* itself at
  s* ≈ 4.0715. So the hypothesis set is satisfiable for every λ ∈ (0, λ*].

## 3. The number
I used mpmath (40 and 55 digits) with the exact power series of w at 0, a recurrence carried to 200 terms. I then
integrated with mpmath's Taylor `odefun` from s₀ = 0.25 and, separately, from s₀ = 0.6. The maximum of s²e^{w(s)} is where
s·w'(s) = −2 (first root, found with `findroot`). The two runs agree to all 40 digits printed:
- s*  = 4.071496844298139347601209033344716
- λ*  = 3.321992118339823988416478082002996
- margin: 3.321992119 − λ* = 6.60176e-10 > 0, so the bound holds, and it is tight to about 7e-10.
- With 3.3219921 the statement is **false**: 3.3219921 − λ* = −1.83e-8 < 0, and λ* is attained by the radial solution at
  s*. Any bound below 3.32199211834 makes it false. (A spot check: λ(s) then decreases, to 2.38 at s = 10 and 1.68 at
  s = 30, consistent with the expected 3-D oscillation of the λ-curve about the singular value 2.)

## 4. Near-misses (variants that should be false)
- Drop `hb` (no boundary condition): u(x) = w(s‖x‖) + c with λeᶜ = s² solves the PDE for every λ > 0. Taking
  c = ln(s²/λ) breaks the bound for, say, λ = 100.
- Conclusion `lam ≤ 2` (the singular value) or `lam ≤ 3.3219921`: false, because the regular radial solution with
  λ ∈ (2, λ*] (for example λ = 3, or λ* itself) satisfies every hypothesis.
- Flip the sign (Δu − λeᵘ = 0): for λ > 0 the nonlinearity is monotone, and a (nonpositive) solution exists for every
  λ > 0. So no upper bound holds.
- Bound only the radial case and then claim "λ < λ*" strictly: false, because λ* is attained.

## 5. Verdict
**STANDS.** The statement faithfully says the intended claim. There is no Translation, Underspecified, or Source flaw.
Junk conventions do not weaken it, and the hypotheses are satisfiable for all λ ∈ (0, λ*]. The decimal bound is correct
and tight: λ* = 3.3219921183398239884…, which is below 3.321992119 by 6.6e-10. One minor follow-up: confirm that the
imported `Checked.Math.GSymFree` does not change the meaning of `Δ` or of any notation used.
