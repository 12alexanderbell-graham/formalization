# Interpretive choices (blind)

- Solution `w : ℝ → ℝ` is a hypothesis (structure `IsRegularGelfandSolution`), not constructed; the theorem is for every such `w`. Existence/uniqueness is not claimed.
- Regularity at 0: `ContDiffOn ℝ 2 w (Ici 0)` (C² up to the endpoint, one-sided). `w 0 = 0`; `w'(0) = 0` as `derivWithin w (Ici 0) 0 = 0`.
- Domain: only `s ≥ 0` matters; values of `w` on `s < 0` are unconstrained.
- ODE assumed only for `s > 0`, using `deriv (deriv w) s + 2/s * deriv w s + exp (w s) = 0` (on the open set (0,∞) `deriv` is the genuine derivative since w is C² there).
- Regularity at 0 is stated rather than a limit condition; "defined for every s ≥ 0" is encoded by `w` being a total function with the C² hypothesis on `Ici 0`.
- `λ(s) := s^2 * exp (w s)` (`gelfandLambda`). The reduction u(r) = w(sr) − w(s) is not formalized; only the branch λ is.
- Conclusion: `∃ ζ : ℕ → ℝ`, `StrictMono`, tends to `atTop`, numeric bounds on `ζ 0` and `λ(ζ 0)` as stated (real literals), then (i)–(viii).
- (i) quantified over `s ≥ 0`, `s ≠ ζ 0`. (ii)/(iii) over `s ≥ ζ(2k)` resp. `s ≥ ζ(2k+1)` (all reals above, not only up to the next turning point), excluding the named point.
- (iv) stated as `λ(ζ(2k+1)) < 2 ∧ 2 < λ(ζ(2k))`.
- (v) `Tendsto λ atTop (nhds 2)`.
- (vi)–(viii) as `StrictMonoOn`/`StrictAntiOn` on closed intervals `Icc`.
- "Turning points are exactly the ζ_k" (no other local extrema) is not stated separately; it follows from strict monotonicity on the consecutive intervals covering [0,∞) (vi–viii plus ζ → ∞).
- Not compiled; names assumed current (`Tendsto`, `atTop`, `nhds`, `Ici`, `Icc`, `StrictMonoOn`, `StrictAntiOn`).
