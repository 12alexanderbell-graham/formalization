# Interpretive choices (blind restatement)

- Solution class: `IsRegularSol w φ`: `w 0 = 0`; for all s >= 0, `HasDerivWithinAt w (φ s) (Ici 0) s`;
  `φ` continuous within `Ici 0` at 0; for s > 0, `HasDerivAt φ (-(2/s) * φ s - exp (w s)) s`.
  No condition on `φ 0` imposed. Theorem quantifies over all such `w φ`.
- `lam w s = s^2 * exp (w s)`. The singular value 2 appears only as the literal limit/threshold.
- Turning points: no derivative characterisation; they are given by a sequence `ζ : ℕ → ℝ`, `StrictMono`,
  tending to atTop, with global strict max at `ζ 0` over `s >= 0`, and for each k `ζ (2k+1)` strict min over
  `Ici (ζ (2k))` and `ζ (2k+2)` strict max over `Ici (ζ (2k+1))` (strictness written as `s ≠ ζ_j → strict ineq`).
- Index convention: `ζ 0` is the first (global max) turning point; even indices are maxima, odd are minima.
  (iv) uses `n >= 0` with ratios `ζ(n+7)/ζ(n+6)`, i.e. indices from `ζ 0` as in the statement.
- Monotonicity: `StrictMonoOn`/`StrictAntiOn` on closed intervals `Icc`.
- Limits: `Tendsto ... atTop (nhds _)`; `λ(s) → 2` as real s → atTop. Ratio limit is
  `(λ(ζ_{k+1}) - 2)/(λ(ζ_k) - 2) → -exp(-π/√7)`, `ζ_{k+1}/ζ_k → exp(2π/√7)`.
- Numeric intervals as `Icc` with decimal real literals; bounds in (iv) as `|a - b| <= (47/100)*(33/100)^n`
  and `(3/100)*(33/100)^n`. `-π/√7` parsed as `(-π)/√7`, equal to `-(π/√7)`.
- Sequence is existential; uniqueness not claimed beyond the stated extremality properties. Not compiled.
