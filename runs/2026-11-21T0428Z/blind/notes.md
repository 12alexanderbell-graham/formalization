# Interpretive choices (blind)

- Solution class: `w φ : ℝ → ℝ` with `w 0 = 0`; `HasDerivWithinAt w (φ s) (Ici 0) s` for all `s ≥ 0` (one-sided at 0); `φ` continuous within `Ici 0` at 0; `HasDerivAt φ (-(2/s) * φ s - exp (w s)) s` for all `s > 0`. No condition on `φ 0` is imposed.
- `λ s = s^2 * exp (w s)`, defined as `gelfandLam w`.
- Turning points: not characterised via derivative of λ. They are given as a `StrictMono` sequence `ζ : ℕ → ℝ` tending to `atTop`, with `StrictMonoOn` / `StrictAntiOn` of λ on the closed intervals `Icc` as stated (increasing on `[0, ζ 0]`, decreasing on `[ζ(2k), ζ(2k+1)]`, increasing on `[ζ(2k+1), ζ(2k+2)]`). Strict alternation makes the ζ_k exactly the local extrema.
- Limit: `Tendsto (gelfandLam w) atTop (nhds 2)`.
- Decimals: real literals (`4.071496844 : ℝ`, via OfScientific) in closed intervals `Icc lo hi`; ζ₀..ζ₄ are `ζ 0 .. ζ 4`.
- Sequence indexed from 0; the theorem quantifies over all such w, with `∃ ζ` in the conclusion.
