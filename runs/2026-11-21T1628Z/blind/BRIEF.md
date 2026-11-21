# Blind restatement brief (run 2026-11-21T1628Z)

You are formalizing one claim in Lean 4 + Mathlib. Do NOT read anything in the repository /home/claude/formalization other than what this brief names (no `Checked/`, `Work/`, `runs/` other than your own output folder, no `*.md` files, no git history). Write your output only to `runs/2026-11-21T1628Z/blind/`. Do not compile; write carefully against current Mathlib names.

You may (and should) use these existing program definitions; your file should `import Checked.Cosmography.B1Truncation`, which provides them (the namespaces to `open` are `Checked.Cosmography`, `Checked.Cosmography.BambaY`, `Checked.Cosmography.B1`):

```lean
noncomputable def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t          -- Hubble rate
noncomputable def redshift (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := a t₀ / a t - 1       -- redshift of emission time t seen at t₀
noncomputable def comoving (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := ∫ s in t..t₀, 1 / a s -- comoving distance (c = 1)
noncomputable def lumDistFlat (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=                     -- flat luminosity distance
  a t₀ * (1 + redshift a t₀ t) * comoving a t₀ t
noncomputable def logPolyDL3 (a₂ a₃ H₀ z : ℝ) : ℝ :=                            -- cubic log-polynomial fit
  Real.log 10 / H₀ *
    (Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3)
```

The claim (cosmology; the cubic log-polynomial Hubble-diagram fit of Risaliti & Lusso 2019, `D_L = ln(10) (c/H) (x + a₂ x² + a₃ x³)`, `x = log₁₀(1 + z)`):

> Take any exactly flat ΛCDM universe with matter density Ω_M between 0 and 1 (inclusive): a scale factor whose Hubble rate obeys H(z) = H₀ √(Ω_M (1+z)³ + 1 − Ω_M) over the relevant epoch, observed today. Consider three sources at 1 + z = √2, 2√2 and 4√2. Suppose a cubic log-polynomial (any second coefficient a₂, any third coefficient a₃, any normalisation H > 0), positive at those three redshifts, reproduces that universe's distance modulus (5 log₁₀ of the luminosity distance) within 0.05 mag, up to one common magnitude offset, at all three redshifts.
> Claim: then a₃ > 13/5 (= 2.6), whatever a₂.

Write `runs/2026-11-21T1628Z/blind/B1A3BoundBlind.lean` (the import above, any auxiliary definitions you need, one theorem `blind_a3_bound` stating the claim as faithfully as you can, `:= by sorry`) and a short `notes.md` listing every interpretive choice (where the expansion law is assumed to hold, how the sources are placed in time, how "within 0.05 mag up to a common offset" is stated, junk values of `Real.logb` and how you avoided them, strict or non-strict inequalities). If your Write tool is refused, put both file contents in your final message. Always report both file contents in your final message.
