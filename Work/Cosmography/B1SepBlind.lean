import Checked.Cosmography.B1Truncation

/-!
# B1 separation, blind restatement

Blind restatement (written without seeing the program's statement) of the claim:

> Suppose the universe is exactly flat ΛCDM with matter density `Ω ∈ [0.2, 0.4]`, i.e. the
> scale factor `a` is positive and differentiable on the time interval from the emission of a
> source at redshift 7 up to now (`t₀`), `H₀ > 0`, and `H(s) = H₀ √(Ω(1+z(s))³ + 1 − Ω)` at every
> time `s` in that interval. Consider sources at redshift 3 and redshift 7. Take any cubic
> log-polynomial — any coefficients `a₂, a₃`, any positive normalisation `H`, giving positive
> distances at both redshifts — whose distance modulus agrees with the exact distance modulus up
> to one common additive magnitude offset to within 0.05 mag at both redshifts. Then the point
> `(a₂, a₃)` lies at Euclidean distance more than `5/4` from `(lusA2 Ω, lusA3 Ω)`.

## Reading and modelling choices

* **Conventions** are the program's (`Checked.Cosmography`): `c = 1`, `hubble a t = ȧ/a`,
  `redshift a t₀ t = a(t₀)/a(t) − 1`, exact luminosity distance `lumDistFlat a t₀ t`, the cubic
  `logPolyDL3 a₂ a₃ H z`, and the ΛCDM point `(lusA2 Ω, lusA3 Ω)`.
* **Ω range**: closed interval `1/5 ≤ Ω ≤ 2/5` ("between 0.2 and 0.4", endpoints included —
  the stronger reading).
* **Times**: three times `t₇ ≤ t₃ ≤ t₀` (emission at `z = 7`, emission at `z = 3`, now). The
  ΛCDM hypotheses are imposed on the whole closed interval `Set.Icc t₇ t₀`, which contains `t₃`:
  `a s > 0` and `a` differentiable at every `s` there, `H₀ := hubble a t₀ > 0`, and the Friedmann
  law `hubble a s = H₀ √(Ω (1 + redshift a t₀ s)³ + 1 − Ω)` at every `s` there.
  The ordering `t₇ ≤ t₃ ≤ t₀` is assumed explicitly (it is what "sources at redshift 3 and 7
  observed now, inside the interval" means). Redshifts are pinned by
  `redshift a t₀ t₃ = 3` and `redshift a t₀ t₇ = 7`.
* **Cubic**: universally quantified `a₂ a₃ H : ℝ` with `0 < H`, and positivity of the cubic
  distances `logPolyDL3 a₂ a₃ H 3 > 0` and `logPolyDL3 a₂ a₃ H 7 > 0` (so the logarithms are
  meaningful). The cubic is evaluated at the literal redshifts `3` and `7` (equal to
  `redshift a t₀ t₃`, `redshift a t₀ t₇` by hypothesis). Its normalisation `H` is independent of
  the model's `H₀`.
* **Distance-modulus residual** at redshift `z` (source time `t_z`):
  `Δ_z := 5 log₁₀ (lumDistFlat a t₀ t_z / logPolyDL3 a₂ a₃ H z)` — the exact distance modulus
  minus the cubic's distance modulus (distance moduli differ by `5 log₁₀` of the distance ratio).
* **"Agrees up to one common additive offset to within 0.05 mag at both redshifts"**: there
  exists a single real offset `δ` (in magnitudes) with `|Δ₃ − δ| ≤ 0.05` and `|Δ₇ − δ| ≤ 0.05`.
  The offset is existentially quantified inside the hypothesis (so the hypothesis is the weak
  one, and the theorem the strong one); the tolerance is non-strict `≤ 1/20` (again the weaker
  hypothesis). This is equivalent to `|Δ₇ − Δ₃| ≤ 0.1`. Note that a common offset is already
  redundant with the free normalisation `H` (rescaling `H` shifts both `Δ`'s equally), so the
  hypothesis is really a constraint on the *shape* `(a₂, a₃)` only.
* **Conclusion**: strict `5/4 < √((a₂ − lusA2 Ω)² + (a₃ − lusA3 Ω)²)` (Euclidean distance in the
  `(a₂, a₃)` plane, written with `Real.sqrt`).
-/

namespace Work.Cosmography.B1SepBlind

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

/-- **B1 separation (blind restatement).** In every exact flat ΛCDM model with `Ω ∈ [0.2, 0.4]`
holding on the time interval from a `z = 7` emission to now, every cubic log-polynomial
(positive normalisation, positive distances at `z = 3, 7`) whose distance modulus matches the
exact one at `z = 3` and `z = 7` up to a common offset within 0.05 mag has `(a₂, a₃)` farther
than `5/4` from the ΛCDM-implied point `(lusA2 Ω, lusA3 Ω)`. -/
theorem blind_separation (Ω : ℝ) (hΩ₁ : 1 / 5 ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (a : ℝ → ℝ) (t₇ t₃ t₀ : ℝ) (h₇₃ : t₇ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₇ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₇ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₇ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 3) (hz₇ : redshift a t₀ t₇ = 7)
    (a₂ a₃ H : ℝ) (hHpos : 0 < H)
    (hP₃ : 0 < logPolyDL3 a₂ a₃ H 3) (hP₇ : 0 < logPolyDL3 a₂ a₃ H 7)
    (hfit : ∃ δ : ℝ,
      |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H 3) - δ| ≤ 1 / 20 ∧
      |5 * Real.logb 10 (lumDistFlat a t₀ t₇ / logPolyDL3 a₂ a₃ H 7) - δ| ≤ 1 / 20) :
    5 / 4 < √((a₂ - lusA2 Ω) ^ 2 + (a₃ - lusA3 Ω) ^ 2) := by
  sorry

end Work.Cosmography.B1SepBlind
