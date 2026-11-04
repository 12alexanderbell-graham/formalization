import Checked.Cosmography.B1FitWitness

/-!
# C27 at fit level: no cubic in the RL19 reading box matches any flat ΛCDM over the quasar range

Risaliti & Lusso 2019 (arXiv:1811.02590v1, the only version) Fig. 3: the filled contours (quasars +
JLA supernovae, cubic log-polynomial fit) are centred at `(a₂, a₃) ≈ (3.46 ± 0.03, 1.63 ± 0.06)`
(two readings: run 0428Z `(3.45, 1.6)`, `runs/2026-10-31T0428Z/rl19_numbers.md`; blind second
reading run 2026-11-04T0228Z from an independent render, pixel centroids, `(3.458, 1.629)`).
The box below, `a₂ ∈ [3.43, 3.49]`, `a₃ ∈ [1.57, 1.69]`, contains both readings with their stated
uncertainty.

**Statement.** For every `Ω ∈ [0, 1]` and every scale factor obeying `H = H₀√(Ω(1+z)³ + 1 − Ω)` back
to the farthest of the sources at `1 + z = √2, 2√2, 4√2`, no cubic log-polynomial with `(a₂, a₃)` in
the box (any normalisation `H > 0`, positive at the three redshifts) has a distance modulus within
0.05 mag of the exact one, up to a common offset, at all three redshifts. With
`Checked.Cosmography.B1Fit.fit_direction` this is the certified form of C27: the RL19 centre lies on
the opposite side of the line through the ΛCDM-implied point from every cubic that matches exact
ΛCDM over the quasar range, so the truncation of the cubic does not account for it.
It is a statement about the centre of the published contours, not about the data or their
covariance (not printed).

FROZEN (annex 40.1) in run 2026-11-04T0228Z before proof work (bf5d489).
PROMOTED from `Work/Cosmography/B1FitRL19.lean` in the same run (statement and theorem docstring
byte-identical). Audit: `runs/2026-11-04T0228Z/audit_b1fit.md` (section C27); blind restatement
closed in `Work/Cosmography/B1FitRL19Audit.lean`; non-vacuity: `hyps_satisfiable` below.
-/

namespace Checked.Cosmography.B1FitRL19

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

/-! ## Proof tools (not part of the frozen statement) -/

/-- On the box, the direction functional is negative for every `Ω ∈ [0, 1]`. -/
lemma box_neg (Ω a₂ a₃ l L : ℝ) (hΩ0 : 0 ≤ Ω) (hΩ1 : Ω ≤ 1)
    (ha₂ : 343 / 100 ≤ a₂ ∧ a₂ ≤ 349 / 100) (ha₃ : 157 / 100 ≤ a₃ ∧ a₃ ≤ 169 / 100)
    (hl1 : 2302 / 1000 ≤ l) (hl2 : l ≤ 23027 / 10000)
    (hL1 : 30101 / 100000 ≤ L) (hL2 : L ≤ 30105 / 100000) :
    20 / 3 * L * (a₃ - l ^ 2 * (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6))
      - (a₂ - l * (3 / 2 - 3 / 4 * Ω)) < 0 := by
  set A3 := 9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6 with hA3
  set A2 := 3 / 2 - 3 / 4 * Ω with hA2
  have hA3p : 5 / 18 ≤ A3 := by nlinarith [sq_nonneg (Ω - 8 / 9)]
  have hA2p : 0 ≤ A2 := by linarith
  have hl0 : 0 ≤ l := by linarith
  have hL0 : 0 ≤ L := by linarith
  have e1 : L * a₃ ≤ 30105 / 100000 * (169 / 100) :=
    mul_le_mul hL2 ha₃.2 (by linarith) (by norm_num)
  have hll : (2302 / 1000 : ℝ) ^ 2 ≤ l ^ 2 := pow_le_pow_left₀ (by norm_num) hl1 2
  have e2a : 30101 / 100000 * (2302 / 1000) ^ 2 ≤ L * l ^ 2 :=
    mul_le_mul hL1 hll (by positivity) hL0
  have e2 : 30101 / 100000 * (2302 / 1000) ^ 2 * A3 ≤ L * l ^ 2 * A3 :=
    mul_le_mul_of_nonneg_right e2a (by linarith)
  have e3 : l * A2 ≤ 23027 / 10000 * A2 := mul_le_mul_of_nonneg_right hl2 hA2p
  have hq : 30105 / 100000 * (169 / 100) * (20 / 3) - 343 / 100 + 23027 / 10000 * A2
      - 20 / 3 * (30101 / 100000 * (2302 / 1000) ^ 2 * A3) < 0 := by
    rw [hA2, hA3]; nlinarith [sq_nonneg (Ω - 49 / 60)]
  have e : 20 / 3 * L * (a₃ - l ^ 2 * A3) - (a₂ - l * A2)
      = 20 / 3 * (L * a₃) - 20 / 3 * (L * l ^ 2 * A3) - a₂ + l * A2 := by ring
  rw [e]; nlinarith

/-- **C27 (fit level).** For every `Ω ∈ [0, 1]`, no cubic log-polynomial with `a₂ ∈ [3.43, 3.49]`,
`a₃ ∈ [1.57, 1.69]` (the RL19 Fig. 3 contour centre with its reading uncertainty), normalisation
`H > 0`, positive at `1 + z = √2, 2√2, 4√2`, agrees with the exact distance modulus of a model
obeying `H = H₀√(Ω(1+z)³ + 1 − Ω)` within 0.05 mag up to a common offset at all three redshifts. -/
theorem rl19_box_unmatched (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₁ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₁ : t₃ ≤ t₁) (h₁₀ : t₁ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₁ : redshift a t₀ t₁ = √2 - 1) (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1)
    (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ H c : ℝ) (ha₂l : 343 / 100 ≤ a₂) (ha₂u : a₂ ≤ 349 / 100)
    (ha₃l : 157 / 100 ≤ a₃) (ha₃u : a₃ ≤ 169 / 100) (hHp : 0 < H)
    (hp₁ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁))
    (hp₃ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (hp₅ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) :
    ¬ (|5 * Real.logb 10 (lumDistFlat a t₀ t₁ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)) - c|
          ≤ 1 / 20 ∧
        |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c|
          ≤ 1 / 20 ∧
        |5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) - c|
          ≤ 1 / 20) := by
  rintro ⟨hm₁, hm₃, hm₅⟩
  have hf := Checked.Cosmography.B1Fit.fit_direction Ω hΩ₀ hΩ₁ a t₅ t₃ t₁ t₀ h₅₃ h₃₁ h₁₀ hpos hdiff
    hH₀ hH hz₁ hz₃ hz₅ a₂ a₃ H c hHp hp₁ hp₃ hp₅ hm₁ hm₃ hm₅
  obtain ⟨hL1, hL2⟩ := Checked.Cosmography.B1FitWitness.t_bounds
  have hl1 := Checked.Cosmography.B1Fit.log_ten_ge
  have hl2 := Checked.Cosmography.B1FitWitness.log_ten_le
  have hneg := box_neg Ω a₂ a₃ (Real.log 10) (Real.logb 10 2) hΩ₀ hΩ₁ ⟨ha₂l, ha₂u⟩ ⟨ha₃l, ha₃u⟩
    (by norm_num at hl1 ⊢; linarith) (by norm_num at hl2 ⊢; linarith) hL1 hL2
  unfold lusA2 lusA3 at hf
  nlinarith

/-! ## Non-vacuity -/

/-- Every hypothesis of `rl19_box_unmatched` holds at once: the exact solution with `Ω = 1/5`
(`Checked.Cosmography.B1FitWitness.exists_model`) and the cubic `a₂ = 173/50`, `a₃ = 163/100`,
`H = 1` (the box centre), which is positive at the three redshifts. -/
theorem hyps_satisfiable : ∃ (Ω : ℝ) (a : ℝ → ℝ) (t₅ t₃ t₁ t₀ a₂ a₃ H : ℝ),
    0 ≤ Ω ∧ Ω ≤ 1 ∧ t₅ ≤ t₃ ∧ t₃ ≤ t₁ ∧ t₁ ≤ t₀ ∧
    (∀ s ∈ Set.Icc t₅ t₀, 0 < a s) ∧ (∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s) ∧
    0 < hubble a t₀ ∧
    (∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)) ∧
    redshift a t₀ t₁ = √2 - 1 ∧ redshift a t₀ t₃ = 2 * √2 - 1 ∧
    redshift a t₀ t₅ = 4 * √2 - 1 ∧
    (343 / 100 ≤ a₂ ∧ a₂ ≤ 349 / 100) ∧ (157 / 100 ≤ a₃ ∧ a₃ ≤ 169 / 100) ∧ 0 < H ∧
    0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁) ∧ 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃) ∧
    0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₅) := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, hz₁, hz₃, hz₅⟩ :=
    Checked.Cosmography.B1FitWitness.exists_model
  have hq2 : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
  have hl0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hℓ0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpoly : ∀ u : ℝ, 0 < u → ∀ z : ℝ, Real.log (1 + z) = u →
      0 < logPolyDL3 (173 / 50) (163 / 100) 1 z := by
    intro u hu z hz
    rw [Checked.Cosmography.B1Fit.lp_eq _ _ 1 _ _ one_ne_zero hz]; positivity
  refine ⟨1 / 5, a, t₅, t₃, t₁, t₀, 173 / 50, 163 / 100, 1, by norm_num, by norm_num, h53, h31,
    h10, hpos, hdiff, hH₀, hH, hz₁, hz₃, hz₅, by norm_num, by norm_num, one_pos, ?_, ?_, ?_⟩
  · rw [hz₁]; refine hpoly (Real.log 2 / 2) (by positivity) _ ?_
    rw [show (1:ℝ) + (√2 - 1) = √2 by ring, Real.log_sqrt (by norm_num)]
  · rw [hz₃]; refine hpoly (Real.log 2 + Real.log 2 / 2) (by positivity) _ ?_
    rw [show (1:ℝ) + (2 * √2 - 1) = 2 * √2 by ring, Real.log_mul (by norm_num) hq2.ne',
      Real.log_sqrt (by norm_num)]
  · rw [hz₅]; refine hpoly (2 * Real.log 2 + Real.log 2 / 2) (by positivity) _ ?_
    rw [show (1:ℝ) + (4 * √2 - 1) = 4 * √2 by ring, Real.log_mul (by norm_num) hq2.ne',
      Real.log_sqrt (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring

end Checked.Cosmography.B1FitRL19
