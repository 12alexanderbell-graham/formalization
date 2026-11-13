import Checked.Trust.NonVacuity
import Checked.Cosmography.FREta

/-!
# Hypothesis necessity: the non-degeneracy condition of the printed η₂₀, η₃₀ refutations
(run 2026-11-13T0828Z)

`Checked.Cosmography.FREta.printedEta20_false_at` and `printedEta30_false_at` refute the review's
first-order coefficients (11.42), (11.43) at every Ω ∈ (0, 1) where the printed denominator is nonzero
and `(54Ω² − 29Ω − 2)(27Ω² + 24Ω − 32) ≠ 0` (hypothesis 4). That condition is needed: at
Ω₀ = 4(√7 − 1)/9 ≈ 0.731, a root of 27Ω² + 24Ω − 32, the printed and the correct coefficients agree
(η₂₀: both are 0; η₃₀: their difference has the factor 27Ω² + 24Ω − 32), so the printed first-order
statement holds there, while 0 < Ω₀ < 1 and the printed denominator is nonzero.

The nonzero printed denominator (hypothesis 3) is redundant in both: where it vanishes, Lean's x/0 = 0
makes the printed coefficient 0, and the correct coefficient vanishes only where hypothesis 4 fails
(η₂₀) or at a root of 81Ω² − 60Ω − 16, which shares no positive root with the denominator (η₃₀).
-/

namespace Checked.Trust.NecessityEta
open Checked.Cosmography.FREta Checked.Cosmography.FRCosmo

/-- Ω₀ = 4(√7 − 1)/9: facts used by both witnesses. -/
theorem omega0_facts :
    0 < 4 * (Real.sqrt 7 - 1) / 9 ∧ 4 * (Real.sqrt 7 - 1) / 9 < 1 ∧
      27 * (4 * (Real.sqrt 7 - 1) / 9) ^ 2 + 24 * (4 * (Real.sqrt 7 - 1) / 9) - 32 = 0 ∧
      printedDen (4 * (Real.sqrt 7 - 1) / 9) ≠ 0 ∧
      27 * (4 * (Real.sqrt 7 - 1) / 9) ^ 3 + 276 * (4 * (Real.sqrt 7 - 1) / 9) ^ 2
        - 4 * (4 * (Real.sqrt 7 - 1) / 9) - 8 ≠ 0 := by
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hlo : 2.6 < Real.sqrt 7 := by
    rw [show (2.6 : ℝ) = Real.sqrt (2.6 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hhi : Real.sqrt 7 < 2.7 := by
    rw [show (2.7 : ℝ) = Real.sqrt (2.7 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  set Ω := 4 * (Real.sqrt 7 - 1) / 9 with hΩ
  have l1 : 0.71 < Ω := by rw [hΩ]; linarith
  have l2 : Ω < 0.76 := by rw [hΩ]; linarith
  refine ⟨by linarith, by linarith, ?_, ?_, ?_⟩
  · rw [hΩ]; ring_nf; rw [h7]; ring
  · rw [printedDen_eq]
    apply mul_ne_zero (by linarith)
    nlinarith [mul_pos (show 0 < Ω - 0.71 by linarith) (show 0 < 0.76 - Ω by linarith),
      pow_pos (show 0 < Ω by linarith) 2, pow_pos (show 0 < Ω by linarith) 3]
  · nlinarith [mul_pos (show 0 < Ω - 0.71 by linarith) (show 0 < 0.76 - Ω by linarith),
      pow_pos (show 0 < Ω by linarith) 2, pow_pos (show 0 < Ω by linarith) 3]

/-- At a root of 27Ω² + 24Ω − 32 both coefficients of η₂₀ vanish. -/
theorem agree20 (Ω : ℝ) (hz : 27 * Ω ^ 2 + 24 * Ω - 32 = 0) :
    correct20 Ω = 0 ∧ printed20 Ω = 0 := by
  constructor
  · unfold correct20
    rw [show -2 * (27 * Ω ^ 2 + 24 * Ω - 32) = 0 by rw [hz]; ring, zero_div]
  · unfold printed20
    rw [show (64 - 6 * Ω * (9 * Ω + 8)) = -2 * (27 * Ω ^ 2 + 24 * Ω - 32) by ring, hz]
    simp

/-- At a root of 27Ω² + 24Ω − 32 in (0, 1) where the printed denominator's cubic factor is nonzero, the
printed and the correct coefficient of η₃₀ agree. -/
theorem agree30 (Ω : ℝ) (h0 : 0 < Ω) (h1 : Ω < 1) (hz : 27 * Ω ^ 2 + 24 * Ω - 32 = 0)
    (hc : 27 * Ω ^ 3 + 276 * Ω ^ 2 - 4 * Ω - 8 ≠ 0) : correct30 Ω = printed30 Ω := by
  have hq : (27 * Ω ^ 2 + 60 * Ω + 112) ≠ 0 := by positivity
  have h2 : Ω - 2 ≠ 0 := by intro h; linarith
  have hΩ0 := h0.ne'
  have key : correct30 Ω - printed30 Ω = -4 * (3 * Ω + 8) * (27 * Ω ^ 2 + 24 * Ω - 32)
      * (54 * Ω ^ 2 - 29 * Ω - 2) / (243 * Ω ^ 2 * (Ω - 2) * (27 * Ω ^ 2 + 60 * Ω + 112)
        * (27 * Ω ^ 3 + 276 * Ω ^ 2 - 4 * Ω - 8)) := by
    unfold correct30 printed30; rw [printedDen_eq, div_mul_div_comm,
      div_sub_div _ _ (by simp [hΩ0, h2, hq]) (by simp [hΩ0, h2, hc]),
      div_eq_div_iff (by simp [hΩ0, h2, hq, hc]) (by simp [hΩ0, h2, hq, hc])]
    ring
  rw [hz, mul_zero, zero_mul, zero_div, sub_eq_zero] at key
  exact key

/-- `(54Ω² − 29Ω − 2)(27Ω² + 24Ω − 32) ≠ 0` (hypothesis 4) is needed in `printedEta20_false_at`: at
Ω₀ = 4(√7 − 1)/9 the printed and the correct coefficient of η₂₀ are both 0, so the printed
first-order statement holds (`eta20_hasDerivAt`). -/
theorem printedEta20_false_at_h4 :
    necessity% Checked.Cosmography.FREta.printedEta20_false_at 4 := by
  obtain ⟨h0, h1, hz, hd, -⟩ := omega0_facts
  refine ⟨4 * (Real.sqrt 7 - 1) / 9, h0, h1, hd, ?_⟩
  have he := (eta20_hasDerivAt h0 h1).2
  obtain ⟨hc, hp⟩ := agree20 _ hz
  rw [hp]; rw [hc] at he; exact he

/-- `(54Ω² − 29Ω − 2)(27Ω² + 24Ω − 32) ≠ 0` (hypothesis 4) is needed in `printedEta30_false_at`: at
Ω₀ = 4(√7 − 1)/9 the printed and the correct coefficient of η₃₀ agree (their difference has the factor
27Ω² + 24Ω − 32), so the printed first-order statement holds (`eta30_hasDerivAt`). -/
theorem printedEta30_false_at_h4 :
    necessity% Checked.Cosmography.FREta.printedEta30_false_at 4 := by
  obtain ⟨h0, h1, hz, hd, hc⟩ := omega0_facts
  refine ⟨4 * (Real.sqrt 7 - 1) / 9, h0, h1, hd, ?_⟩
  rw [← agree30 _ h0 h1 hz hc]
  exact (eta30_hasDerivAt h0 h1).2

/-- `printedDen Ω ≠ 0` (hypothesis 3) is redundant in `printedEta20_false_at`: where the printed
denominator vanishes, Lean's x/0 = 0 makes the printed coefficient 0, and the correct coefficient is 0 only
at a root of 27Ω² + 24Ω − 32, which hypothesis 4 excludes. -/
theorem printedEta20_false_at_r3 :
    dropped% Checked.Cosmography.FREta.printedEta20_false_at 3 := by
  intro Ω h0 h1 hne
  by_cases hd : printedDen Ω = 0
  · intro h
    have hp : printed20 Ω = 0 := by unfold printed20; rw [hd]; simp
    rw [hp] at h
    have he := (eta20_hasDerivAt h0 h1).2.unique h
    have hq : (27 * Ω ^ 2 + 60 * Ω + 112) ≠ 0 := by positivity
    have h2 : Ω - 2 ≠ 0 := by intro h; linarith
    have hden : 27 * Ω * (Ω - 2) * (27 * Ω ^ 2 + 60 * Ω + 112) ≠ 0 := by
      have := h0.ne'; simp [this, h2, hq]
    unfold correct20 at he
    rw [div_eq_zero_iff] at he
    rcases he with he | he
    · apply hne
      rw [show 27 * Ω ^ 2 + 24 * Ω - 32 = 0 by linarith, mul_zero]
    · exact hden he
  · exact Checked.Cosmography.FREta.printedEta20_false_at h0 h1 hd hne

/-- `printedDen Ω ≠ 0` (hypothesis 3) is redundant in `printedEta30_false_at`: where the printed
denominator vanishes (in (0, 1): a root of 27Ω³ + 276Ω² − 4Ω − 8), the printed coefficient is 0 (Lean's
x/0 = 0), and the correct one is 0 only at a root of 81Ω² − 60Ω − 16; the two polynomials have no common
positive root (the remainder of the cubic by the quadratic is 5956Ω/27 + 4088/81 > 0). -/
theorem printedEta30_false_at_r3 :
    dropped% Checked.Cosmography.FREta.printedEta30_false_at 3 := by
  intro Ω h0 h1 hne
  by_cases hd : printedDen Ω = 0
  · intro h
    have hp : printed30 Ω = 0 := by unfold printed30; rw [hd]; simp
    rw [hp] at h
    have he := (eta30_hasDerivAt h0 h1).2.unique h
    have hq : (27 * Ω ^ 2 + 60 * Ω + 112) ≠ 0 := by positivity
    have h2 : Ω - 2 ≠ 0 := by intro h; linarith
    have hden : 243 * Ω ^ 2 * (Ω - 2) * (27 * Ω ^ 2 + 60 * Ω + 112) ≠ 0 := by
      have := h0.ne'; simp [this, h2, hq]
    have hcub : 27 * Ω ^ 3 + 276 * Ω ^ 2 - 4 * Ω - 8 = 0 := by
      rw [printedDen_eq] at hd
      rcases mul_eq_zero.1 hd with h | h
      · exact absurd h h2
      · exact h
    unfold correct30 at he
    rw [div_eq_zero_iff] at he
    rcases he with he | he
    · have hquad : 81 * Ω ^ 2 - 60 * Ω - 16 = 0 := by linarith
      have : 5956 * Ω / 27 + 4088 / 81 = 0 := by
        linear_combination hcub - (Ω / 3 + 296 / 81) * hquad
      linarith
    · exact hden he
  · exact Checked.Cosmography.FREta.printedEta30_false_at h0 h1 hd hne

/-! ## The range 0 < Ω < 1 (hypotheses 1, 2) is redundant -/

/-- `correct20` is the first-order coefficient of η₂₀ for every Ω ≠ 0, 2 (the proof of
`eta20_hasDerivAt` uses only these). -/
theorem eta20_hasDerivAt' {Ω : ℝ} (hΩ : Ω ≠ 0) (h2 : Ω - 2 ≠ 0) :
    HasDerivAt (eta20 Ω) (correct20 Ω) 0 := by
  have hq : (27 * Ω ^ 2 + 60 * Ω + 112) ≠ 0 := by nlinarith [sq_nonneg (Ω + 10 / 9)]
  have hD0 : Dfam Ω 0 ≠ 0 := by
    rw [Dfam_zero]; simp [hΩ, h2, hq]
  rw [eta20_eq]
  have hK : ContinuousAt (fun ε => N2e Ω ε / (36 * Dfam Ω ε)) 0 :=
    (N2e_cont Ω).continuousAt.div ((continuous_const.mul (Dfam_cont Ω)).continuousAt)
      (mul_ne_zero (by norm_num) hD0)
  convert hasDerivAt_mul_cont hK using 1
  show correct20 Ω = N2e Ω 0 / (36 * Dfam Ω 0)
  unfold correct20
  rw [div_eq_div_iff (by simp [hΩ, h2, hq]) (mul_ne_zero (by norm_num) hD0), Dfam_zero]
  unfold N2e
  ring

/-- `correct30` is the first-order coefficient of η₃₀ for every Ω ≠ 0, 2. -/
theorem eta30_hasDerivAt' {Ω : ℝ} (hΩ : Ω ≠ 0) (h2 : Ω - 2 ≠ 0) :
    HasDerivAt (eta30 Ω) (correct30 Ω) 0 := by
  have hq : (27 * Ω ^ 2 + 60 * Ω + 112) ≠ 0 := by nlinarith [sq_nonneg (Ω + 10 / 9)]
  have hD0 : Dfam Ω 0 ≠ 0 := by
    rw [Dfam_zero]; simp [hΩ, h2, hq]
  have hJ0 : Jfam Ω 0 ≠ 0 := by
    unfold Jfam qL jL; intro h; apply hΩ; linarith
  rw [eta30_eq]
  have hK : ContinuousAt (fun ε => N3e Ω ε / (216 * Jfam Ω ε * Dfam Ω ε)) 0 :=
    (N3e_cont Ω).continuousAt.div
      (((continuous_const.mul (Jfam_cont Ω)).mul (Dfam_cont Ω)).continuousAt)
      (mul_ne_zero (mul_ne_zero (by norm_num) hJ0) hD0)
  convert hasDerivAt_mul_cont hK using 1
  show correct30 Ω = N3e Ω 0 / (216 * Jfam Ω 0 * Dfam Ω 0)
  unfold correct30
  rw [div_eq_div_iff (by simp [hΩ, h2, hq]) (mul_ne_zero (mul_ne_zero (by norm_num) hJ0) hD0),
    Dfam_zero]
  unfold N3e Jfam qL jL
  ring

/-- Where both coefficients are defined (Ω ≠ 0, 2, printed denominator nonzero), the printed and the
correct coefficient of η₂₀ agree only where `(54Ω² − 29Ω − 2)(27Ω² + 24Ω − 32) = 0`. -/
theorem agree20_imp {Ω : ℝ} (hΩ : Ω ≠ 0) (h2 : Ω - 2 ≠ 0) (hd : printedDen Ω ≠ 0)
    (he : correct20 Ω = printed20 Ω) :
    (54 * Ω ^ 2 - 29 * Ω - 2) * (27 * Ω ^ 2 + 24 * Ω - 32) = 0 := by
  have hq : (27 * Ω ^ 2 + 60 * Ω + 112) ≠ 0 := by nlinarith [sq_nonneg (Ω + 10 / 9)]
  rw [printedDen_eq] at hd
  have hc : 27 * Ω ^ 3 + 276 * Ω ^ 2 - 4 * Ω - 8 ≠ 0 := right_ne_zero_of_mul hd
  have key : correct20 Ω - printed20 Ω = -8 * (27 * Ω ^ 2 + 24 * Ω - 32) * (54 * Ω ^ 2 - 29 * Ω - 2)
      / (27 * Ω * (Ω - 2) * (27 * Ω ^ 2 + 60 * Ω + 112) * (27 * Ω ^ 3 + 276 * Ω ^ 2 - 4 * Ω - 8)) := by
    unfold correct20 printed20; rw [printedDen_eq, div_mul_div_comm,
      div_sub_div _ _ (by simp [hΩ, h2, hq]) (by simp [h2, hc]),
      div_eq_div_iff (by simp [hΩ, h2, hq, hc]) (by simp [hΩ, h2, hq, hc])]
    ring
  rw [he, sub_self] at key
  rcases div_eq_zero_iff.1 key.symm with h | h
  · linear_combination (-1 / 8) * h
  · exfalso; revert h; simp [hΩ, h2, hq, hc]

/-- Same for η₃₀, with the extra factor 3Ω + 8 of the difference. -/
theorem agree30_imp {Ω : ℝ} (hΩ : Ω ≠ 0) (h2 : Ω - 2 ≠ 0) (hd : printedDen Ω ≠ 0)
    (he : correct30 Ω = printed30 Ω) :
    (3 * Ω + 8) * ((54 * Ω ^ 2 - 29 * Ω - 2) * (27 * Ω ^ 2 + 24 * Ω - 32)) = 0 := by
  have hq : (27 * Ω ^ 2 + 60 * Ω + 112) ≠ 0 := by nlinarith [sq_nonneg (Ω + 10 / 9)]
  rw [printedDen_eq] at hd
  have hc : 27 * Ω ^ 3 + 276 * Ω ^ 2 - 4 * Ω - 8 ≠ 0 := right_ne_zero_of_mul hd
  have key : correct30 Ω - printed30 Ω = -4 * (3 * Ω + 8) * (27 * Ω ^ 2 + 24 * Ω - 32)
      * (54 * Ω ^ 2 - 29 * Ω - 2) / (243 * Ω ^ 2 * (Ω - 2) * (27 * Ω ^ 2 + 60 * Ω + 112)
        * (27 * Ω ^ 3 + 276 * Ω ^ 2 - 4 * Ω - 8)) := by
    unfold correct30 printed30; rw [printedDen_eq, div_mul_div_comm,
      div_sub_div _ _ (by simp [hΩ, h2, hq]) (by simp [hΩ, h2, hc]),
      div_eq_div_iff (by simp [hΩ, h2, hq, hc]) (by simp [hΩ, h2, hq, hc])]
    ring
  rw [he, sub_self] at key
  rcases div_eq_zero_iff.1 key.symm with h | h
  · linear_combination (-1 / 4) * h
  · exfalso; revert h; simp [hΩ, h2, hq, hc]

/-- Conversely, where 3Ω + 8 = 0 (Ω = −8/3) the two coefficients of η₃₀ agree. -/
theorem agree30_m83 : correct30 (-8 / 3) = printed30 (-8 / 3) := by
  unfold correct30 printed30 printedDen; norm_num

/-- `0 < Ω` (hypothesis 1) is needed in `printedEta30_false_at`: at Ω = −8/3 the printed and the correct
coefficient of η₃₀ agree (their difference has the factor 3Ω + 8), Ω < 1, the printed denominator and
`(54Ω² − 29Ω − 2)(27Ω² + 24Ω − 32)` are nonzero, and η₃₀ has that first-order coefficient. -/
theorem printedEta30_false_at_h1 :
    necessity% Checked.Cosmography.FREta.printedEta30_false_at 1 := by
  refine ⟨-8 / 3, by norm_num, by unfold printedDen; norm_num, by norm_num, ?_⟩
  rw [← agree30_m83]
  exact eta30_hasDerivAt' (by norm_num) (by norm_num)

/-- `Ω < 1` (hypothesis 2) is redundant in `printedEta30_false_at`: for Ω ≥ 1 with a nonzero printed
denominator (so Ω ≠ 2) the first-order coefficient is `correct30`, and it equals the printed one only
where `(3Ω + 8)(54Ω² − 29Ω − 2)(27Ω² + 24Ω − 32) = 0`, i.e. (as 3Ω + 8 > 0) where hypothesis 4 fails. -/
theorem printedEta30_false_at_r2 :
    dropped% Checked.Cosmography.FREta.printedEta30_false_at 2 := by
  intro Ω h0 hd hne h
  have h2 : Ω - 2 ≠ 0 := by
    intro e; apply hd; rw [printedDen_eq, e, zero_mul]
  have he := (eta30_hasDerivAt' h0.ne' h2).unique h
  have := agree30_imp h0.ne' h2 hd he
  exact hne ((mul_eq_zero.1 this).resolve_left (by linarith))

/-- `Ω < 1` (hypothesis 2) is redundant in `printedEta20_false_at`: for Ω ≥ 1 (Ω ≠ 2 by the printed
denominator) the coefficients agree only where hypothesis 4 fails. -/
theorem printedEta20_false_at_r2 :
    dropped% Checked.Cosmography.FREta.printedEta20_false_at 2 := by
  intro Ω h0 hd hne h
  have h2 : Ω - 2 ≠ 0 := by
    intro e; apply hd; rw [printedDen_eq, e, zero_mul]
  exact hne (agree20_imp h0.ne' h2 hd ((eta20_hasDerivAt' h0.ne' h2).unique h))

/-- At Ω = 0 the family η₂₀(0, ·) is not continuous at 0: it is 0 there and tends to 13/1674 (for
ε ≠ 0 it equals (26 − 6ε)/(36(3ε³ + 7ε² + 33ε + 93))). -/
theorem eta20_zero_not_contAt : ¬ ContinuousAt (eta20 0) 0 := by
  intro hc
  set g : ℝ → ℝ := fun ε => (26 - 6 * ε) / (36 * (3 * ε ^ 3 + 7 * ε ^ 2 + 33 * ε + 93)) with hg
  have hgc : ContinuousAt g 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop); norm_num
  have heq : eta20 0 =ᶠ[nhdsWithin 0 {0}ᶜ] g := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : ε ≠ 0 := hε
    rw [eta20_eq]
    have hD : Dfam 0 ε = -(ε ^ 2 * (3 * ε ^ 3 + 7 * ε ^ 2 + 33 * ε + 93)) := by
      unfold Dfam P0 Q0 qL jL sL lL; ring
    have hN : N2e 0 ε = 6 * ε ^ 2 - 26 * ε := by unfold N2e; ring
    simp only [hD, hN, hg]
    by_cases hp : 3 * ε ^ 3 + 7 * ε ^ 2 + 33 * ε + 93 = 0
    · rw [hp]; simp
    · field_simp
      ring
  have t1 : Filter.Tendsto (eta20 0) (nhdsWithin 0 {0}ᶜ) (nhds (eta20 0 0)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have t2 : Filter.Tendsto (eta20 0) (nhdsWithin 0 {0}ᶜ) (nhds (g 0)) :=
    (hgc.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm
  have := tendsto_nhds_unique t1 t2
  rw [eta20_eq] at this
  norm_num [hg] at this

/-- `0 < Ω` (hypothesis 1) is redundant in `printedEta20_false_at`: for Ω < 0 the coefficients agree
only where hypothesis 4 fails, and at Ω = 0 the family η₂₀(0, ·) is not even continuous at 0. -/
theorem printedEta20_false_at_r1 :
    dropped% Checked.Cosmography.FREta.printedEta20_false_at 1 := by
  intro Ω h1 hd hne h
  rcases lt_trichotomy Ω 0 with hn | rfl | hp
  · have h2 : Ω - 2 ≠ 0 := by intro e; linarith
    exact hne (agree20_imp hn.ne h2 hd ((eta20_hasDerivAt' hn.ne h2).unique h))
  · exact eta20_zero_not_contAt h.continuousAt
  · exact Checked.Cosmography.FREta.printedEta20_false_at hp h1 hd hne h

end Checked.Trust.NecessityEta
