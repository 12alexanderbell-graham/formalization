import Checked.Data.FR13
import Checked.Trust.NonVacuity

/-! Hypothesis necessity for the six Farooq–Ratra data headlines of `Checked.Data.FR13` (run
2026-11-18T1828Z). Each says something about a minimiser Ω over the unit interval of the marginalised
chi-square; hypotheses 1 and 2 are the two ends of that interval, hypothesis 3 is the minimiser condition.

Outside the unit interval the marginalised chi-square is large, so 1 and 2 are REDUNDANT (each alone): by
the closed form `margChi_closed` it is at least the chi-square plus the prior term at one value of the
Hubble constant (`margChi_ge`), hence at least the term of the farthest row of the table plus the prior
term (`row_ge`). For Ω at most zero the model's expansion factor at that row is at most one, and for Ω at
least one it is at least five and a half, and in both cases the sum is at least fifty for either prior
(`lo_bound`, `hi_bound`, case analysis on the Hubble constant), above the certified value at the interior
point (`minhi68`, `minhi73`), so such an Ω is never a minimiser over the unit interval. The same bound at
Ω equal to zero makes hypothesis 3 of `fr13_minval68` and `fr13_minval738` NEEDED: zero lies in the unit
interval but its chi-square is far above the stated window. -/

namespace Checked.Trust.NecessityAU
open Checked.Data.FR13Tools Checked.Data.FR13Certs Checked.Data.FR13Val Checked.Data.FR13ValCerts
  Checked.Data.FR13

/-- The marginalised chi-square is at least χ² plus the prior term at one value of H₀ (the
minimiser B/A of the Gaussian exponent), for every table and every Ω. -/
theorem margChi_ge {n : ℕ} (t : Fin n → ℝ × ℝ × ℝ) (Hb σ Ω : ℝ) (hσ : 0 < σ) :
    ∃ H : ℝ, chiSq t H Ω + (H - Hb) ^ 2 / σ ^ 2 ≤ margChi t Hb σ Ω := by
  rw [margChi_closed t Hb σ Ω hσ]
  have hS2 : 0 ≤ S2 t Ω := Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hA : 0 < S2 t Ω + 1 / σ ^ 2 := by positivity
  have hlog : 0 ≤ Real.log (σ ^ 2 * (S2 t Ω + 1 / σ ^ 2)) := by
    apply Real.log_nonneg
    have : σ ^ 2 * (S2 t Ω + 1 / σ ^ 2) = σ ^ 2 * S2 t Ω + 1 := by field_simp
    rw [this]; nlinarith
  refine ⟨(S1 t Ω + Hb / σ ^ 2) / (S2 t Ω + 1 / σ ^ 2), ?_⟩
  rw [chiSq_expand]
  have key : ((S1 t Ω + Hb / σ ^ 2) / (S2 t Ω + 1 / σ ^ 2)) ^ 2 * S2 t Ω
      - 2 * ((S1 t Ω + Hb / σ ^ 2) / (S2 t Ω + 1 / σ ^ 2)) * S1 t Ω + S0 t
      + ((S1 t Ω + Hb / σ ^ 2) / (S2 t Ω + 1 / σ ^ 2) - Hb) ^ 2 / σ ^ 2
      = (S0 t + Hb ^ 2 / σ ^ 2)
        - (S1 t Ω + Hb / σ ^ 2) ^ 2 / (S2 t Ω + 1 / σ ^ 2) := by
    field_simp
    ring
  linarith

/-- The chi-square is at least the term of the farthest row of the Farooq–Ratra table. -/
theorem row_ge (H Ω : ℝ) :
    ((H * √(Ω * (1 + 2.3) ^ 3 + 1 - Ω) - 224) / 8) ^ 2 ≤ chiSq tbl H Ω := by
  unfold chiSq
  have h := Finset.single_le_sum
    (f := fun i : Fin 28 => ((H * √(Ω * (1 + (tbl i).1) ^ 3 + 1 - Ω) - (tbl i).2.1) / (tbl i).2.2) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ (27 : Fin 28))
  have e : tbl 27 = (2.300, 224, 8) := by
    simp [tbl]
  simp only [e] at h
  convert h using 3
  norm_num

/-- Clearing the two denominators. -/
theorem two_terms (X Y c : ℝ) (hc : 0 < c) (h : 50 * (64 * c) ≤ c * X + 64 * Y) :
    50 ≤ X / 8 ^ 2 + Y / c := by
  rw [div_add_div _ _ (by norm_num) hc.ne', le_div_iff₀ (by positivity)]
  nlinarith

/-- For Ω ≤ 0 the row term plus the prior term is at least 50, for either prior. -/
theorem lo_bound (Hb σ Ω H : ℝ) (hΩ : Ω ≤ 0)
    (hp : (Hb = 68 ∧ σ = 2.8) ∨ (Hb = 73.8 ∧ σ = 2.4)) :
    50 ≤ ((H * √(Ω * (1 + 2.3) ^ 3 + 1 - Ω) - 224) / 8) ^ 2 + (H - Hb) ^ 2 / σ ^ 2 := by
  set s := √(Ω * (1 + 2.3) ^ 3 + 1 - Ω) with hs
  have s0 : 0 ≤ s := Real.sqrt_nonneg _
  have s1 : s ≤ 1 := by
    rw [hs, Real.sqrt_le_one]
    nlinarith
  rw [div_pow]
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · apply two_terms _ _ _ (by norm_num)
    rcases le_or_gt H 0 with h | h
    · have : H * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h s0
      nlinarith [sq_nonneg (H - 68)]
    rcases le_or_gt H 224 with h' | h'
    · have hx : H * s ≤ H := by nlinarith
      have : (224 - H) ^ 2 ≤ (H * s - 224) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (H - 85)]
    · nlinarith [sq_nonneg (H * s - 224)]
  · apply two_terms _ _ _ (by norm_num)
    rcases le_or_gt H 0 with h | h
    · have : H * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h s0
      nlinarith [sq_nonneg (H - 73.8)]
    rcases le_or_gt H 224 with h' | h'
    · have hx : H * s ≤ H := by nlinarith
      have : (224 - H) ^ 2 ≤ (H * s - 224) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (H - 86.2)]
    · nlinarith [sq_nonneg (H * s - 224)]

/-- For Ω ≥ 1 the row term plus the prior term is at least 50, for either prior. -/
theorem hi_bound (Hb σ Ω H : ℝ) (hΩ : 1 ≤ Ω)
    (hp : (Hb = 68 ∧ σ = 2.8) ∨ (Hb = 73.8 ∧ σ = 2.4)) :
    50 ≤ ((H * √(Ω * (1 + 2.3) ^ 3 + 1 - Ω) - 224) / 8) ^ 2 + (H - Hb) ^ 2 / σ ^ 2 := by
  set s := √(Ω * (1 + 2.3) ^ 3 + 1 - Ω) with hs
  have s1 : 5.99 ≤ s := by
    rw [hs, Real.le_sqrt (by norm_num) (by nlinarith)]
    nlinarith
  rw [div_pow]
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · apply two_terms _ _ _ (by norm_num)
    rcases lt_or_ge (5.99 * H) 224 with h | h
    · nlinarith [sq_nonneg (H * s - 224)]
    · have hx : 5.99 * H ≤ H * s := by nlinarith
      have : (5.99 * H - 224) ^ 2 ≤ (H * s - 224) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (H - 43)]
  · apply two_terms _ _ _ (by norm_num)
    rcases lt_or_ge (5.99 * H) 224 with h | h
    · nlinarith [sq_nonneg (H * s - 224)]
    · have hx : 5.99 * H ≤ H * s := by nlinarith
      have : (5.99 * H - 224) ^ 2 ≤ (H * s - 224) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (H - 46)]

/-- Outside the open unit interval the marginalised chi-square of the table is at least 50, for either prior. -/
theorem outside_ge (Hb σ Ω : ℝ) (hΩ : Ω ≤ 0 ∨ 1 ≤ Ω)
    (hp : (Hb = 68 ∧ σ = 2.8) ∨ (Hb = 73.8 ∧ σ = 2.4)) :
    50 ≤ margChiSq fr13Table Hb σ Ω := by
  have hσ : 0 < σ := by rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  rw [margChiSq_eq]
  obtain ⟨H, hH⟩ := margChi_ge tbl Hb σ Ω hσ
  have hr := row_ge H Ω
  have hb := hΩ.elim (fun h => lo_bound Hb σ Ω H h hp) (fun h => hi_bound Hb σ Ω H h hp)
  linarith

theorem out68 (Ω : ℝ) (hΩ : Ω ≤ 0 ∨ 1 ≤ Ω) : 50 ≤ margChiSq fr13Table 68 2.8 Ω :=
  outside_ge 68 2.8 Ω hΩ (Or.inl ⟨rfl, rfl⟩)

theorem out738 (Ω : ℝ) (hΩ : Ω ≤ 0 ∨ 1 ≤ Ω) : 50 ≤ margChiSq fr13Table 73.8 2.4 Ω :=
  outside_ge 73.8 2.4 Ω hΩ (Or.inr ⟨rfl, rfl⟩)

/-- No Ω outside the unit interval beats the interior certified point (first prior). -/
theorem no_out68 (Ω : ℝ) (hΩ : Ω < 0 ∨ 1 < Ω)
    (hmin : ∀ Ω' ∈ Set.Icc (0 : ℝ) 1, margChiSq fr13Table 68 2.8 Ω ≤ margChiSq fr13Table 68 2.8 Ω') :
    False := by
  have h1 := out68 Ω (hΩ.imp le_of_lt le_of_lt)
  have hr := hmin 0.2878 ⟨by norm_num, by norm_num⟩
  simp only [margChiSq_eq] at hr
  have := minhi68
  rw [margChiSq_eq] at h1
  linarith

/-- No Ω outside the unit interval beats the interior certified point (second prior). -/
theorem no_out738 (Ω : ℝ) (hΩ : Ω < 0 ∨ 1 < Ω)
    (hmin : ∀ Ω' ∈ Set.Icc (0 : ℝ) 1,
      margChiSq fr13Table 73.8 2.4 Ω ≤ margChiSq fr13Table 73.8 2.4 Ω') :
    False := by
  have h1 := out738 Ω (hΩ.imp le_of_lt le_of_lt)
  have hr := hmin 0.2534 ⟨by norm_num, by norm_num⟩
  simp only [margChiSq_eq] at hr
  have := minhi73
  rw [margChiSq_eq] at h1
  linarith

/-! ### Redundancy of the two ends of the interval (1 and 2), each alone -/

theorem fr13_bestfit68_r1 : dropped% Checked.Data.FR13.fr13_bestfit68 1 := by
  intro Ω h1 hmin
  rcases le_or_gt 0 Ω with h0 | h0
  · exact fr13_bestfit68 Ω h0 h1 hmin
  · exact (no_out68 Ω (Or.inl h0) hmin).elim

theorem fr13_bestfit68_r2 : dropped% Checked.Data.FR13.fr13_bestfit68 2 := by
  intro Ω h0 hmin
  rcases le_or_gt Ω 1 with h1 | h1
  · exact fr13_bestfit68 Ω h0 h1 hmin
  · exact (no_out68 Ω (Or.inr h1) hmin).elim

theorem fr13_bestfit738_r1 : dropped% Checked.Data.FR13.fr13_bestfit738 1 := by
  intro Ω h1 hmin
  rcases le_or_gt 0 Ω with h0 | h0
  · exact fr13_bestfit738 Ω h0 h1 hmin
  · exact (no_out738 Ω (Or.inl h0) hmin).elim

theorem fr13_bestfit738_r2 : dropped% Checked.Data.FR13.fr13_bestfit738 2 := by
  intro Ω h0 hmin
  rcases le_or_gt Ω 1 with h1 | h1
  · exact fr13_bestfit738 Ω h0 h1 hmin
  · exact (no_out738 Ω (Or.inr h1) hmin).elim

theorem fr13_minval68_r1 : dropped% Checked.Data.FR13.fr13_minval68 1 := by
  intro Ω h1 hmin
  rcases le_or_gt 0 Ω with h0 | h0
  · exact fr13_minval68 Ω h0 h1 hmin
  · exact (no_out68 Ω (Or.inl h0) hmin).elim

theorem fr13_minval68_r2 : dropped% Checked.Data.FR13.fr13_minval68 2 := by
  intro Ω h0 hmin
  rcases le_or_gt Ω 1 with h1 | h1
  · exact fr13_minval68 Ω h0 h1 hmin
  · exact (no_out68 Ω (Or.inr h1) hmin).elim

theorem fr13_minval738_r1 : dropped% Checked.Data.FR13.fr13_minval738 1 := by
  intro Ω h1 hmin
  rcases le_or_gt 0 Ω with h0 | h0
  · exact fr13_minval738 Ω h0 h1 hmin
  · exact (no_out738 Ω (Or.inl h0) hmin).elim

theorem fr13_minval738_r2 : dropped% Checked.Data.FR13.fr13_minval738 2 := by
  intro Ω h0 hmin
  rcases le_or_gt Ω 1 with h1 | h1
  · exact fr13_minval738 Ω h0 h1 hmin
  · exact (no_out738 Ω (Or.inr h1) hmin).elim

theorem fr13_zda68_r1 : dropped% Checked.Data.FR13.fr13_zda68 1 := by
  intro Ω h1 hmin z hz hda
  rcases le_or_gt 0 Ω with h0 | h0
  · exact fr13_zda68 Ω h0 h1 hmin z hz hda
  · exact (no_out68 Ω (Or.inl h0) hmin).elim

theorem fr13_zda68_r2 : dropped% Checked.Data.FR13.fr13_zda68 2 := by
  intro Ω h0 hmin z hz hda
  rcases le_or_gt Ω 1 with h1 | h1
  · exact fr13_zda68 Ω h0 h1 hmin z hz hda
  · exact (no_out68 Ω (Or.inr h1) hmin).elim

theorem fr13_zda738_r1 : dropped% Checked.Data.FR13.fr13_zda738 1 := by
  intro Ω h1 hmin z hz hda
  rcases le_or_gt 0 Ω with h0 | h0
  · exact fr13_zda738 Ω h0 h1 hmin z hz hda
  · exact (no_out738 Ω (Or.inl h0) hmin).elim

theorem fr13_zda738_r2 : dropped% Checked.Data.FR13.fr13_zda738 2 := by
  intro Ω h0 hmin z hz hda
  rcases le_or_gt Ω 1 with h1 | h1
  · exact fr13_zda738 Ω h0 h1 hmin z hz hda
  · exact (no_out738 Ω (Or.inr h1) hmin).elim

/-! ### The minimiser condition (3) of the two minimum-value headlines is needed: Ω equal to zero -/

theorem fr13_minval68_h3 : necessity% Checked.Data.FR13.fr13_minval68 3 := by
  refine ⟨0, le_rfl, zero_le_one, ?_⟩
  rintro ⟨-, h⟩
  have := out68 0 (Or.inl le_rfl)
  linarith

theorem fr13_minval738_h3 : necessity% Checked.Data.FR13.fr13_minval738 3 := by
  refine ⟨0, le_rfl, zero_le_one, ?_⟩
  rintro ⟨-, h⟩
  have := out738 0 (Or.inl le_rfl)
  linarith

end Checked.Trust.NecessityAU
