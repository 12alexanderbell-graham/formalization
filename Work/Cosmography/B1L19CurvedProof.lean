import Work.Cosmography.B1L19CurvedRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Proof of `Work.Cosmography.B1L19Curved`: reduction to the certified ratio bound

`d_L(4√2 − 1)/d_L(2√2 − 1) = 2 S(J₅)/S(J₃) ≥ 27/10` for every `m ∈ [1/10, 1]`, `k ∈ [−1/10, 0]`,
with `S(J) = sin(√−k J)/√−k` (or `J` if `k = 0`), from `Work.Cosmography.B1L19CurvedCerts.ratio_bound`
and `sin x ≤ x`, `sin x > x − x³/6`.
-/

namespace Work.Cosmography.B1L19CurvedProof

open Set Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.BambaK
open Checked.Cosmography.B1 Checked.Cosmography.B1Fit Checked.Cosmography.B1L19
open Work.Cosmography.B1L19CurvedTools

/-- The transverse factor in terms of `κ = −k ≥ 0`. -/
noncomputable def S (κ J : ℝ) : ℝ := if κ = 0 then J else Real.sin (√κ * J) / √κ

lemma S_ratio (κ J₃ J₅ U J₃u J₅l : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 10) (hJ3 : 0 < J₃)
    (h35 : J₃ ≤ J₅) (h3u : J₃ ≤ J₃u) (h5l : J₅l ≤ J₅) (h5u : J₅ ≤ U)
    (hb : 27 / 10 * J₃u ≤ 2 * J₅l - 2 * κ * U ^ 3 / 4) (hU : U ^ 2 ≤ 10) :
    0 < S κ J₃ ∧ 27 / 10 * S κ J₃ ≤ 2 * S κ J₅ := by
  have hJ5 : 0 < J₅ := lt_of_lt_of_le hJ3 h35
  have hU0 : 0 ≤ U := le_trans hJ5.le h5u
  unfold S
  rcases eq_or_lt_of_le hκ0 with h | h
  · subst h
    simp only [ite_true]
    refine ⟨hJ3, ?_⟩
    nlinarith
  · have hne : κ ≠ 0 := h.ne'
    simp only [hne, ite_false]
    set s := √κ with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 h
    have hss : s ^ 2 = κ := Real.sq_sqrt h.le
    have hJ5U : J₅ ^ 3 ≤ U ^ 3 := pow_le_pow_left₀ hJ5.le h5u 3
    have hJ5U2 : J₅ ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ hJ5.le h5u 2
    -- lower bound for sin at the farther source
    have hsin5 := Real.sin_gt_sub_cube (mul_pos hs0 hJ5)
    have hsin3 := Real.sin_gt_sub_cube (mul_pos hs0 hJ3)
    have hle3 := Real.sin_le (mul_pos hs0 hJ3).le
    have e5 : (s * J₅ - (s * J₅) ^ 3 / 6) / s = J₅ - κ * J₅ ^ 3 / 6 := by
      rw [← hss]; field_simp
    have e3 : (s * J₃ - (s * J₃) ^ 3 / 6) / s = J₃ - κ * J₃ ^ 3 / 6 := by
      rw [← hss]; field_simp
    have l5 : J₅ - κ * J₅ ^ 3 / 6 < Real.sin (s * J₅) / s := by
      rw [← e5]; exact div_lt_div_of_pos_right hsin5 hs0
    have l3 : J₃ - κ * J₃ ^ 3 / 6 < Real.sin (s * J₃) / s := by
      rw [← e3]; exact div_lt_div_of_pos_right hsin3 hs0
    have u3 : Real.sin (s * J₃) / s ≤ J₃ := by
      rw [div_le_iff₀ hs0]; linarith
    have hJ32 : J₃ ^ 2 ≤ J₅ ^ 2 := pow_le_pow_left₀ hJ3.le h35 2
    have hk32 : κ * J₃ ^ 2 ≤ 1 := by nlinarith
    have pos3 : 0 < J₃ - κ * J₃ ^ 3 / 6 := by
      have : κ * J₃ ^ 3 = (κ * J₃ ^ 2) * J₃ := by ring
      nlinarith
    refine ⟨by linarith, ?_⟩
    have c1 : κ * J₅ ^ 3 / 6 ≤ κ * U ^ 3 / 4 := by
      have : κ * J₅ ^ 3 ≤ κ * U ^ 3 := mul_le_mul_of_nonneg_left hJ5U hκ0
      have : 0 ≤ κ * U ^ 3 := by positivity
      linarith
    nlinarith

lemma sqrtk (Ω₀ : ℝ) : √(-(1 - Ω₀)) = √(Ω₀ - 1) := by ring_nf

/-- The residual difference is at least `5 log₁₀(27/10 · P(x₃)/P(x₅))`. -/
lemma delta_curved (Ω K : ℝ) (hΩ₀ : 1 / 10 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hK₀ : 1 ≤ omega0 K a t₀) (hK₁ : omega0 K a t₀ ≤ 11 / 10)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3
        + (1 - omega0 K a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 K a t₀ - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ a₄ H : ℝ) (hHp : 0 < H) (x₃ x₅ : ℝ)
    (hx₃ : Real.logb 10 (1 + (2 * √2 - 1)) = x₃) (hx₅ : Real.logb 10 (1 + (4 * √2 - 1)) = x₅)
    (hQ3 : 0 < x₃ + a₂ * x₃ ^ 2 + a₃ * x₃ ^ 3 + a₄ * x₃ ^ 4)
    (hQ5 : 0 < x₅ + a₂ * x₅ ^ 2 + a₃ * x₅ ^ 3 + a₄ * x₅ ^ 4) :
    5 * Real.logb 10 (27 / 10 * (x₃ + a₂ * x₃ ^ 2 + a₃ * x₃ ^ 3 + a₄ * x₃ ^ 4)
        / (x₅ + a₂ * x₅ ^ 2 + a₃ * x₅ ^ 3 + a₄ * x₅ ^ 4))
      ≤ 5 * Real.logb 10 (lumDist K a t₀ t₅ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅))
        - 5 * Real.logb 10 (lumDist K a t₀ t₃ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₃)) := by
  set k := 1 - omega0 K a t₀ with hk
  have hd : Dom Ω k := ⟨hΩ₀, hΩ₁, by linarith, by linarith⟩
  have hH' : ∀ s ∈ Set.Icc t₅ t₀, hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3
      + k * (1 + redshift a t₀ s) ^ 2 + (1 - k) - Ω) := by
    intro s hs; rw [hH s hs, hk]; ring_nf
  have h₅₀ : t₅ ≤ t₀ := le_trans h₅₃ h₃₀
  have hsub3 : Set.Icc t₃ t₀ ⊆ Set.Icc t₅ t₀ := Set.Icc_subset_Icc_left h₅₃
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨h₅₀, le_rfl⟩
  have ha3 : 0 < a t₃ := hpos t₃ ⟨h₅₃, h₃₀⟩
  have ha5 : 0 < a t₅ := hpos t₅ ⟨le_rfl, h₅₀⟩
  have hχ3 := comoving_eq hd a t₃ t₀ h₃₀ (fun s hs => hpos s (hsub3 hs))
    (fun s hs => hdiff s (hsub3 hs)) hH₀ (fun s hs => hH' s (hsub3 hs))
  have hχ5 := comoving_eq hd a t₅ t₀ h₅₀ hpos hdiff hH₀ hH'
  -- K ≥ 0
  have hK : 0 ≤ K := by
    have h1 : 0 ≤ K / (hubble a t₀ ^ 2 * a t₀ ^ 2) := by unfold omega0 at hK₀; linarith
    have h2 : 0 < hubble a t₀ ^ 2 * a t₀ ^ 2 := by positivity
    by_contra hneg; push Not at hneg
    have : K / (hubble a t₀ ^ 2 * a t₀ ^ 2) < 0 := div_neg_of_neg_of_pos hneg h2
    linarith
  have hd3 := lumDist_eq K a t₀ t₃ _ ha₀ hH₀ hχ3 hK
  have hd5 := lumDist_eq K a t₀ t₅ _ ha₀ hH₀ hχ5 hK
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  rw [ratio_of_z a t₃ t₀ _ ha3 ha₀ hz₃, es3, hz₃, es3] at hd3
  rw [ratio_of_z a t₅ t₀ _ ha5 ha₀ hz₅, es5, hz₅, es5] at hd5
  set κ := omega0 K a t₀ - 1 with hκ
  have hκk : -k = κ := by rw [hk, hκ]; ring
  set J3 := ∫ v in √(1 / (2 * √2))..1, gC Ω k v with hJ3
  set J5 := ∫ v in √(1 / (4 * √2))..1, gC Ω k v with hJ5
  have hS3 : lumDist K a t₀ t₃ = 2 * √2 / hubble a t₀ * S κ J3 := by rw [hd3]; rfl
  have hS5 : lumDist K a t₀ t₅ = 4 * √2 / hubble a t₀ * S κ J5 := by rw [hd5]; rfl
  set H₀ := hubble a t₀ with hH₀def
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq2 : 0 < √2 := by linarith
  have hs3 : 1 < 2 * √2 := by linarith
  have hs5 : 1 < 4 * √2 := by linarith
  obtain ⟨hw3p, hw3⟩ := w_lt_one _ hs3
  obtain ⟨hw5p, hw5⟩ := w_lt_one _ hs5
  have hJ3p : 0 < J3 := Jpos hd _ hw3p hw3
  obtain ⟨wb3u, wb3l⟩ := wb (2 * √2) (148651 / 250000) (594603 / 1000000) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb5u, wb5l⟩ := wb (4 * √2) (420449 / 1000000) (13139 / 31250) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  have hJ3u : J3 ≤ ∫ v in (594603 / 1000000 : ℝ)..1, gC Ω k v :=
    J_shift hd _ _ (by norm_num) wb3u hw3.le
  have hJ5l : ∫ v in (420449 / 1000000 : ℝ)..1, gC Ω k v ≤ J5 :=
    J_shift hd _ _ hw5p wb5l (by norm_num)
  have hJ5u : J5 ≤ ∫ v in (13139 / 31250 : ℝ)..1, gC Ω k v :=
    J_shift hd _ _ (by norm_num) wb5u hw5.le
  have h35 : J3 ≤ J5 := by
    apply J_shift hd _ _ hw5p _ hw3.le
    apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le (by positivity); linarith
  obtain ⟨U, hU1, hU2, hU3⟩ := Work.Cosmography.B1L19CurvedCerts.ratio_bound Ω k hd
  rw [hκk] at hU2
  have hκ0 : 0 ≤ κ := by rw [← hκk]; linarith [hd.k1]
  have hκ1 : κ ≤ 1 / 10 := by rw [← hκk]; linarith [hd.k0]
  obtain ⟨hSp, hSr⟩ := S_ratio κ J3 J5 U _ _ hκ0 hκ1 hJ3p h35 hJ3u hJ5l (le_trans hJ5u hU1) hU2 hU3
  have hS5p : 0 < S κ J5 := by linarith
  set Q3 := x₃ + a₂ * x₃ ^ 2 + a₃ * x₃ ^ 3 + a₄ * x₃ ^ 4 with hQ3def
  set Q5 := x₅ + a₂ * x₅ ^ 2 + a₃ * x₅ ^ 3 + a₄ * x₅ ^ 4 with hQ5def
  have hl0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  rw [hz₃, hz₅, lp4_eq a₂ a₃ a₄ H x₃ _ hx₃, lp4_eq a₂ a₃ a₄ H x₅ _ hx₅, hS3, hS5]
  have hX3 : 0 < 2 * √2 / H₀ * S κ J3 / (Real.log 10 / H * Q3) := by positivity
  have hX5 : 0 < 4 * √2 / H₀ * S κ J5 / (Real.log 10 / H * Q5) := by positivity
  have e : 5 * Real.logb 10 (4 * √2 / H₀ * S κ J5 / (Real.log 10 / H * Q5))
      - 5 * Real.logb 10 (2 * √2 / H₀ * S κ J3 / (Real.log 10 / H * Q3))
      = 5 * Real.logb 10 ((4 * √2 / H₀ * S κ J5 / (Real.log 10 / H * Q5))
          / (2 * √2 / H₀ * S κ J3 / (Real.log 10 / H * Q3))) := by
    rw [Real.logb_div hX5.ne' hX3.ne']; ring
  have key : (4 * √2 / H₀ * S κ J5 / (Real.log 10 / H * Q5))
      / (2 * √2 / H₀ * S κ J3 / (Real.log 10 / H * Q3)) = 2 * S κ J5 / S κ J3 * (Q3 / Q5) := by
    field_simp; ring
  rw [e, key]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
  have hJ : 27 / 10 ≤ 2 * S κ J5 / S κ J3 := by rw [le_div_iff₀ hSp]; linarith
  rw [show 27 / 10 * Q3 / Q5 = 27 / 10 * (Q3 / Q5) by ring]
  exact mul_le_mul_of_nonneg_right hJ (by positivity)

/-- The common core of the frozen and the blind proofs: from the two distances in the form
`(1+z)/H₀ · S(κ, J)` to the residual difference bound. -/
lemma delta_core (Ω k κ : ℝ) (hd : Dom Ω k) (hκk : -k = κ) (K H₀ : ℝ) (hH₀ : 0 < H₀)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (ha₀ : 0 < a t₀) (ha3 : 0 < a t₃) (ha5 : 0 < a t₅)
    (hd3 : lumDist K a t₀ t₃ = (1 + redshift a t₀ t₃) / H₀ *
      S κ (∫ v in √(a t₃ / a t₀)..1, gC Ω k v))
    (hd5 : lumDist K a t₀ t₅ = (1 + redshift a t₀ t₅) / H₀ *
      S κ (∫ v in √(a t₅ / a t₀)..1, gC Ω k v))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ a₄ H : ℝ) (hHp : 0 < H) (x₃ x₅ : ℝ)
    (hx₃ : Real.logb 10 (1 + (2 * √2 - 1)) = x₃) (hx₅ : Real.logb 10 (1 + (4 * √2 - 1)) = x₅)
    (hQ3 : 0 < x₃ + a₂ * x₃ ^ 2 + a₃ * x₃ ^ 3 + a₄ * x₃ ^ 4)
    (hQ5 : 0 < x₅ + a₂ * x₅ ^ 2 + a₃ * x₅ ^ 3 + a₄ * x₅ ^ 4) :
    5 * Real.logb 10 (27 / 10 * (x₃ + a₂ * x₃ ^ 2 + a₃ * x₃ ^ 3 + a₄ * x₃ ^ 4)
        / (x₅ + a₂ * x₅ ^ 2 + a₃ * x₅ ^ 3 + a₄ * x₅ ^ 4))
      ≤ 5 * Real.logb 10 (lumDist K a t₀ t₅ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₅))
        - 5 * Real.logb 10 (lumDist K a t₀ t₃ / logPolyDL4 a₂ a₃ a₄ H (redshift a t₀ t₃)) := by
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  rw [ratio_of_z a t₃ t₀ _ ha3 ha₀ hz₃, es3, hz₃, es3] at hd3
  rw [ratio_of_z a t₅ t₀ _ ha5 ha₀ hz₅, es5, hz₅, es5] at hd5
  set J3 := ∫ v in √(1 / (2 * √2))..1, gC Ω k v with hJ3
  set J5 := ∫ v in √(1 / (4 * √2))..1, gC Ω k v with hJ5
  have hS3 : lumDist K a t₀ t₃ = 2 * √2 / H₀ * S κ J3 := by rw [hd3]
  have hS5 : lumDist K a t₀ t₅ = 4 * √2 / H₀ * S κ J5 := by rw [hd5]
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq2 : 0 < √2 := by linarith
  have hs3 : 1 < 2 * √2 := by linarith
  have hs5 : 1 < 4 * √2 := by linarith
  obtain ⟨hw3p, hw3⟩ := w_lt_one _ hs3
  obtain ⟨hw5p, hw5⟩ := w_lt_one _ hs5
  have hJ3p : 0 < J3 := Jpos hd _ hw3p hw3
  obtain ⟨wb3u, wb3l⟩ := wb (2 * √2) (148651 / 250000) (594603 / 1000000) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb5u, wb5l⟩ := wb (4 * √2) (420449 / 1000000) (13139 / 31250) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  have hJ3u : J3 ≤ ∫ v in (594603 / 1000000 : ℝ)..1, gC Ω k v :=
    J_shift hd _ _ (by norm_num) wb3u hw3.le
  have hJ5l : ∫ v in (420449 / 1000000 : ℝ)..1, gC Ω k v ≤ J5 :=
    J_shift hd _ _ hw5p wb5l (by norm_num)
  have hJ5u : J5 ≤ ∫ v in (13139 / 31250 : ℝ)..1, gC Ω k v :=
    J_shift hd _ _ (by norm_num) wb5u hw5.le
  have h35 : J3 ≤ J5 := by
    apply J_shift hd _ _ hw5p _ hw3.le
    apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le (by positivity); linarith
  obtain ⟨U, hU1, hU2, hU3⟩ := Work.Cosmography.B1L19CurvedCerts.ratio_bound Ω k hd
  rw [hκk] at hU2
  have hκ0 : 0 ≤ κ := by rw [← hκk]; linarith [hd.k1]
  have hκ1 : κ ≤ 1 / 10 := by rw [← hκk]; linarith [hd.k0]
  obtain ⟨hSp, hSr⟩ := S_ratio κ J3 J5 U _ _ hκ0 hκ1 hJ3p h35 hJ3u hJ5l (le_trans hJ5u hU1) hU2 hU3
  have hS5p : 0 < S κ J5 := by linarith
  set Q3 := x₃ + a₂ * x₃ ^ 2 + a₃ * x₃ ^ 3 + a₄ * x₃ ^ 4 with hQ3def
  set Q5 := x₅ + a₂ * x₅ ^ 2 + a₃ * x₅ ^ 3 + a₄ * x₅ ^ 4 with hQ5def
  have hl0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  rw [hz₃, hz₅, lp4_eq a₂ a₃ a₄ H x₃ _ hx₃, lp4_eq a₂ a₃ a₄ H x₅ _ hx₅, hS3, hS5]
  have hX3 : 0 < 2 * √2 / H₀ * S κ J3 / (Real.log 10 / H * Q3) := by positivity
  have hX5 : 0 < 4 * √2 / H₀ * S κ J5 / (Real.log 10 / H * Q5) := by positivity
  have e : 5 * Real.logb 10 (4 * √2 / H₀ * S κ J5 / (Real.log 10 / H * Q5))
      - 5 * Real.logb 10 (2 * √2 / H₀ * S κ J3 / (Real.log 10 / H * Q3))
      = 5 * Real.logb 10 ((4 * √2 / H₀ * S κ J5 / (Real.log 10 / H * Q5))
          / (2 * √2 / H₀ * S κ J3 / (Real.log 10 / H * Q3))) := by
    rw [Real.logb_div hX5.ne' hX3.ne']; ring
  have key : (4 * √2 / H₀ * S κ J5 / (Real.log 10 / H * Q5))
      / (2 * √2 / H₀ * S κ J3 / (Real.log 10 / H * Q3)) = 2 * S κ J5 / S κ J3 * (Q3 / Q5) := by
    field_simp; ring
  rw [e, key]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
  have hJ : 27 / 10 ≤ 2 * S κ J5 / S κ J3 := by rw [le_div_iff₀ hSp]; linarith
  rw [show 27 / 10 * Q3 / Q5 = 27 / 10 * (Q3 / Q5) by ring]
  exact mul_le_mul_of_nonneg_right hJ (by positivity)


lemma logb_11225 : (1 / 20 : ℝ) < Real.logb 10 1.1225 := by
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
  have h1 : ((10:ℝ) ^ (1:ℕ)) ^ ((20:ℕ)⁻¹ : ℝ) < ((1.1225:ℝ) ^ (20:ℕ)) ^ ((20:ℕ)⁻¹ : ℝ) :=
    Real.rpow_lt_rpow (by positivity) (by norm_num) (by norm_num)
  rw [Real.pow_rpow_inv_natCast (by norm_num) (by norm_num), ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)] at h1
  convert h1 using 2; norm_num

lemma logb_108 : (3 / 100 : ℝ) < Real.logb 10 1.08 := by
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
  have h1 : ((10:ℝ) ^ (3:ℕ)) ^ ((100:ℕ)⁻¹ : ℝ) < ((1.08:ℝ) ^ (100:ℕ)) ^ ((100:ℕ)⁻¹ : ℝ) :=
    Real.rpow_lt_rpow (by positivity) (by norm_num) (by norm_num)
  rw [Real.pow_rpow_inv_natCast (by norm_num) (by norm_num), ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)] at h1
  convert h1 using 2; norm_num

lemma poly_sq (L : ℝ) (hL1 : 30101 / 100000 ≤ L) (hL2 : L ≤ 30105 / 100000) :
    0 < 5 / 2 * L + 3.075 * (5 / 2 * L) ^ 2 + 4.466 * (5 / 2 * L) ^ 3 + (-3.716) * (5 / 2 * L) ^ 4 ∧
    1.1225 * (5 / 2 * L + 3.075 * (5 / 2 * L) ^ 2 + 4.466 * (5 / 2 * L) ^ 3 + (-3.716) * (5 / 2 * L) ^ 4)
      < 27 / 10 * (3 / 2 * L + 3.075 * (3 / 2 * L) ^ 2 + 4.466 * (3 / 2 * L) ^ 3
        + (-3.716) * (3 / 2 * L) ^ 4) := by
  have hL0 : 0 < L := by linarith
  have l2a : (30101 / 100000) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL1 2
  have l2b : L ^ 2 ≤ (30105 / 100000) ^ 2 := pow_le_pow_left₀ hL0.le hL2 2
  have l3a : (30101 / 100000) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL1 3
  have l3b : L ^ 3 ≤ (30105 / 100000) ^ 3 := pow_le_pow_left₀ hL0.le hL2 3
  constructor
  · have hG : 0 < 1 + 3.075 * (5 / 2 * L) + 4.466 * (5 / 2) ^ 2 * L ^ 2 - 3.716 * (5 / 2) ^ 3 * L ^ 3 := by
      norm_num at l2a l2b l3a l3b ⊢; linarith
    have e : 5 / 2 * L + 3.075 * (5 / 2 * L) ^ 2 + 4.466 * (5 / 2 * L) ^ 3 + (-3.716) * (5 / 2 * L) ^ 4
        = 5 / 2 * L * (1 + 3.075 * (5 / 2 * L) + 4.466 * (5 / 2) ^ 2 * L ^ 2 - 3.716 * (5 / 2) ^ 3 * L ^ 3) := by
      ring
    rw [e]; positivity
  · have hF : 0 < (27 / 10 * (3 / 2) - 1.1225 * (5 / 2)) + 3.075 * (27 / 10 * (3 / 2) ^ 2 - 1.1225 * (5 / 2) ^ 2) * L
        + 4.466 * (27 / 10 * (3 / 2) ^ 3 - 1.1225 * (5 / 2) ^ 3) * L ^ 2
        + (-3.716) * (27 / 10 * (3 / 2) ^ 4 - 1.1225 * (5 / 2) ^ 4) * L ^ 3 := by
      norm_num at l2a l2b l3a l3b ⊢; linarith
    have e : 27 / 10 * (3 / 2 * L + 3.075 * (3 / 2 * L) ^ 2 + 4.466 * (3 / 2 * L) ^ 3 + (-3.716) * (3 / 2 * L) ^ 4)
        - 1.1225 * (5 / 2 * L + 3.075 * (5 / 2 * L) ^ 2 + 4.466 * (5 / 2 * L) ^ 3 + (-3.716) * (5 / 2 * L) ^ 4)
        = L * ((27 / 10 * (3 / 2) - 1.1225 * (5 / 2)) + 3.075 * (27 / 10 * (3 / 2) ^ 2 - 1.1225 * (5 / 2) ^ 2) * L
        + 4.466 * (27 / 10 * (3 / 2) ^ 3 - 1.1225 * (5 / 2) ^ 3) * L ^ 2
        + (-3.716) * (27 / 10 * (3 / 2) ^ 4 - 1.1225 * (5 / 2) ^ 4) * L ^ 3) := by ring
    nlinarith [mul_pos hL0 hF]

lemma poly_sqg (L : ℝ) (hL1 : 30101 / 100000 ≤ L) (hL2 : L ≤ 30105 / 100000) :
    0 < 5 / 2 * L + 3.205 * (5 / 2 * L) ^ 2 + 3.564 * (5 / 2 * L) ^ 3 + (-2.510) * (5 / 2 * L) ^ 4 ∧
    1.08 * (5 / 2 * L + 3.205 * (5 / 2 * L) ^ 2 + 3.564 * (5 / 2 * L) ^ 3 + (-2.510) * (5 / 2 * L) ^ 4)
      < 27 / 10 * (3 / 2 * L + 3.205 * (3 / 2 * L) ^ 2 + 3.564 * (3 / 2 * L) ^ 3
        + (-2.510) * (3 / 2 * L) ^ 4) := by
  have hL0 : 0 < L := by linarith
  have l2a : (30101 / 100000) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL1 2
  have l2b : L ^ 2 ≤ (30105 / 100000) ^ 2 := pow_le_pow_left₀ hL0.le hL2 2
  have l3a : (30101 / 100000) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL1 3
  have l3b : L ^ 3 ≤ (30105 / 100000) ^ 3 := pow_le_pow_left₀ hL0.le hL2 3
  constructor
  · have hG : 0 < 1 + 3.205 * (5 / 2 * L) + 3.564 * (5 / 2) ^ 2 * L ^ 2 - 2.510 * (5 / 2) ^ 3 * L ^ 3 := by
      norm_num at l2a l2b l3a l3b ⊢; linarith
    have e : 5 / 2 * L + 3.205 * (5 / 2 * L) ^ 2 + 3.564 * (5 / 2 * L) ^ 3 + (-2.510) * (5 / 2 * L) ^ 4
        = 5 / 2 * L * (1 + 3.205 * (5 / 2 * L) + 3.564 * (5 / 2) ^ 2 * L ^ 2 - 2.510 * (5 / 2) ^ 3 * L ^ 3) := by
      ring
    rw [e]; positivity
  · have hF : 0 < (27 / 10 * (3 / 2) - 1.08 * (5 / 2)) + 3.205 * (27 / 10 * (3 / 2) ^ 2 - 1.08 * (5 / 2) ^ 2) * L
        + 3.564 * (27 / 10 * (3 / 2) ^ 3 - 1.08 * (5 / 2) ^ 3) * L ^ 2
        + (-2.510) * (27 / 10 * (3 / 2) ^ 4 - 1.08 * (5 / 2) ^ 4) * L ^ 3 := by
      norm_num at l2a l2b l3a l3b ⊢; linarith
    have e : 27 / 10 * (3 / 2 * L + 3.205 * (3 / 2 * L) ^ 2 + 3.564 * (3 / 2 * L) ^ 3 + (-2.510) * (3 / 2 * L) ^ 4)
        - 1.08 * (5 / 2 * L + 3.205 * (5 / 2 * L) ^ 2 + 3.564 * (5 / 2 * L) ^ 3 + (-2.510) * (5 / 2 * L) ^ 4)
        = L * ((27 / 10 * (3 / 2) - 1.08 * (5 / 2)) + 3.205 * (27 / 10 * (3 / 2) ^ 2 - 1.08 * (5 / 2) ^ 2) * L
        + 3.564 * (27 / 10 * (3 / 2) ^ 3 - 1.08 * (5 / 2) ^ 3) * L ^ 2
        + (-2.510) * (27 / 10 * (3 / 2) ^ 4 - 1.08 * (5 / 2) ^ 4) * L ^ 3) := by ring
    nlinarith [mul_pos hL0 hF]

end Work.Cosmography.B1L19CurvedProof
