import Checked.Trust.NecessityBVCerts
import Checked.Cosmography.B1L19Curved
import Checked.Trust.Necessity

/-!
# Hypothesis necessity, the curved quartic pair: the sign of the curvature (trust track T2b)

Run 2026-11-25T1228Z. `B1L19Curved.l19_sq_curved` and `l19_sqg_curved` assume a closed or flat model: the
total density parameter at least one (hypothesis 8). That hypothesis is REDUNDANT in both
(`l19_sq_curved_r8`, `l19_sqg_curved_r8`): every open model with the same density range has the two-redshift
distance ratio of the closed proof, so the conclusion holds for every curvature below the upper bound.

* **The transverse factor** of an open model is a hyperbolic sine, and the hyperbolic sine over its argument
  increases (`sinh_ratio`), so the ratio of the two luminosity distances is at least twice the ratio of the two
  distance integrals; no cubic correction as in the closed case.
* **The integrals** are those of `Checked.Cosmography.B1L19CurvedTools` with a nonnegative and unbounded
  curvature parameter (`Checked.Trust.NCBV.DomO`). Up to twenty, generated tangent and chord cells on parameter
  boxes (`ratio_open`, `runs/2026-11-25T1228Z/scripts/gen_open.py`); above twenty, the integrand is within a
  fixed factor of an integrand with a closed-form antiderivative on each side of the nearer source
  (`NCBV.big_upper`, `NCBV.big_lower`), and the two antiderivative values compare by a rational power
  inequality (`big_k`).
-/

namespace Checked.Trust.NCBV

open Set Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.BambaK
open Checked.Cosmography.B1 Checked.Cosmography.B1Fit Checked.Cosmography.B1L19
open Checked.Cosmography.B1L19CurvedTools Checked.Cosmography.Transverse

/-- The hyperbolic sine over its argument increases. -/
lemma sinh_ratio (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) : Real.sinh x * y ≤ Real.sinh y * x := by
  have hg : MonotoneOn (fun t => t * Real.cosh t - Real.sinh t) (Ici 0) := by
    have hd : ∀ t, HasDerivAt (fun t => t * Real.cosh t - Real.sinh t) (t * Real.sinh t) t := by
      intro t
      have := ((hasDerivAt_id' t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)
      exact this.congr_deriv (by ring)
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (by fun_prop : Continuous fun t => t * Real.cosh t - Real.sinh t).continuousOn
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Ici] at ht
      rw [(hd t).deriv]; exact mul_nonneg (le_of_lt ht) (Real.sinh_nonneg_iff.2 (le_of_lt ht))
  have hq : MonotoneOn (fun t => Real.sinh t / t) (Ioi 0) := by
    have hd : ∀ t, t ≠ 0 → HasDerivAt (fun t => Real.sinh t / t)
        ((Real.cosh t * t - Real.sinh t * 1) / t ^ 2) t := by
      intro t ht
      exact (Real.hasDerivAt_sinh t).div (hasDerivAt_id t) ht
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro t ht; exact (hd t (ne_of_gt ht)).continuousAt.continuousWithinAt
    · intro t ht; rw [interior_Ioi] at ht
      exact (hd t (ne_of_gt ht)).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Ioi] at ht
      rw [(hd t (ne_of_gt ht)).deriv]
      have h0 := hg (mem_Ici.2 le_rfl) (mem_Ici.2 (le_of_lt ht)) (le_of_lt ht)
      simp only [Real.cosh_zero, Real.sinh_zero, zero_mul, sub_zero] at h0
      apply div_nonneg _ (by positivity)
      linarith
  have h := hq hx (lt_of_lt_of_le hx hxy) hxy
  simp only at h
  rw [div_le_div_iff₀ hx (lt_of_lt_of_le hx hxy)] at h
  linarith

/-- Above twenty the two integrals compare analytically. -/
lemma big_k (m k : ℝ) (hd : DomO m k) (hk : 20 ≤ k) :
    27 / 10 * ∫ v in (594603 / 1000000 : ℝ)..1, gC m k v
      ≤ 2 * ∫ v in (420449 / 1000000 : ℝ)..1, gC m k v := by
  have hk0 : 0 < k := by linarith
  have hU := big_upper hd hk0 (594603 / 1000000) (by norm_num) (by norm_num)
  have hL := big_lower hd (59 / 10) (420449 / 1000000) (594603 / 1000000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by
      intro v hv
      obtain ⟨h1, h2⟩ := hv
      have hu0 : (420449 / 1000000 : ℝ) ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
      have hu1 : v ^ 2 ≤ (594603 / 1000000 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
      have e : v ^ 6 = (v ^ 2) ^ 3 := by ring
      rw [e]
      set u := v ^ 2
      nlinarith [mul_nonneg (sub_nonneg.2 hu0) (sub_nonneg.2 hu1)])
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (gC_intIntO hd (420449 / 1000000) (594603 / 1000000) (by norm_num) (by norm_num) (by norm_num))
    (gC_intIntO hd (594603 / 1000000) 1 (by norm_num) (by norm_num) le_rfl)]
  set IL := ∫ v in (420449 / 1000000 : ℝ)..(594603 / 1000000), gC m k v
  set IR := ∫ v in (594603 / 1000000 : ℝ)..1, gC m k v
  -- the antiderivative values: −F(W₃) = log P₃, F(W₃) − F(W₅) = log P₅ − log P₃
  set s3 := √(1 - (594603 / 1000000 : ℝ) ^ 4)
  set s5 := √(1 - (420449 / 1000000 : ℝ) ^ 4)
  have hs3 : s3 ≤ 117 / 125 := by
    rw [show (117 / 125 : ℝ) = √((117 / 125) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs5 : 123 / 125 ≤ s5 := Real.le_sqrt_of_sq_le (by norm_num)
  have hs30 : 0 ≤ s3 := Real.sqrt_nonneg _
  set P3 := (1 + s3) / (594603 / 1000000 : ℝ) ^ 2
  set P5 := (1 + s5) / (420449 / 1000000 : ℝ) ^ 2
  have hF3 : Fo (594603 / 1000000) = -Real.log P3 := by
    unfold Fo; rw [Real.log_div (by positivity) (by positivity)]; ring
  have hF5 : Fo (420449 / 1000000) = -Real.log P5 := by
    unfold Fo; rw [Real.log_div (by positivity) (by positivity)]; ring
  have hP3 : 1 < P3 := by
    rw [lt_div_iff₀ (by norm_num)]; nlinarith
  have hP3u : P3 ≤ (1 + 117 / 125) / (594603 / 1000000 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by norm_num)
  have hP5l : (1 + 123 / 125) / (420449 / 1000000 : ℝ) ^ 2 ≤ P5 :=
    div_le_div_of_nonneg_right (by linarith) (by norm_num)
  have hpow : P3 ^ 7 ≤ P5 ^ 5 := by
    have h1 : P3 ^ 7 ≤ ((1 + 117 / 125) / (594603 / 1000000 : ℝ) ^ 2) ^ 7 :=
      pow_le_pow_left₀ (by linarith) hP3u 7
    have h2 : ((1 + 123 / 125) / (420449 / 1000000 : ℝ) ^ 2) ^ 5 ≤ P5 ^ 5 :=
      pow_le_pow_left₀ (by norm_num) hP5l 5
    have h3 : ((1 + 117 / 125) / (594603 / 1000000 : ℝ) ^ 2) ^ 7
        ≤ ((1 + 123 / 125) / (420449 / 1000000 : ℝ) ^ 2) ^ 5 := by norm_num
    linarith
  have hlog3 : 0 < Real.log P3 := Real.log_pos hP3
  have hlog : 7 * Real.log P3 ≤ 5 * Real.log P5 := by
    have := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow, Real.log_pow] at this
  rw [Fo_one, hF3] at hU
  rw [hF3, hF5] at hL
  -- 7/20 · IR ≤ IL
  have hsk : 0 < √k := Real.sqrt_pos.2 hk0
  have hskc : 0 < √(k + 59 / 10) := Real.sqrt_pos.2 (by linarith)
  have hsq : 7 / 20 * √(k + 59 / 10) ≤ 2 / 5 * √k := by
    have h1 : (7 / 20 * √(k + 59 / 10)) ^ 2 ≤ (2 / 5 * √k) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hk0.le]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h1
  have hU' : IR * √k ≤ Real.log P3 := by
    have := (le_div_iff₀ hsk).1 (by simpa using hU); linarith
  have hL' : 2 / 5 * Real.log P3 ≤ IL * √(k + 59 / 10) := by
    have := (div_le_iff₀ hskc).1 hL; linarith
  have key : 7 / 20 * IR ≤ IL := by
    have hIR : 0 ≤ IR := intervalIntegral.integral_nonneg (by norm_num) (fun v _ => gC_nonneg m k v)
    have hIL : 0 ≤ IL := intervalIntegral.integral_nonneg (by norm_num) (fun v _ => gC_nonneg m k v)
    nlinarith [mul_le_mul_of_nonneg_left hsq hIR, mul_nonneg hIR hsk.le]
  linarith

/-- On the whole open domain. -/
lemma ratio_all (m k : ℝ) (hd : DomO m k) :
    27 / 10 * ∫ v in (594603 / 1000000 : ℝ)..1, gC m k v
      ≤ 2 * ∫ v in (420449 / 1000000 : ℝ)..1, gC m k v := by
  rcases le_total k 20 with h | h
  · exact ratio_open m k hd h
  · exact big_k m k hd h

lemma scale_aux (X s3 s5 : ℝ) (hX : 0 ≤ X) (h : 27 / 10 * s3 ≤ 2 * s5) :
    27 / 10 * (X * (2 * s3)) ≤ X * (4 * s5) := by
  nlinarith [mul_le_mul_of_nonneg_left h hX]

/-- The residual difference of an open model is at least `5 log₁₀(27/10 · P(x₃)/P(x₅))`. -/
lemma delta_open (Ω K : ℝ) (hΩ₀ : 1 / 10 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hKo : omega0 K a t₀ < 1)
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
  have hd : DomO Ω k := ⟨hΩ₀, hΩ₁, by linarith⟩
  have hH' : ∀ s ∈ Set.Icc t₅ t₀, hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3
      + k * (1 + redshift a t₀ s) ^ 2 + (1 - k) - Ω) := by
    intro s hs; rw [hH s hs, hk]; ring_nf
  have h₅₀ : t₅ ≤ t₀ := le_trans h₅₃ h₃₀
  have hsub3 : Set.Icc t₃ t₀ ⊆ Set.Icc t₅ t₀ := Set.Icc_subset_Icc_left h₅₃
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨h₅₀, le_rfl⟩
  have ha3 : 0 < a t₃ := hpos t₃ ⟨h₅₃, h₃₀⟩
  have ha5 : 0 < a t₅ := hpos t₅ ⟨le_rfl, h₅₀⟩
  have hχ3 := comoving_eqO hd a t₃ t₀ h₃₀ (fun s hs => hpos s (hsub3 hs))
    (fun s hs => hdiff s (hsub3 hs)) hH₀ (fun s hs => hH' s (hsub3 hs))
  have hχ5 := comoving_eqO hd a t₅ t₀ h₅₀ hpos hdiff hH₀ hH'
  -- K < 0
  have hKn : K < 0 := by
    have h2 : 0 < hubble a t₀ ^ 2 * a t₀ ^ 2 := by positivity
    have h1 : K / (hubble a t₀ ^ 2 * a t₀ ^ 2) < 0 := by unfold omega0 at hKo; linarith
    by_contra hneg; push Not at hneg
    have : 0 ≤ K / (hubble a t₀ ^ 2 * a t₀ ^ 2) := div_nonneg hneg h2.le
    linarith
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  rw [ratio_of_z a t₃ t₀ _ ha3 ha₀ hz₃, es3] at hχ3
  rw [ratio_of_z a t₅ t₀ _ ha5 ha₀ hz₅, es5] at hχ5
  set J3 := ∫ v in √(1 / (2 * √2))..1, gC Ω k v with hJ3
  set J5 := ∫ v in √(1 / (4 * √2))..1, gC Ω k v with hJ5
  set H₀ := hubble a t₀ with hH₀def
  set a₀ := a t₀ with ha₀def
  set r := √(-K) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hL : ∀ t, lumDist K a t₀ t = a₀ * (1 + redshift a t₀ t) * (Real.sinh (r * comoving a t₀ t) / r) := by
    intro t; unfold lumDist transverse; simp only [not_lt.2 hKn.le, hKn, ↓reduceIte]; rfl
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq2 : 0 < √2 := by linarith
  have hs3 : 1 < 2 * √2 := by linarith
  have hs5 : 1 < 4 * √2 := by linarith
  obtain ⟨hw3p, hw3⟩ := w_lt_one _ hs3
  obtain ⟨hw5p, hw5⟩ := w_lt_one _ hs5
  have hJ3p : 0 < J3 := JposO hd _ hw3p hw3
  obtain ⟨wb3u, wb3l⟩ := wb (2 * √2) (148651 / 250000) (594603 / 1000000) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb5u, wb5l⟩ := wb (4 * √2) (420449 / 1000000) (13139 / 31250) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  have hJ3u : J3 ≤ ∫ v in (594603 / 1000000 : ℝ)..1, gC Ω k v :=
    J_shiftO hd _ _ (by norm_num) wb3u hw3.le
  have hJ5l : ∫ v in (420449 / 1000000 : ℝ)..1, gC Ω k v ≤ J5 :=
    J_shiftO hd _ _ hw5p wb5l (by norm_num)
  have h35 : J3 ≤ J5 := by
    apply J_shiftO hd _ _ hw5p _ hw3.le
    apply Real.sqrt_le_sqrt
    apply one_div_le_one_div_of_le (by positivity); linarith
  have hR := ratio_all Ω k hd
  have hJr : 27 / 10 * J3 ≤ 2 * J5 := by linarith
  -- the transverse factors
  set c := r / (H₀ * a₀) with hc
  have hc0 : 0 < c := by positivity
  have hx3 : r * comoving a t₀ t₃ = c * J3 := by rw [hχ3, hc]; field_simp
  have hx5 : r * comoving a t₀ t₅ = c * J5 := by rw [hχ5, hc]; field_simp
  have hsr := sinh_ratio (c * J3) (c * J5) (by positivity) (mul_le_mul_of_nonneg_left h35 hc0.le)
  have hsh3 : 0 < Real.sinh (c * J3) := Real.sinh_pos_iff.2 (by positivity)
  have hsinh : 27 / 10 * Real.sinh (c * J3) ≤ 2 * Real.sinh (c * J5) := by
    have h1 : Real.sinh (c * J3) * J5 ≤ Real.sinh (c * J5) * J3 := by
      have := hsr
      have e1 : Real.sinh (c * J3) * (c * J5) = c * (Real.sinh (c * J3) * J5) := by ring
      have e2 : Real.sinh (c * J5) * (c * J3) = c * (Real.sinh (c * J5) * J3) := by ring
      rw [e1, e2] at this
      exact le_of_mul_le_mul_left this hc0
    have h2 : 27 / 10 * Real.sinh (c * J3) * J3 ≤ 2 * Real.sinh (c * J5) * J3 := by
      nlinarith [mul_le_mul_of_nonneg_left hJr hsh3.le]
    exact le_of_mul_le_mul_right h2 hJ3p
  -- the two distances
  have eD3 : lumDist K a t₀ t₃ = a₀ * (2 * √2) * (Real.sinh (c * J3) / r) := by
    rw [hL, hz₃, es3, hx3]
  have eD5 : lumDist K a t₀ t₅ = a₀ * (4 * √2) * (Real.sinh (c * J5) / r) := by
    rw [hL, hz₅, es5, hx5]
  obtain ⟨D3, hD3⟩ : ∃ D, lumDist K a t₀ t₃ = D := ⟨_, rfl⟩
  obtain ⟨D5, hD5⟩ : ∃ D, lumDist K a t₀ t₅ = D := ⟨_, rfl⟩
  rw [hD3] at eD3
  rw [hD5] at eD5
  rw [hD3, hD5]
  have hX0 : 0 < a₀ * √2 / r := by positivity
  have e3 : D3 = (a₀ * √2 / r) * (2 * Real.sinh (c * J3)) := by rw [eD3]; ring
  have e5 : D5 = (a₀ * √2 / r) * (4 * Real.sinh (c * J5)) := by rw [eD5]; ring
  have hD3p : 0 < D3 := by rw [e3]; positivity
  have hDr' : 27 / 10 * D3 ≤ D5 := by
    rw [e3, e5]; exact scale_aux _ _ _ hX0.le hsinh
  have hDr : 27 / 10 ≤ D5 / D3 := by rw [le_div_iff₀ hD3p]; exact hDr'
  have hD5p : 0 < D5 := by linarith
  set Q3 := x₃ + a₂ * x₃ ^ 2 + a₃ * x₃ ^ 3 + a₄ * x₃ ^ 4 with hQ3def
  set Q5 := x₅ + a₂ * x₅ ^ 2 + a₃ * x₅ ^ 3 + a₄ * x₅ ^ 4 with hQ5def
  have hl0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  rw [hz₃, hz₅, lp4_eq a₂ a₃ a₄ H x₃ _ hx₃, lp4_eq a₂ a₃ a₄ H x₅ _ hx₅]
  have hX3 : 0 < D3 / (Real.log 10 / H * Q3) := by positivity
  have hX5 : 0 < D5 / (Real.log 10 / H * Q5) := by positivity
  have e : 5 * Real.logb 10 (D5 / (Real.log 10 / H * Q5))
      - 5 * Real.logb 10 (D3 / (Real.log 10 / H * Q3))
      = 5 * Real.logb 10 ((D5 / (Real.log 10 / H * Q5)) / (D3 / (Real.log 10 / H * Q3))) := by
    rw [Real.logb_div hX5.ne' hX3.ne']; ring
  have key : (D5 / (Real.log 10 / H * Q5)) / (D3 / (Real.log 10 / H * Q3))
      = D5 / D3 * (Q3 / Q5) := by
    field_simp
  rw [e, key]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
  rw [show 27 / 10 * Q3 / Q5 = 27 / 10 * (Q3 / Q5) by ring]
  exact mul_le_mul_of_nonneg_right hDr (by positivity)

open Checked.Cosmography.B1L19CurvedProof in
theorem l19_sq_curved_r8 : dropped% Checked.Cosmography.B1L19Curved.l19_sq_curved 8 := by
  intro Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff hH₀ hK1 hH hz3 hz5 H hHp
  rcases le_or_gt 1 (omega0 K a t₀) with hK0 | hK0
  · exact Checked.Cosmography.B1L19Curved.l19_sq_curved Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff hH₀
      hK0 hK1 hH hz3 hz5 H hHp
  obtain ⟨hL1, hL2⟩ := L_bounds
  obtain ⟨hQ5, hF⟩ := poly_sq _ hL1 hL2
  have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + 3.075 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 4.466 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-3.716) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by linarith
  have hd := delta_open Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff hH₀ hK0 hH hz3 hz5
    3.075 4.466 (-3.716) H hHp _ _ x3_eq x5_eq hQ3 hQ5
  have hq : (1.1225 : ℝ) < 27 / 10 * (3 / 2 * (Real.log 2 / Real.log 10)
      + 3.075 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 4.466 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-3.716) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
      / (5 / 2 * (Real.log 2 / Real.log 10) + 3.075 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 4.466 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-3.716) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4) := by
    rw [lt_div_iff₀ hQ5]; linarith
  have hlg := Real.logb_lt_logb (by norm_num : (1:ℝ) < 10) (by norm_num) hq
  have := logb_11225
  linarith

open Checked.Cosmography.B1L19CurvedProof in
theorem l19_sqg_curved_r8 : dropped% Checked.Cosmography.B1L19Curved.l19_sqg_curved 8 := by
  intro Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff hH₀ hK1 hH hz3 hz5 H hHp
  rcases le_or_gt 1 (omega0 K a t₀) with hK0 | hK0
  · exact Checked.Cosmography.B1L19Curved.l19_sqg_curved Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff hH₀
      hK0 hK1 hH hz3 hz5 H hHp
  obtain ⟨hL1, hL2⟩ := L_bounds
  obtain ⟨hQ5, hF⟩ := poly_sqg _ hL1 hL2
  have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + 3.205 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 3.564 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-2.510) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by linarith
  have hd := delta_open Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hpos hdiff hH₀ hK0 hH hz3 hz5
    3.205 3.564 (-2.510) H hHp _ _ x3_eq x5_eq hQ3 hQ5
  have hq : (1.08 : ℝ) < 27 / 10 * (3 / 2 * (Real.log 2 / Real.log 10)
      + 3.205 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 3.564 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-2.510) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
      / (5 / 2 * (Real.log 2 / Real.log 10) + 3.205 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 3.564 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-2.510) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4) := by
    rw [lt_div_iff₀ hQ5]; linarith
  have hlg := Real.logb_lt_logb (by norm_num : (1:ℝ) < 10) (by norm_num) hq
  have := logb_108
  linarith

end Checked.Trust.NCBV
