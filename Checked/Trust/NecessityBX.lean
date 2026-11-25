import Checked.Trust.NecessityBXCerts
import Checked.Cosmography.B1L19Curved
import Checked.Trust.Necessity
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Hypothesis necessity, the curved quartic pair: the lower density bound (trust track T2b)

Run 2026-11-25T1828Z. `B1L19Curved.l19_sq_curved` and `l19_sqg_curved` assume a matter density of at least one
tenth (hypothesis 1). That hypothesis is NEEDED in both (`l19_sq_curved_h1`, `l19_sqg_curved_h1`), and the
reason is the curvature, not the integrals: a closed model whose radicand nearly vanishes at the farther source
has a long comoving distance to it, and the transverse factor, a sine, is then past its maximum.

* **The witness** is the closed model of matter density one hundred twenty-one ten-thousandths and total density
  eleven tenths (curvature constant one tenth with unit Hubble rate and scale factor today), built with the scale
  factor of `Checked.Trust.NCAS.ma`. Its radicand is positive from the farther source on but small there, so the
  distance integral to the farther source lies between eight and ten, against about two for the nearer one
  (`Checked.Trust.NCBX.bx_U5`, `bx_L5`, `bx_L3`, `bx_U3`: generated step sums, the integrand decreasing).
* **The sine** at the farther source is within six tenths of zero from above (the argument is past the
  right angle and below the half turn), while at the nearer source it is above one half, so the luminosity
  distance ratio is below the ratio of the two quartic values, and the residual at the farther source does not
  exceed the one at the nearer source.
-/

namespace Checked.Trust.NCBX

open Set MeasureTheory Real Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.BambaK Checked.Cosmography.B1
open Checked.Cosmography.B1Fit Checked.Cosmography.B1L19 Checked.Cosmography.Transverse
open Checked.Cosmography.B1L19CurvedTools Checked.Trust.NCAS

/-- Moving the lower limit up decreases the integral. -/
lemma bx_shift {w w' : ℝ} (hw : 13139 / 31250 ≤ w) (hww : w ≤ w') (hw' : w' ≤ 1) :
    ∫ v in w'..1, gC (121 / 10000) (-1 / 10) v ≤ ∫ v in w..1, gC (121 / 10000) (-1 / 10) v := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (bx_int hw hww hw')
    (bx_int (le_trans hw hww) hw' le_rfl)]
  have : 0 ≤ ∫ v in w..w', gC (121 / 10000) (-1 / 10) v :=
    intervalIntegral.integral_nonneg hww (fun v _ => gC_nonneg _ _ v)
  linarith

/-- The arithmetic of the last step: `0 < Q₃ ≤ 0.42 Q₅` and `0.84 s₅ ≤ s₃` with `s₅ > 0` make the residual
at `4√2` at most the one at `2√2`. -/
theorem bx_final (s3 s5 Q3 Q5 l r : ℝ) (hl : 0 < l) (hr : 0 < r) (hQ3 : 0 < Q3)
    (hq : Q3 ≤ 21 / 50 * Q5) (h5p : 0 < s5) (h53 : 21 / 25 * s5 ≤ s3) :
    5 * Real.logb 10 (4 * r * s5 / (l / 1 * Q5)) - 5 * Real.logb 10 (2 * r * s3 / (l / 1 * Q3)) ≤ 0 := by
  have hQ5 : 0 < Q5 := by linarith
  have hs3 : 0 < s3 := by linarith
  have hA : 0 < 4 * r * s5 / (l / 1 * Q5) := by positivity
  have hAB : 4 * r * s5 / (l / 1 * Q5) ≤ 2 * r * s3 / (l / 1 * Q3) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : s5 * Q3 ≤ s5 * (21 / 50 * Q5) := mul_le_mul_of_nonneg_left hq h5p.le
    have h2 : 21 / 25 * s5 * Q5 ≤ s3 * Q5 := mul_le_mul_of_nonneg_right h53 hQ5.le
    have hk : 0 ≤ r * l := by positivity
    have h3' := mul_le_mul_of_nonneg_left h1 hk
    have h4 := mul_le_mul_of_nonneg_left h2 hk
    have e1 : 4 * r * s5 * (l / 1 * Q3) = 4 * (r * l * (s5 * Q3)) := by ring
    have e2 : 2 * r * s3 * (l / 1 * Q5) = 2 * (r * l * (s3 * Q5)) := by ring
    have e3 : r * l * (s5 * (21 / 50 * Q5)) = 1 / 2 * (r * l * (21 / 25 * s5 * Q5)) := by ring
    rw [e1, e2]
    nlinarith
  have := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 10) hA hAB
  linarith

/-- The closed model of matter density `121/10000` and total density `11/10` (`K = 1/10`): every hypothesis of
the curved Lusso et al. 2019 headlines except the lower density bound holds, and the residual at `1 + z = 4√2`
does not exceed the one at `1 + z = 2√2`, for any quartic whose values satisfy `0 < Q₃ ≤ 0.42 Q₅`. -/
theorem bx_core (a₂ a₃ a₄ : ℝ)
    (hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
    (hq : 3 / 2 * (Real.log 2 / Real.log 10) + a₂ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + a₄ * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4
      ≤ 21 / 50 * (5 / 2 * (Real.log 2 / Real.log 10) + a₂ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + a₃ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3 + a₄ * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4)) :
    ∃ a : ℝ → ℝ, ∃ t₅ t₃ t₀ : ℝ, t₅ ≤ t₃ ∧ t₃ ≤ t₀ ∧ (∀ s ∈ Icc t₅ t₀, 0 < a s) ∧
      (∀ s ∈ Icc t₅ t₀, DifferentiableAt ℝ a s) ∧ 0 < hubble a t₀ ∧ omega0 (1 / 10) a t₀ = 11 / 10 ∧
      (∀ s ∈ Icc t₅ t₀, hubble a s = hubble a t₀ * √(121 / 10000 * (1 + redshift a t₀ s) ^ 3
        + (1 - omega0 (1 / 10) a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 (1 / 10) a t₀ - 121 / 10000)) ∧
      redshift a t₀ t₃ = 2 * √2 - 1 ∧ redshift a t₀ t₅ = 4 * √2 - 1 ∧
      5 * Real.logb 10 (lumDist (1 / 10) a t₀ t₅ / logPolyDL4 a₂ a₃ a₄ 1 (redshift a t₀ t₅))
        - 5 * Real.logb 10 (lumDist (1 / 10) a t₀ t₃ / logPolyDL4 a₂ a₃ a₄ 1 (redshift a t₀ t₃)) ≤ 0 := by
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hs3 : (1:ℝ) < 2 * √2 := by linarith
  have hs5 : (1:ℝ) < 4 * √2 := by linarith
  obtain ⟨hw3p, hw3⟩ := w_lt_one _ hs3
  obtain ⟨hw5p, hw5⟩ := w_lt_one _ hs5
  obtain ⟨wb3u, wb3l⟩ := wb (2 * √2) (148651 / 250000) (594603 / 1000000) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb5u, wb5l⟩ := wb (4 * √2) (420449 / 1000000) (13139 / 31250) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  set c := √(1 / (4 * √2)) with hcdef
  set w := √(1 / (2 * √2)) with hwdef
  have hc1 : c ≤ 1 := hw5.le
  have hy : ∀ v ∈ Icc c 1, 0 < yC (121 / 10000) (-1 / 10) v := fun v hv =>
    bx_pos (le_trans wb5u hv.1) hv.2
  have hcw : c ≤ w := by linarith
  have hwm : w ∈ Icc c 1 := ⟨hcw, hw3.le⟩
  have hcm : c ∈ Icc c 1 := ⟨le_rfl, hc1⟩
  set a := ma (121 / 10000) (-1 / 10) c hw5p hc1 hy with hadef
  have hmono := (mtau_strictMono hw5p hc1 hy).monotone
  set T := mtau (121 / 10000) (-1 / 10) c with hTdef
  have hIcc : ∀ s ∈ Icc (T c) (T 1),
      s ∈ Icc (mtau (121 / 10000) (-1 / 10) c c) (mtau (121 / 10000) (-1 / 10) c 1) :=
    fun s hs => hs
  have ha0 : a (T 1) = 1 := by rw [hadef, ma_tau]; norm_num
  have hH0 : hubble a (T 1) = 1 := ma_hubble0 hw5p hc1 hy
  have hom : omega0 (1 / 10) a (T 1) = 11 / 10 := by unfold omega0; rw [hH0, ha0]; norm_num
  have hz : ∀ v ∈ Icc c 1, ∀ r : ℝ, 0 < r → v = √(1 / r) → redshift a (T 1) (T v) = r - 1 := by
    intro v hv r hr hvr
    unfold redshift; rw [ha0, hadef, ma_tau, hvr, Real.sq_sqrt (by positivity)]; field_simp
  have hz3 := hz w hwm (2 * √2) (by positivity) rfl
  have hz5 := hz c hcm (4 * √2) (by positivity) rfl
  refine ⟨a, T c, T w, T 1, hmono hcw, hmono hw3.le, fun s hs => ma_pos hw5p hc1 hy (hIcc s hs),
    fun s hs => (ma_deriv hw5p hc1 hy s).differentiableAt, by rw [hH0]; norm_num, hom, ?_, hz3, hz5, ?_⟩
  · intro s hs
    rw [ma_law hw5p hc1 hy (hIcc s hs), hom]
    congr 2; ring
  -- distances
  set J3 := ∫ v in w..1, gC (121 / 10000) (-1 / 10) v with hJ3
  set J5 := ∫ v in c..1, gC (121 / 10000) (-1 / 10) v with hJ5
  set ρ := √(1 / 10 : ℝ) with hρ
  have hχ3 : comoving a (T 1) (T w) = J3 := ma_comoving hw5p hc1 hy hwm
  have hχ5 : comoving a (T 1) (T c) = J5 := ma_comoving hw5p hc1 hy hcm
  have hK : (0:ℝ) < 1 / 10 := by norm_num
  have hd3 : lumDist (1 / 10) a (T 1) (T w) = 2 * √2 * (Real.sin (ρ * J3) / ρ) := by
    unfold lumDist transverse; rw [ha0, hz3, hχ3]; simp only [hK, ↓reduceIte]; ring
  have hd5 : lumDist (1 / 10) a (T 1) (T c) = 4 * √2 * (Real.sin (ρ * J5) / ρ) := by
    unfold lumDist transverse; rw [ha0, hz5, hχ5]; simp only [hK, ↓reduceIte]; ring
  -- integral bounds
  have hJ5u : J5 ≤ 9641 / 1000 := le_trans (bx_shift le_rfl wb5u hc1) bx_U5
  have hJ5l : 8067 / 1000 ≤ J5 := le_trans bx_L5 (bx_shift wb5u wb5l (by norm_num))
  have hJ3l : 2001 / 1000 ≤ J3 :=
    le_trans bx_L3 (bx_shift (le_trans wb5u hcw) wb3l (by norm_num))
  have hJ3u : J3 ≤ 2683 / 1000 := le_trans (bx_shift (by norm_num) wb3u hw3.le) bx_U3
  -- the square root of one tenth
  have hρl : 31622 / 100000 ≤ ρ := Real.le_sqrt_of_sq_le (by norm_num)
  have hρu : ρ ≤ 31623 / 100000 := by
    rw [hρ, show (31623 / 100000 : ℝ) = √((31623 / 100000) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hρ0 : 0 < ρ := by linarith
  -- the two sines
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d4
  have hx5l : 31622 / 100000 * (8067 / 1000) ≤ ρ * J5 :=
    mul_le_mul hρl hJ5l (by norm_num) hρ0.le
  have hx5u : ρ * J5 ≤ 31623 / 100000 * (9641 / 1000) :=
    mul_le_mul hρu hJ5u (by linarith) (by norm_num)
  have hx3l : 31622 / 100000 * (2001 / 1000) ≤ ρ * J3 :=
    mul_le_mul hρl hJ3l (by norm_num) hρ0.le
  have hx3u : ρ * J3 ≤ 31623 / 100000 * (2683 / 1000) :=
    mul_le_mul hρu hJ3u (by linarith) (by norm_num)
  have hsin5p : 0 < Real.sin (ρ * J5) :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num at hx5l; linarith only [hx5l])
      (by norm_num at hx5u; linarith only [hx5u, hpi1])
  have hsin5u : Real.sin (ρ * J5) ≤ π - ρ * J5 := by
    rw [← Real.sin_pi_sub]; exact Real.sin_le (by norm_num at hx5u; linarith only [hx5u, hpi1])
  have hsin3 : 5565 / 10000 ≤ Real.sin (ρ * J3) := by
    set x := ρ * J3 with hx
    have hc := Real.sin_gt_sub_cube (x := x) (by norm_num at hx3l; linarith only [hx3l])
    have hx0 : 0 ≤ x := by norm_num at hx3l; linarith only [hx3l]
    have hx2 : x ^ 2 ≤ 7225 / 10000 := by
      have h85 : x ≤ 85 / 100 := by norm_num at hx3u; linarith only [hx3u]
      calc x ^ 2 = x * x := sq x
        _ ≤ (85 / 100) * (85 / 100) := mul_le_mul h85 h85 hx0 (by norm_num)
        _ = 7225 / 10000 := by norm_num
    have hx3 : x ^ 3 ≤ 7225 / 10000 * x := by
      rw [show x ^ 3 = x ^ 2 * x by ring]; exact mul_le_mul_of_nonneg_right hx2 hx0
    norm_num at hx3l
    linarith only [hc, hx3, hx3l]
  have h53 : 21 / 25 * (Real.sin (ρ * J5) / ρ) ≤ Real.sin (ρ * J3) / ρ := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hρ0]
    norm_num at hx5l
    linarith only [hx5l, hsin5u, hsin3, hpi2]
  -- the residual difference
  rw [hz3, hz5, lp4_eq a₂ a₃ a₄ 1 _ _ x3_eq, lp4_eq a₂ a₃ a₄ 1 _ _ x5_eq, hd3, hd5]
  exact bx_final _ _ _ _ _ _ (Real.log_pos (by norm_num)) (by positivity) hQ3 hq
    (div_pos hsin5p hρ0) h53

/-- `l19_sq_curved` without `1/10 ≤ Ω`: the closed model of matter density `121/10000` and total density
`11/10`; the residual of the SNe + quasar central fit does not grow between `1 + z = 2√2` and `4√2`. -/
theorem l19_sq_curved_h1 : necessity% Checked.Cosmography.B1L19Curved.l19_sq_curved 1 := by
  obtain ⟨l1, l2⟩ := L_bounds
  obtain ⟨hQ3, hq⟩ := q_sq _ l1 l2
  obtain ⟨a, t₅, t₃, t₀, h53, h30, hp, hd, hH₀, hom, hH, hz3, hz5, hres⟩ := bx_core _ _ _ hQ3 hq
  refine ⟨121 / 10000, 1 / 10, by norm_num, a, t₅, t₃, t₀, h53, h30, hp, hd, hH₀,
    by rw [hom]; norm_num, by rw [hom], hH, hz3, hz5, 1, one_pos, ?_⟩
  rw [not_lt]; linarith

/-- `l19_sqg_curved` without `1/10 ≤ Ω`: the same closed model; the residual of the SNe + GRB + quasar
central fit does not grow between `1 + z = 2√2` and `4√2`. -/
theorem l19_sqg_curved_h1 : necessity% Checked.Cosmography.B1L19Curved.l19_sqg_curved 1 := by
  obtain ⟨l1, l2⟩ := L_bounds
  obtain ⟨hQ3, hq⟩ := q_sqg _ l1 l2
  obtain ⟨a, t₅, t₃, t₀, h53, h30, hp, hd, hH₀, hom, hH, hz3, hz5, hres⟩ := bx_core _ _ _ hQ3 hq
  refine ⟨121 / 10000, 1 / 10, by norm_num, a, t₅, t₃, t₀, h53, h30, hp, hd, hH₀,
    by rw [hom]; norm_num, by rw [hom], hH, hz3, hz5, 1, one_pos, ?_⟩
  rw [not_lt]; linarith

end Checked.Trust.NCBX
