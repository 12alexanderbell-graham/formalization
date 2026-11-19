import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Sim.DuffingExists
import Checked.Math.LEExistsRight
import Work.Math.LE52Cell

/-!
# Lane–Emden index five halves: existence away from the centre, from any start in a box

Picard–Lindelöf (Mathlib) for the clamped time-dependent field
(θ, φ) ↦ (cl₂ φ, −2 t⁻¹ cl₂ φ − g52 (cl₁₆ θ)) on [1/2, 6] (the index-three construction
`Checked.Math.LEExistsRight` with the power five halves). The clamped energy Ψ(φ) + U(θ)
(U ≥ 0: g52 vanishes for a negative argument) has derivative −2 t⁻¹ (cl₂ φ)² ≤ 0, so Ψ(φ) stays
below 2 and |φ| < 2; then |θ'| ≤ 2 keeps |θ| below 1.08 + 11 < 16. Both clamps stay inactive and
the solution solves θ'' + (2/t) θ' + θ ^ (5/2) = 0 in the form √θ ^ 5 (`Work.Math.LE52Cell.g52`).
Run 2026-11-19T1628Z (from the index three halves module of run 2026-11-19T1028Z).
-/

namespace Work.Math.LE52ExistsRight
open Set Checked.Sim.DuffingExists Work.Math.LE52Cell

/-- Clamped Lane–Emden field of index five halves. -/
noncomputable def F (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (cl 2 p.2, -(2 * t⁻¹ * cl 2 p.2) - g52 (cl 16 p.1))

theorem lipF {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 6) : LipschitzWith 164 (F t) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
  have hti : t⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ ht0 (by norm_num)]; linarith [ht.1]
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  simp only [F, Prod.dist_eq, Real.dist_eq]
  change _ ≤ (164 : ℝ) * _
  have hd1 : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
  have hv : |cl 2 p.2 - cl 2 q.2| ≤ |p.2 - q.2| := cl_sub _ _ _
  refine max_le (by nlinarith [abs_nonneg (p.2 - q.2)]) ?_
  have hc := g52_lip (TH := 16) (S := 4) (abs_cl_le (by norm_num) p.1) (abs_cl_le (by norm_num) q.1)
    (by norm_num) (by norm_num)
  have huw : |cl 16 p.1 - cl 16 q.1| ≤ |p.1 - q.1| := cl_sub _ _ _
  have hre : -(2 * t⁻¹ * cl 2 p.2) - g52 (cl 16 p.1) - (-(2 * t⁻¹ * cl 2 q.2) - g52 (cl 16 q.1)) =
      -(2 * t⁻¹ * (cl 2 p.2 - cl 2 q.2)) - (g52 (cl 16 p.1) - g52 (cl 16 q.1)) := by ring
  rw [hre]
  have h1 : |2 * t⁻¹ * (cl 2 p.2 - cl 2 q.2)| ≤ 4 * |p.2 - q.2| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * t⁻¹)]
    nlinarith [abs_nonneg (cl 2 p.2 - cl 2 q.2)]
  calc |-(2 * t⁻¹ * (cl 2 p.2 - cl 2 q.2)) - (g52 (cl 16 p.1) - g52 (cl 16 q.1))|
      ≤ |2 * t⁻¹ * (cl 2 p.2 - cl 2 q.2)| + |g52 (cl 16 p.1) - g52 (cl 16 q.1)| := by
        have := abs_sub (-(2 * t⁻¹ * (cl 2 p.2 - cl 2 q.2))) (g52 (cl 16 p.1) - g52 (cl 16 q.1))
        rwa [abs_neg] at this
    _ ≤ 4 * |p.2 - q.2| + 160 * |p.1 - q.1| := by nlinarith
    _ ≤ 164 * max |p.1 - q.1| |p.2 - q.2| := by nlinarith [abs_nonneg (p.1 - q.1)]

theorem g52_cl16_le (y : ℝ) : g52 (cl 16 y) ≤ 1024 := by
  have hs := sqrt_le_of (S := 4) (abs_cl_le (by norm_num : (0 : ℝ) ≤ 16) y) (by norm_num)
    (by norm_num)
  unfold g52
  calc Real.sqrt (cl 16 y) ^ 5 ≤ 4 ^ 5 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 5
    _ = 1024 := by norm_num

theorem normF {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 6) (p : ℝ × ℝ) : ‖F t p‖ ≤ 1032 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
  have hti : t⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ ht0 (by norm_num)]; linarith [ht.1]
  simp only [F, Prod.norm_def, Real.norm_eq_abs]
  have hv := abs_le.1 (abs_cl_le (by norm_num : (0 : ℝ) ≤ 2) p.2)
  refine max_le ((abs_cl_le (by norm_num) _).trans (by norm_num)) ?_
  rw [abs_le]
  set v := cl 2 p.2
  have hg0 := g52_nonneg (cl 16 p.1)
  have hg1 := g52_cl16_le p.1
  have hvt : |t⁻¹ * v| ≤ 4 := by
    rw [abs_mul, abs_of_pos hti0]
    have : |v| ≤ 2 := abs_le.2 hv
    nlinarith [abs_nonneg v]
  have hvt' := abs_le.1 hvt
  constructor <;> nlinarith

theorem contF (x : ℝ × ℝ) : ContinuousOn (fun t => F t x) (Icc (1 / 2 : ℝ) 6) := by
  unfold F
  refine continuousOn_const.prodMk ?_
  refine ContinuousOn.sub (ContinuousOn.neg ?_) continuousOn_const
  refine ContinuousOn.mul (continuousOn_const.mul ?_) continuousOn_const
  exact continuousOn_id.inv₀ fun t ht => by simp only [id]; linarith [ht.1]

/-- Kinetic part of the clamped energy. -/
noncomputable def Ψ (v : ℝ) : ℝ := ∫ s in (0 : ℝ)..v, cl 2 s

/-- Potential part of the clamped energy. -/
noncomputable def U (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, g52 (cl 16 s)

theorem contU : Continuous fun s => g52 (cl 16 s) :=
  (Real.continuous_sqrt.comp (continuous_cl _)).pow 5

theorem hasDerivAt_Ψ (v : ℝ) : HasDerivAt Ψ (cl 2 v) v :=
  ((continuous_cl _).integral_hasStrictDerivAt 0 v).hasDerivAt

theorem hasDerivAt_U (x : ℝ) : HasDerivAt U (g52 (cl 16 x)) x :=
  (contU.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem Ψ_parts : MonotoneOn Ψ (Ici 0) ∧ AntitoneOn Ψ (Iic 0) :=
  mono_parts hasDerivAt_Ψ (fun y hy => cl_nonneg (by norm_num) hy)
    (fun y hy => cl_nonpos (by norm_num) hy)

theorem U_parts : MonotoneOn U (Ici 0) ∧ AntitoneOn U (Iic 0) :=
  mono_parts hasDerivAt_U (fun y _ => g52_nonneg _)
    (fun y hy => by
      have h := cl_nonpos (c := 16) (by norm_num) hy
      unfold g52
      rw [Real.sqrt_eq_zero'.2 h]; norm_num)

theorem Ψ_zero : Ψ 0 = 0 := by simp [Ψ]
theorem U_zero : U 0 = 0 := by simp [U]

theorem Ψ_val {b : ℝ} (hb : |b| ≤ 2) : Ψ b = b ^ 2 / 2 := by
  unfold Ψ
  rw [intervalIntegral.integral_congr (g := fun s => s)
    (fun s hs => cl_of_abs_le (Checked.Math.LEExistsRight.mem_of_uIcc hb hs)), integral_id]
  ring

theorem Ψ_nonneg (v : ℝ) : 0 ≤ Ψ v := by
  rcases le_total 0 v with h | h
  · rw [← Ψ_zero]; exact Ψ_parts.1 (le_refl (0 : ℝ)) h h
  · rw [← Ψ_zero]; exact Ψ_parts.2 h (le_refl (0 : ℝ)) h

theorem U_nonneg (x : ℝ) : 0 ≤ U x := by
  rcases le_total 0 x with h | h
  · rw [← U_zero]; exact U_parts.1 (le_refl (0 : ℝ)) h h
  · rw [← U_zero]; exact U_parts.2 h (le_refl (0 : ℝ)) h

theorem abs_lt_of_Ψ {v : ℝ} (h : Ψ v < 2) : |v| < 2 := by
  by_contra hc
  push Not at hc
  rcases le_total 0 v with h0 | h0
  · have hv : 2 ≤ v := by rw [abs_of_nonneg h0] at hc; exact hc
    have := Ψ_parts.1 (show (0 : ℝ) ≤ 2 by norm_num) h0 hv
    rw [Ψ_val (by norm_num)] at this; linarith
  · have hv : v ≤ -2 := by rw [abs_of_nonpos h0] at hc; linarith
    have := Ψ_parts.2 h0 (show (-2 : ℝ) ≤ 0 by norm_num) hv
    rw [Ψ_val (by norm_num)] at this; linarith

/-- U at a start with |θ₀| ≤ 1.08: the integrand is at most (26/25)⁵ there. -/
theorem U_start {b : ℝ} (hb : |b| ≤ 1.08) : U b ≤ 1.08 * (26 / 25) ^ 5 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := b)
    (f := fun s => g52 (cl 16 s)) (C := (26 / 25) ^ 5) (fun s hs => by
      have hs' : |s| ≤ 1.08 := by
        rcases le_total 0 b with h0 | h0
        · rw [uIoc_of_le h0] at hs; rw [abs_le]; rw [abs_le] at hb
          constructor <;> linarith [hs.1, hs.2]
        · rw [uIoc_of_ge h0] at hs; rw [abs_le]; rw [abs_le] at hb
          constructor <;> linarith [hs.1, hs.2]
      have hcl : cl 16 s = s := cl_of_abs_le (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (g52_nonneg _), hcl]
      have hq := sqrt_le_of (S := 26 / 25) hs' (by norm_num) (by norm_num)
      unfold g52
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hq 5)
  have hU : U b ≤ ‖U b‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
  unfold U at hU ⊢
  have hb' : |b - 0| ≤ 1.08 := by rw [sub_zero]; exact hb
  calc _ ≤ _ := hU
    _ ≤ (26 / 25) ^ 5 * |b - 0| := h
    _ ≤ (26 / 25) ^ 5 * 1.08 := mul_le_mul_of_nonneg_left hb' (by norm_num)
    _ = 1.08 * (26 / 25) ^ 5 := by ring

theorem exists_right (θ₀ φ₀ : ℝ) (hθ : |θ₀| ≤ 1.08) (hφ : |φ₀| ≤ 0.3) :
    ∃ θ φ : ℝ → ℝ, θ (1/2) = θ₀ ∧ φ (1/2) = φ₀ ∧
      ∀ t ∈ Icc (1/2 : ℝ) 6, HasDerivWithinAt θ (φ t) (Icc (1/2) 6) t ∧
        HasDerivWithinAt φ (-(2 / t * φ t) - g52 (θ t)) (Icc (1/2) 6) t := by
  have hPL : IsPicardLindelof F (tmin := 1 / 2) (tmax := 6)
      ⟨1 / 2, by norm_num, by norm_num⟩ (θ₀, φ₀) 5676 0 1032 164 :=
    { lipschitzOnWith := fun t ht => (lipF ht).lipschitzOnWith
      continuousOn := fun x _ => contF x
      norm_le := fun t ht p _ => by
        have := normF ht p; exact_mod_cast this
      mul_max_le := by
        simp only [NNReal.coe_ofNat, NNReal.coe_zero, sub_zero]
        norm_num }
  obtain ⟨α, h0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  set H : ℝ → ℝ := fun t => Ψ (α t).2 + U (α t).1 with hH
  have hcont : ContinuousOn H (Icc (1 / 2) 6) := by
    intro t ht
    have hc := (hα t ht).continuousWithinAt
    have h1 : ContinuousWithinAt (fun r => (α r).2) (Icc (1 / 2) 6) t :=
      continuous_snd.continuousAt.comp_continuousWithinAt hc
    have h2 : ContinuousWithinAt (fun r => (α r).1) (Icc (1 / 2) 6) t :=
      continuous_fst.continuousAt.comp_continuousWithinAt hc
    exact ((hasDerivAt_Ψ _).continuousAt.comp_continuousWithinAt h1).add
      ((hasDerivAt_U _).continuousAt.comp_continuousWithinAt h2)
  have hD : ∀ t ∈ Ioo (1 / 2 : ℝ) 6, HasDerivAt H (-(2 * t⁻¹ * cl 2 (α t).2 ^ 2)) t := by
    intro t ht
    have hd : HasDerivAt α (F t (α t)) t :=
      (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hdu := hd.hasDerivWithinAt (s := univ)
    have h1 := (hasDerivAt_Ψ _).comp t
      (hasDerivWithinAt_univ.1 (Checked.Math.LEExistsRight.snd_derivW hdu))
    have h2 := (hasDerivAt_U _).comp t
      (hasDerivWithinAt_univ.1 (Checked.Math.LEExistsRight.fst_derivW hdu))
    convert h1.add h2 using 1
    · rfl
    · simp only [F]; ring
  have hanti : AntitoneOn H (Icc (1 / 2) 6) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont
    · intro t ht; rw [interior_Icc] at ht; exact (hD t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hD t ht).deriv]
      have : 0 < t⁻¹ := inv_pos.2 (by linarith [ht.1])
      nlinarith [sq_nonneg (cl 2 (α t).2)]
  have hH0 : H (1 / 2) < 2 := by
    simp only [hH, h0]
    rw [Ψ_val (hφ.trans (by norm_num))]
    have hU := U_start hθ
    have h2 : φ₀ ^ 2 ≤ 0.3 ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hφ 2
    norm_num at hU h2 ⊢
    linarith
  have hφin : ∀ t ∈ Icc (1 / 2 : ℝ) 6, |(α t).2| < 2 := by
    intro t ht
    have h := hanti ⟨le_refl _, by norm_num⟩ ht ht.1
    simp only [hH] at h hH0
    exact abs_lt_of_Ψ (by linarith [U_nonneg (α t).1])
  have hθin : ∀ t ∈ Icc (1 / 2 : ℝ) 6, |(α t).1| < 16 := by
    intro t ht
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r => (α r).1) (f' := fun r => cl 2 (α r).2) (C := 2) (s := Icc (1 / 2) 6)
      (fun r hr => by
        have := Checked.Math.LEExistsRight.fst_derivW (hα r hr)
        simpa only [F] using this)
      (fun r _ => by rw [Real.norm_eq_abs]; exact abs_cl_le (by norm_num) _)
      (convex_Icc _ _) ⟨le_refl _, by norm_num⟩ ht
    simp only [Real.norm_eq_abs, h0] at hmv
    rw [abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t - 1 / 2)] at hmv
    have h1 := abs_sub_abs_le_abs_sub (α t).1 θ₀
    norm_num at hθ
    linarith [ht.2]
  refine ⟨fun t => (α t).1, fun t => (α t).2, by show (α (1 / 2)).1 = θ₀; rw [h0],
    by show (α (1 / 2)).2 = φ₀; rw [h0], fun t ht => ⟨?_, ?_⟩⟩
  · have := Checked.Math.LEExistsRight.fst_derivW (hα t ht)
    simp only [F] at this
    rwa [cl_of_abs_le (hφin t ht).le] at this
  · have := Checked.Math.LEExistsRight.snd_derivW (hα t ht)
    simp only [F] at this
    rw [cl_of_abs_le (hφin t ht).le, cl_of_abs_le (hθin t ht).le] at this
    convert this using 1
    simp only [div_eq_mul_inv]

end Work.Math.LE52ExistsRight
