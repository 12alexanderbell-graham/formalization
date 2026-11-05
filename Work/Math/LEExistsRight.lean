import Mathlib
import Checked.Sim.DuffingExists

/-!
# Lane–Emden n = 3: existence on [1/2, 7] from any start with |θ₀| ≤ 1.08, |φ₀| ≤ 0.3

Picard–Lindelöf (Mathlib) for the clamped time-dependent field
f t (θ, φ) = (cl 1 φ, −2 t⁻¹ cl 1 φ − (cl (6/5) θ)³), Lipschitz (constant 9) and bounded (6)
for t ∈ [1/2, 7]. The clamped energy H = Ψ(φ) + U(θ), Ψ v = ∫₀^v cl 1, U x = ∫₀^x (cl (6/5))³,
has derivative −2 t⁻¹ (cl 1 φ)² ≤ 0, so H ≤ H(1/2) = φ₀²/2 + θ₀⁴/4 < 1/2 = Ψ(±1) < U(±6/5);
both clamps stay inactive and the solution solves θ'' + (2/t) θ' + θ³ = 0.
-/

namespace Work.Math.LEExistsRight
open Set Checked.Sim.DuffingExists

/-- Clamped Lane–Emden field. -/
noncomputable def F (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (cl 1 p.2, -(2 * t⁻¹ * cl 1 p.2) - cl (6 / 5) p.1 ^ 3)

theorem cube_diff (u w : ℝ) (hu : |u| ≤ 6 / 5) (hw : |w| ≤ 6 / 5) :
    |u ^ 3 - w ^ 3| ≤ 9 / 2 * |u - w| := by
  have hu' := abs_le.1 hu
  have hw' := abs_le.1 hw
  have hfac : u ^ 3 - w ^ 3 = (u - w) * (u ^ 2 + u * w + w ^ 2) := by ring
  have hc0 : 0 ≤ u ^ 2 + u * w + w ^ 2 := by nlinarith [sq_nonneg (u + w)]
  have hc1 : u ^ 2 + u * w + w ^ 2 ≤ 9 / 2 := by nlinarith [sq_nonneg (u - w)]
  rw [hfac, abs_mul, abs_of_nonneg hc0]
  nlinarith [abs_nonneg (u - w)]

theorem lipF {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 7) : LipschitzWith 9 (F t) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
  have hti : t⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ ht0 (by norm_num)]; linarith [ht.1]
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  simp only [F, Prod.dist_eq, Real.dist_eq]
  change _ ≤ (9 : ℝ) * _
  have hd1 : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
  have hv : |cl 1 p.2 - cl 1 q.2| ≤ |p.2 - q.2| := cl_sub _ _ _
  refine max_le (by nlinarith [abs_nonneg (p.2 - q.2)]) ?_
  have hu := abs_cl_le (by norm_num : (0 : ℝ) ≤ 6 / 5) p.1
  have hw := abs_cl_le (by norm_num : (0 : ℝ) ≤ 6 / 5) q.1
  have hc := cube_diff _ _ hu hw
  have huw : |cl (6 / 5) p.1 - cl (6 / 5) q.1| ≤ |p.1 - q.1| := cl_sub _ _ _
  have hre : -(2 * t⁻¹ * cl 1 p.2) - cl (6 / 5) p.1 ^ 3 -
      (-(2 * t⁻¹ * cl 1 q.2) - cl (6 / 5) q.1 ^ 3) =
      -(2 * t⁻¹ * (cl 1 p.2 - cl 1 q.2)) - (cl (6 / 5) p.1 ^ 3 - cl (6 / 5) q.1 ^ 3) := by ring
  rw [hre]
  have h1 : |2 * t⁻¹ * (cl 1 p.2 - cl 1 q.2)| ≤ 4 * |p.2 - q.2| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * t⁻¹)]
    nlinarith [abs_nonneg (cl 1 p.2 - cl 1 q.2)]
  calc |-(2 * t⁻¹ * (cl 1 p.2 - cl 1 q.2)) - (cl (6 / 5) p.1 ^ 3 - cl (6 / 5) q.1 ^ 3)|
      ≤ |2 * t⁻¹ * (cl 1 p.2 - cl 1 q.2)| + |cl (6 / 5) p.1 ^ 3 - cl (6 / 5) q.1 ^ 3| := by
        have := abs_sub (-(2 * t⁻¹ * (cl 1 p.2 - cl 1 q.2)))
          (cl (6 / 5) p.1 ^ 3 - cl (6 / 5) q.1 ^ 3)
        rwa [abs_neg] at this
    _ ≤ 4 * |p.2 - q.2| + 9 / 2 * |p.1 - q.1| := by nlinarith
    _ ≤ 9 * max |p.1 - q.1| |p.2 - q.2| := by nlinarith [abs_nonneg (p.1 - q.1)]

theorem normF {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 7) (p : ℝ × ℝ) : ‖F t p‖ ≤ 6 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
  have hti : t⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ ht0 (by norm_num)]; linarith [ht.1]
  simp only [F, Prod.norm_def, Real.norm_eq_abs]
  have hv := abs_le.1 (abs_cl_le (by norm_num : (0 : ℝ) ≤ 1) p.2)
  have hu := abs_le.1 (abs_cl_le (by norm_num : (0 : ℝ) ≤ 6 / 5) p.1)
  refine max_le ((abs_cl_le (by norm_num) _).trans (by norm_num)) ?_
  rw [abs_le]
  set v := cl 1 p.2
  set u := cl (6 / 5) p.1
  have hu3a : |u ^ 3| ≤ 216 / 125 := by
    have : |u| ^ 3 ≤ (6 / 5) ^ 3 := pow_le_pow_left₀ (abs_nonneg u) (abs_le.2 hu) 3
    rw [← abs_pow] at this
    linarith [show ((6 : ℝ) / 5) ^ 3 = 216 / 125 by norm_num]
  have hu3 := (abs_le.1 hu3a).2
  have hu3' := (abs_le.1 hu3a).1
  have hvt : |t⁻¹ * v| ≤ 2 := by
    rw [abs_mul, abs_of_pos hti0]
    have : |v| ≤ 1 := abs_le.2 hv
    nlinarith [abs_nonneg v]
  have hvt' := abs_le.1 hvt
  constructor <;> nlinarith

theorem contF (x : ℝ × ℝ) : ContinuousOn (fun t => F t x) (Icc (1 / 2 : ℝ) 7) := by
  unfold F
  refine continuousOn_const.prodMk ?_
  refine ContinuousOn.sub (ContinuousOn.neg ?_) continuousOn_const
  refine ContinuousOn.mul (continuousOn_const.mul ?_) continuousOn_const
  exact continuousOn_id.inv₀ fun t ht => by simp only [id]; linarith [ht.1]

theorem fst_derivW {α : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt α d s t) : HasDerivWithinAt (fun r => (α r).1) d.1 s t := by
  have := h.hasFDerivWithinAt.fst.hasDerivWithinAt
  simpa using this

theorem snd_derivW {α : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt α d s t) : HasDerivWithinAt (fun r => (α r).2) d.2 s t := by
  have := h.hasFDerivWithinAt.snd.hasDerivWithinAt
  simpa using this

/-- Kinetic part of the clamped energy. -/
noncomputable def Ψ (v : ℝ) : ℝ := ∫ s in (0 : ℝ)..v, cl 1 s

/-- Potential part of the clamped energy. -/
noncomputable def U (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, cl (6 / 5) s ^ 3

theorem contU : Continuous fun s => cl (6 / 5) s ^ 3 := (continuous_cl _).pow 3

theorem hasDerivAt_Ψ (v : ℝ) : HasDerivAt Ψ (cl 1 v) v :=
  ((continuous_cl _).integral_hasStrictDerivAt 0 v).hasDerivAt

theorem hasDerivAt_U (x : ℝ) : HasDerivAt U (cl (6 / 5) x ^ 3) x :=
  (contU.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem Ψ_parts : MonotoneOn Ψ (Ici 0) ∧ AntitoneOn Ψ (Iic 0) :=
  mono_parts hasDerivAt_Ψ (fun y hy => cl_nonneg (by norm_num) hy)
    (fun y hy => cl_nonpos (by norm_num) hy)

theorem U_parts : MonotoneOn U (Ici 0) ∧ AntitoneOn U (Iic 0) :=
  mono_parts hasDerivAt_U
    (fun y hy => by have := cl_nonneg (c := 6 / 5) (by norm_num) hy; positivity)
    (fun y hy => by
      have h := cl_nonpos (c := 6 / 5) (by norm_num) hy
      nlinarith [sq_nonneg (cl (6 / 5) y)])

theorem Ψ_zero : Ψ 0 = 0 := by simp [Ψ]
theorem U_zero : U 0 = 0 := by simp [U]

theorem mem_of_uIcc {b c s : ℝ} (hb : |b| ≤ c) (hs : s ∈ uIcc 0 b) : |s| ≤ c := by
  rw [Set.uIcc, Set.mem_Icc] at hs
  rw [abs_le] at hb ⊢
  constructor
  · have := hs.1; rcases le_total 0 b with h | h <;> simp_all <;> linarith
  · have := hs.2; rcases le_total 0 b with h | h <;> simp_all <;> linarith

theorem Ψ_val {b : ℝ} (hb : |b| ≤ 1) : Ψ b = b ^ 2 / 2 := by
  unfold Ψ
  rw [intervalIntegral.integral_congr (g := fun s => s)
    (fun s hs => cl_of_abs_le (mem_of_uIcc hb hs)), integral_id]
  ring

theorem U_val {b : ℝ} (hb : |b| ≤ 6 / 5) : U b = b ^ 4 / 4 := by
  unfold U
  rw [intervalIntegral.integral_congr (g := fun s => s ^ 3) (fun s hs => by
      simp only
      rw [cl_of_abs_le (mem_of_uIcc hb hs)]), integral_pow]
  ring

theorem Ψ_nonneg (v : ℝ) : 0 ≤ Ψ v := by
  rcases le_total 0 v with h | h
  · rw [← Ψ_zero]; exact Ψ_parts.1 (le_refl (0 : ℝ)) h h
  · rw [← Ψ_zero]; exact Ψ_parts.2 h (le_refl (0 : ℝ)) h

theorem U_nonneg (x : ℝ) : 0 ≤ U x := by
  rcases le_total 0 x with h | h
  · rw [← U_zero]; exact U_parts.1 (le_refl (0 : ℝ)) h h
  · rw [← U_zero]; exact U_parts.2 h (le_refl (0 : ℝ)) h

theorem abs_lt_of_Ψ {v : ℝ} (h : Ψ v < 1 / 2) : |v| < 1 := by
  by_contra hc
  push Not at hc
  rcases le_total 0 v with h0 | h0
  · have hv : 1 ≤ v := by rw [abs_of_nonneg h0] at hc; exact hc
    have := Ψ_parts.1 (show (0 : ℝ) ≤ 1 by norm_num) h0 hv
    rw [Ψ_val (by norm_num)] at this; linarith
  · have hv : v ≤ -1 := by rw [abs_of_nonpos h0] at hc; linarith
    have := Ψ_parts.2 h0 (show (-1 : ℝ) ≤ 0 by norm_num) hv
    rw [Ψ_val (by norm_num)] at this; linarith

theorem abs_lt_of_U {x : ℝ} (h : U x < 1 / 2) : |x| < 6 / 5 := by
  by_contra hc
  push Not at hc
  rcases le_total 0 x with h0 | h0
  · have hx : 6 / 5 ≤ x := by rw [abs_of_nonneg h0] at hc; exact hc
    have := U_parts.1 (show (0 : ℝ) ≤ 6 / 5 by norm_num) h0 hx
    rw [U_val (by norm_num)] at this; linarith
  · have hx : x ≤ -(6 / 5) := by rw [abs_of_nonpos h0] at hc; linarith
    have := U_parts.2 h0 (show -(6 / 5 : ℝ) ≤ 0 by norm_num) hx
    rw [U_val (by norm_num)] at this; linarith

theorem start_energy {θ₀ φ₀ : ℝ} (hθ : |θ₀| ≤ 1.08) (hφ : |φ₀| ≤ 0.3) :
    φ₀ ^ 2 / 2 + θ₀ ^ 4 / 4 < 1 / 2 := by
  have h1 : θ₀ ^ 2 ≤ 1.08 ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ 2
  have h2 : φ₀ ^ 2 ≤ 0.3 ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hφ 2
  have h3 : θ₀ ^ 4 ≤ (1.08 ^ 2) ^ 2 := by
    have : θ₀ ^ 4 = (θ₀ ^ 2) ^ 2 := by ring
    rw [this]; exact pow_le_pow_left₀ (sq_nonneg _) h1 2
  norm_num at h1 h2 h3 ⊢
  linarith

theorem exists_right (θ₀ φ₀ : ℝ) (hθ : |θ₀| ≤ 1.08) (hφ : |φ₀| ≤ 0.3) :
    ∃ θ φ : ℝ → ℝ, θ (1/2) = θ₀ ∧ φ (1/2) = φ₀ ∧
      ∀ t ∈ Icc (1/2 : ℝ) 7, HasDerivWithinAt θ (φ t) (Icc (1/2) 7) t ∧
        HasDerivWithinAt φ (-(2 / t * φ t) - θ t ^ 3) (Icc (1/2) 7) t := by
  have hPL : IsPicardLindelof F (tmin := 1 / 2) (tmax := 7)
      ⟨1 / 2, by norm_num, by norm_num⟩ (θ₀, φ₀) 39 0 6 9 :=
    { lipschitzOnWith := fun t ht => (lipF ht).lipschitzOnWith
      continuousOn := fun x _ => contF x
      norm_le := fun t ht p _ => by
        have := normF ht p; exact_mod_cast this
      mul_max_le := by
        simp only [NNReal.coe_ofNat, NNReal.coe_zero, sub_zero]
        norm_num }
  obtain ⟨α, h0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  set H : ℝ → ℝ := fun t => Ψ (α t).2 + U (α t).1 with hH
  have hcont : ContinuousOn H (Icc (1 / 2) 7) := by
    intro t ht
    have hc := (hα t ht).continuousWithinAt
    have h1 : ContinuousWithinAt (fun r => (α r).2) (Icc (1 / 2) 7) t :=
      continuous_snd.continuousAt.comp_continuousWithinAt hc
    have h2 : ContinuousWithinAt (fun r => (α r).1) (Icc (1 / 2) 7) t :=
      continuous_fst.continuousAt.comp_continuousWithinAt hc
    exact ((hasDerivAt_Ψ _).continuousAt.comp_continuousWithinAt h1).add
      ((hasDerivAt_U _).continuousAt.comp_continuousWithinAt h2)
  have hD : ∀ t ∈ Ioo (1 / 2 : ℝ) 7, HasDerivAt H (-(2 * t⁻¹ * cl 1 (α t).2 ^ 2)) t := by
    intro t ht
    have hd : HasDerivAt α (F t (α t)) t :=
      (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hdu := hd.hasDerivWithinAt (s := univ)
    have h1 := (hasDerivAt_Ψ _).comp t
      (hasDerivWithinAt_univ.1 (snd_derivW hdu))
    have h2 := (hasDerivAt_U _).comp t
      (hasDerivWithinAt_univ.1 (fst_derivW hdu))
    convert h1.add h2 using 1
    · rfl
    · simp only [F]; ring
  have hanti : AntitoneOn H (Icc (1 / 2) 7) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont
    · intro t ht; rw [interior_Icc] at ht; exact (hD t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hD t ht).deriv]
      have : 0 < t⁻¹ := inv_pos.2 (by linarith [ht.1])
      nlinarith [sq_nonneg (cl 1 (α t).2)]
  have hH0 : H (1 / 2) < 1 / 2 := by
    simp only [hH, h0]
    rw [Ψ_val (hφ.trans (by norm_num)), U_val (hθ.trans (by norm_num))]
    exact start_energy hθ hφ
  have hin : ∀ t ∈ Icc (1 / 2 : ℝ) 7, |(α t).2| < 1 ∧ |(α t).1| < 6 / 5 := by
    intro t ht
    have h := hanti ⟨le_refl _, by norm_num⟩ ht ht.1
    simp only [hH] at h hH0
    exact ⟨abs_lt_of_Ψ (by linarith [U_nonneg (α t).1]),
      abs_lt_of_U (by linarith [Ψ_nonneg (α t).2])⟩
  refine ⟨fun t => (α t).1, fun t => (α t).2, by show (α (1 / 2)).1 = θ₀; rw [h0],
    by show (α (1 / 2)).2 = φ₀; rw [h0], fun t ht => ⟨?_, ?_⟩⟩
  · have := fst_derivW (hα t ht)
    simp only [F] at this
    rwa [cl_of_abs_le (hin t ht).1.le] at this
  · have := snd_derivW (hα t ht)
    simp only [F] at this
    rw [cl_of_abs_le (hin t ht).1.le, cl_of_abs_le (hin t ht).2.le] at this
    convert this using 1
    simp only [div_eq_mul_inv]

end Work.Math.LEExistsRight

#print axioms Work.Math.LEExistsRight.exists_right
