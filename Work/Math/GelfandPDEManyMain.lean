import Checked.Math.GelfandExtrema
import Checked.Math.BEGlobalExists
import Checked.Math.GelfandPDEExists

/-! Route of `Work.Math.GelfandPDEMany.gelfand_pde_radial_many`: multiplicity of radial solutions of the
Gelfand problem in the unit ball of three-dimensional space, from the global regular solution
(`Checked.Math.BEGlobalExists.exists_global`) and the turning points of the radial branch
(`Checked.Math.GelfandExtrema.gelfand_extrema`) by the intermediate value theorem. The construction of a
radial solution from a radius is the one in the proof of `gelfand_pde_radial_exists`. -/

namespace Work.Math.GelfandPDEManyMain
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- A radius s with s² e^{W(s)} = λ gives the radial solution u(x) = W(s‖x‖) + log(s²/λ). -/
theorem radial_of_radius (S : ℝ) (hS : 0 < S) (W Φ : ℝ → ℝ)
    (hw : ∀ t ∈ Icc (0 : ℝ) S, HasDerivWithinAt W (Φ t) (Icc 0 S) t)
    (hφ0 : ContinuousWithinAt Φ (Icc 0 S) 0)
    (hφ : ∀ t ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt Φ (-(2 / t * Φ t) - Real.exp (W t)) (Icc 0 S) t)
    (h0 : W 0 = 0) (s lam : ℝ) (hs0 : 0 < s) (hsS : s < S) (hpos : 0 < lam)
    (hsl : s ^ 2 * Real.exp (W s) = lam) :
    ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
      u = (fun x => W (s * ‖x‖) + Real.log (s ^ 2 / lam)) ∧
      ContDiffOn ℝ 2 u (ball 0 1) ∧
      ContinuousOn u (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) := by
  obtain ⟨hφb, hwb, hDb⟩ := Checked.Math.GProfile.profile_bounds S hS W Φ hw hφ0 hφ h0
  have cW : ContinuousOn W (Icc 0 S) := fun t ht => (hw t ht).continuousWithinAt
  set c : ℝ := Real.log (s ^ 2 / lam) with hc
  have hec : Real.exp c = s ^ 2 / lam := Real.exp_log (by positivity)
  set F : ℝ → ℝ := fun ρ => W (s * ρ) + c with hF
  set F1 : ℝ → ℝ := fun ρ => s * Φ (s * ρ) with hF1d
  set F2 : ℝ → ℝ := fun ρ => s ^ 2 * (-(2 / (s * ρ) * Φ (s * ρ)) - Real.exp (W (s * ρ)))
    with hF2d
  set R : ℝ := S / s with hRd
  have hR1 : 1 < R := (one_lt_div hs0).2 hsS
  have hR0 : 0 < R := by linarith
  have mem : ∀ ρ ∈ Ioo 0 R, s * ρ ∈ Ioo 0 S := fun ρ hρ =>
    ⟨mul_pos hs0 hρ.1, by have := hρ.2; rw [hRd, lt_div_iff₀ hs0] at this; linarith⟩
  have memc : ∀ ρ ∈ Icc 0 R, s * ρ ∈ Icc 0 S := fun ρ hρ =>
    ⟨mul_nonneg hs0.le hρ.1, by have := hρ.2; rw [hRd, le_div_iff₀ hs0] at this; linarith⟩
  have dW : ∀ t ∈ Ioo 0 S, HasDerivAt W (Φ t) t := fun t ht =>
    (hw t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have dΦ : ∀ t ∈ Ioo 0 S, HasDerivAt Φ (-(2 / t * Φ t) - Real.exp (W t)) t := fun t ht =>
    (hφ t ⟨ht.1, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hF1 : ∀ ρ ∈ Ioo 0 R, HasDerivAt F (F1 ρ) ρ := by
    intro ρ hρ
    have h := ((dW _ (mem ρ hρ)).comp ρ ((hasDerivAt_id ρ).const_mul s)).add_const c
    convert h using 1
    all_goals first | rfl | (simp only [hF1d, Function.comp_def, id]; ring)
  have hF2 : ∀ ρ ∈ Ioo 0 R, HasDerivAt F1 (F2 ρ) ρ := by
    intro ρ hρ
    have h := ((dΦ _ (mem ρ hρ)).comp ρ ((hasDerivAt_id ρ).const_mul s)).const_mul s
    convert h using 1
    all_goals first | rfl | (simp only [hF2d, Function.comp_def, id]; ring)
  have cΦ : ∀ t ∈ Ioo 0 S, ContinuousAt Φ t := fun t ht => (dΦ t ht).continuousAt
  have hF2c : ContinuousOn F2 (Ioo 0 R) := by
    intro ρ hρ
    have hm := mem ρ hρ
    have ct : ContinuousAt (fun ρ : ℝ => s * ρ) ρ := (continuous_const.mul continuous_id).continuousAt
    have c1 : ContinuousAt (fun ρ => Φ (s * ρ)) ρ := (cΦ _ hm).comp ct
    have c2 : ContinuousAt (fun ρ => W (s * ρ)) ρ := (dW _ hm).continuousAt.comp ct
    exact (continuousAt_const.mul (((continuousAt_const.div ct hm.1.ne').mul c1).neg.sub
      c2.rexp)).continuousWithinAt
  -- bounds at the centre
  set L : ℝ := -(s ^ 2 / 3) with hL
  set C : ℝ := s ^ 4 * R + s ^ 2 with hC
  have key : ∀ t ∈ Ioo 0 S, |Φ t / t + 1 / 3| ≤ t ^ 2 ∧
      |3 * (Φ t / t) + Real.exp (W t)| ≤ t ^ 2 / 15 := by
    intro t ht
    have htc : t ∈ Icc 0 S := ⟨ht.1.le, ht.2.le⟩
    have hA := hDb t htc
    have hwl := (hwb t htc).1
    have hwu := (hwb t htc).2
    have he1 : Real.exp (W t) ≤ 1 := Real.exp_le_one_iff.2 hwu
    have he2 : 1 + W t ≤ Real.exp (W t) := by linarith [Real.add_one_le_exp (W t)]
    have ht0 : 0 < t := ht.1
    have ht3 : 0 < t ^ 3 := by positivity
    have eA : 3 * (Φ t / t) + Real.exp (W t) =
        (3 * (t ^ 2 * Φ t) + t ^ 3 * Real.exp (W t)) / t ^ 3 := by
      field_simp
    have b2 : |3 * (Φ t / t) + Real.exp (W t)| ≤ t ^ 2 / 15 := by
      rw [eA, abs_div, abs_of_pos ht3, div_le_iff₀ ht3]
      calc _ ≤ t ^ 5 / 15 := hA
        _ = t ^ 2 / 15 * t ^ 3 := by ring
    refine ⟨?_, b2⟩
    have e1 : Φ t / t + 1 / 3 = (3 * (Φ t / t) + Real.exp (W t)) / 3 +
        (1 - Real.exp (W t)) / 3 := by ring
    rw [e1]
    have b3 : |(1 - Real.exp (W t)) / 3| ≤ t ^ 2 / 18 := by
      rw [abs_div, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - Real.exp (W t))]
      norm_num <;> linarith
    have b4 : |(3 * (Φ t / t) + Real.exp (W t)) / 3| ≤ t ^ 2 / 45 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3), div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
      linarith [b2]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ t ^ 2 / 45 + t ^ 2 / 18 := add_le_add b4 b3
      _ ≤ t ^ 2 := by nlinarith [sq_nonneg t]
  have hs4 : 0 ≤ s ^ 4 * R := by positivity
  have hM : ∀ ρ ∈ Ioo 0 R, |F1 ρ / ρ - L| ≤ C * ρ := by
    intro ρ hρ
    have hm := mem ρ hρ
    have k := (key _ hm).1
    have hρ0 : 0 < ρ := hρ.1
    have e : F1 ρ / ρ - L = s ^ 2 * (Φ (s * ρ) / (s * ρ) + 1 / 3) := by
      simp only [hF1d, hL]; field_simp; ring
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    calc s ^ 2 * |Φ (s * ρ) / (s * ρ) + 1 / 3| ≤ s ^ 2 * (s * ρ) ^ 2 :=
          mul_le_mul_of_nonneg_left k (by positivity)
      _ = s ^ 4 * ρ * ρ := by ring
      _ ≤ s ^ 4 * R * ρ := by
          apply mul_le_mul_of_nonneg_right _ hρ0.le
          exact mul_le_mul_of_nonneg_left hρ.2.le (by positivity)
      _ ≤ C * ρ := by
          apply mul_le_mul_of_nonneg_right _ hρ0.le
          simp only [hC]; nlinarith [sq_nonneg s]
  have hK : ∀ ρ ∈ Ioo 0 R, |F2 ρ - F1 ρ / ρ| ≤ C * ρ := by
    intro ρ hρ
    have hm := mem ρ hρ
    have k := (key _ hm).2
    have hρ0 : 0 < ρ := hρ.1
    have e : F2 ρ - F1 ρ / ρ = -(s ^ 2 * (3 * (Φ (s * ρ) / (s * ρ)) + Real.exp (W (s * ρ)))) := by
      simp only [hF1d, hF2d]; field_simp; ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg (by positivity)]
    calc s ^ 2 * |3 * (Φ (s * ρ) / (s * ρ)) + Real.exp (W (s * ρ))| ≤ s ^ 2 * ((s * ρ) ^ 2 / 15) :=
          mul_le_mul_of_nonneg_left k (by positivity)
      _ ≤ s ^ 4 * ρ * ρ := by nlinarith [sq_nonneg (s * ρ), sq_nonneg s, sq_nonneg ρ]
      _ ≤ s ^ 4 * R * ρ := by
          apply mul_le_mul_of_nonneg_right _ hρ0.le
          exact mul_le_mul_of_nonneg_left hρ.2.le (by positivity)
      _ ≤ C * ρ := by
          apply mul_le_mul_of_nonneg_right _ hρ0.le
          simp only [hC]; nlinarith [sq_nonneg s]
  have hquad : ∀ ρ ∈ Ico 0 R, |F ρ - F 0| ≤ C * ρ ^ 2 := by
    intro ρ hρ
    have hm := memc ρ ⟨hρ.1, hρ.2.le⟩
    have b := hwb _ hm
    have e : F ρ - F 0 = W (s * ρ) := by simp [hF, h0]
    rw [e, abs_of_nonpos b.2]
    have : -W (s * ρ) ≤ s ^ 2 * ρ ^ 2 / 6 := by have := b.1; nlinarith
    calc -W (s * ρ) ≤ s ^ 2 * ρ ^ 2 / 6 := this
      _ ≤ C * ρ ^ 2 := by
          simp only [hC]; nlinarith [sq_nonneg ρ, sq_nonneg s, mul_nonneg hs4 (sq_nonneg ρ)]
  -- the solution
  refine ⟨fun x => F ‖x‖, rfl, ?_, ?_, ?_, ⟨F, fun x _ => rfl⟩, ?_⟩
  · intro x hx
    rw [mem_ball_zero_iff] at hx
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases hx0 : x = 0
    · subst hx0
      exact Checked.Math.RadialC2.contDiffAt_zero_radial hR0 hF1 hF2 hF2c hM hK hquad
    · have hr : ‖x‖ ∈ Ioo 0 R := ⟨norm_pos_iff.2 hx0, by linarith⟩
      have hFc : ContDiffOn ℝ 2 F (Ioo 0 R) := Checked.Math.GelfandPDEExists.contDiffOn_two_of_derivs isOpen_Ioo hF1 hF2 hF2c
      exact (hFc.contDiffAt (isOpen_Ioo.mem_nhds hr)).comp x (contDiffAt_norm ℝ hx0)
  · have cF : ContinuousOn F (Icc 0 1) := by
      have : ContinuousOn (fun ρ => W (s * ρ)) (Icc 0 1) :=
        cW.comp (continuous_const.mul continuous_id).continuousOn
          (fun ρ hρ => memc ρ ⟨hρ.1, hρ.2.trans hR1.le⟩)
      exact this.add continuousOn_const
    exact cF.comp continuous_norm.continuousOn (fun x hx =>
      ⟨norm_nonneg x, mem_closedBall_zero_iff.1 hx⟩)
  · intro x hx
    simp only [hF, hx, mul_one]
    rw [← Real.exp_eq_one_iff, Real.exp_add, hec]
    field_simp
    linarith [hsl]
  · intro x hx
    rw [mem_ball_zero_iff] at hx
    by_cases hx0 : x = 0
    · subst hx0
      rw [Checked.Math.RadialC2.laplacian_radial_zero hR0 hF1 hF2 hM hquad, finrank_euclideanSpace_fin]
      simp only [norm_zero, hF, mul_zero, h0, zero_add, hec, hL]
      field_simp
      norm_num
    · have hr : ‖x‖ ∈ Ioo 0 R := ⟨norm_pos_iff.2 hx0, by linarith⟩
      have hL' := Checked.Math.RadialLaplacian.laplacian_radial (f := F) (f' := F1)
        (f'' := F2 ‖x‖) hx0
        (by filter_upwards [isOpen_Ioo.mem_nhds hr] with ρ hρ using hF1 ρ hρ)
        (hF2 _ hr)
      rw [hL', finrank_euclideanSpace_fin]
      have hr0 : 0 < ‖x‖ := hr.1
      simp only [hF, hF1d, hF2d, Real.exp_add, hec]
      field_simp
      ring

/-- The global form: for the global regular solution, any radius s > 0 with s² e^{W(s)} = λ > 0. -/
theorem radial_global (W Φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt W (Φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt Φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt Φ (-(2 / s * Φ s) - Real.exp (W s)) (Ici 0) s)
    (h0 : W 0 = 0) (s lam : ℝ) (hs0 : 0 < s) (hpos : 0 < lam)
    (hsl : s ^ 2 * Real.exp (W s) = lam) :
      ContDiffOn ℝ 2 (fun x : EuclideanSpace ℝ (Fin 3) => W (s * ‖x‖) + Real.log (s ^ 2 / lam))
        (ball 0 1) ∧
      ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) => W (s * ‖x‖) + Real.log (s ^ 2 / lam))
        (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → W (s * ‖x‖) + Real.log (s ^ 2 / lam) = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
        W (s * ‖x‖) + Real.log (s ^ 2 / lam) = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
        Δ (fun x : EuclideanSpace ℝ (Fin 3) => W (s * ‖x‖) + Real.log (s ^ 2 / lam)) x +
          lam * Real.exp (W (s * ‖x‖) + Real.log (s ^ 2 / lam)) = 0) := by
  have hS : (0 : ℝ) < s + 1 := by linarith
  obtain ⟨u, rfl, h1, h2, h3, h4, h5⟩ := radial_of_radius (s + 1) hS W Φ
    (fun t ht => (hw t ht.1).mono Icc_subset_Ici_self) (hφ0.mono Icc_subset_Ici_self)
    (fun t ht => (hφ t ht.1).mono Icc_subset_Ici_self) h0 s lam hs0 (by linarith) hpos hsl
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Distinct radii give distinct functions (their values at the centre differ). -/
theorem ne_of_radius (W : ℝ → ℝ) (h0 : W 0 = 0) (lam s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hpos : 0 < lam)
    (heq : (fun x : EuclideanSpace ℝ (Fin 3) => W (s * ‖x‖) + Real.log (s ^ 2 / lam)) =
      (fun x : EuclideanSpace ℝ (Fin 3) => W (t * ‖x‖) + Real.log (t ^ 2 / lam))) : s = t := by
  have h := congrFun heq 0
  simp only [norm_zero, mul_zero, h0, zero_add] at h
  have h2 : s ^ 2 / lam = t ^ 2 / lam :=
    Real.log_injOn_pos (by simp only [mem_Ioi]; positivity) (by simp only [mem_Ioi]; positivity) h
  have h3 : s ^ 2 = t ^ 2 := by
    field_simp at h2; linarith
  nlinarith [sq_nonneg (s - t), sq_nonneg (s + t)]

theorem main :
    (∃ u : ℕ → EuclideanSpace ℝ (Fin 3) → ℝ, Function.Injective u ∧ ∀ i : ℕ,
      ContDiffOn ℝ 2 (u i) (ball 0 1) ∧
      ContinuousOn (u i) (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u i x = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u i x = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ (u i) x + 2 * Real.exp (u i x) = 0)) ∧
    (∀ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ lam : ℝ, |lam - 2| < ε →
      ∃ u : Fin N → EuclideanSpace ℝ (Fin 3) → ℝ, Function.Injective u ∧ ∀ i : Fin N,
        ContDiffOn ℝ 2 (u i) (ball 0 1) ∧
        ContinuousOn (u i) (closedBall 0 1) ∧
        (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u i x = 0) ∧
        (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u i x = g ‖x‖) ∧
        (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ (u i) x + lam * Real.exp (u i x) = 0)) ∧
    (∀ lam : ℝ, 2 ≤ lam → lam < 3.321992118 →
      ∃ u v : EuclideanSpace ℝ (Fin 3) → ℝ, u ≠ v ∧
        (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
        (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lam * Real.exp (v x) = 0))) := by
  obtain ⟨W, Φ, hw, hφ0, hφ, h0⟩ := Checked.Math.BEGlobalExists.exists_global
  obtain ⟨ζ, hmono, -, hz0lo, -, hl0lo, -, -, -, -, hband, -, -, -, -⟩ :=
    Checked.Math.GelfandExtrema.gelfand_extrema W Φ hw hφ0 hφ h0
  set Λ : ℝ → ℝ := fun s => s ^ 2 * Real.exp (W s) with hΛ
  have cW : ContinuousOn W (Ici 0) := fun t ht => (hw t ht).continuousWithinAt
  have cΛ : ContinuousOn Λ (Ici 0) := (continuousOn_id.pow 2).mul cW.rexp
  have hz0 : 0 < ζ 0 := by norm_num at hz0lo; linarith
  have hzpos : ∀ k, 0 < ζ k := fun k => lt_of_lt_of_le hz0 (hmono.monotone (Nat.zero_le k))
  -- the solution attached to a radius
  set U : ℝ → ℝ → EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun lam s x => W (s * ‖x‖) + Real.log (s ^ 2 / lam) with hU
  -- IVT on a segment [ζ k, ζ (k+1)]
  have ivt : ∀ k : ℕ, ∀ lam : ℝ,
      ((Λ (ζ k) < lam ∧ lam < Λ (ζ (k + 1))) ∨ (Λ (ζ (k + 1)) < lam ∧ lam < Λ (ζ k))) →
      ∃ s ∈ Ioo (ζ k) (ζ (k + 1)), Λ s = lam := by
    intro k lam h
    have hle : ζ k ≤ ζ (k + 1) := hmono.monotone (Nat.le_succ k)
    have c : ContinuousOn Λ (Icc (ζ k) (ζ (k + 1))) :=
      cΛ.mono (fun t ht => le_trans (hzpos k).le ht.1)
    rcases h with h | h
    · exact intermediate_value_Ioo hle c h
    · exact intermediate_value_Ioo' hle c h
  -- the values at consecutive turning points straddle 2
  have strad : ∀ k : ℕ,
      (2 < Λ (ζ k) ∧ Λ (ζ (k + 1)) < 2) ∨ (Λ (ζ k) < 2 ∧ 2 < Λ (ζ (k + 1))) := by
    intro k
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · exact Or.inl ⟨(hband j).2, (hband j).1⟩
    · right
      refine ⟨(hband j).1, ?_⟩
      have : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
      rw [this]; exact (hband (j + 1)).2
  have hne : ∀ k, 0 < |Λ (ζ k) - 2| := by
    intro k
    rcases strad k with h | h
    · exact abs_pos.2 (by linarith [h.1])
    · exact abs_pos.2 (by linarith [h.1])
  -- a radius on segment k for every λ closer to 2 than both ends
  have seg : ∀ k : ℕ, ∀ lam : ℝ, |lam - 2| < |Λ (ζ k) - 2| → |lam - 2| < |Λ (ζ (k + 1)) - 2| →
      ∃ s ∈ Ioo (ζ k) (ζ (k + 1)), Λ s = lam := by
    intro k lam h1 h2
    apply ivt
    rcases strad k with h | h
    · right
      rw [abs_of_pos (by linarith [h.1] : (0 : ℝ) < Λ (ζ k) - 2)] at h1
      rw [abs_of_neg (by linarith [h.2] : Λ (ζ (k + 1)) - 2 < 0)] at h2
      constructor <;> linarith [le_abs_self (lam - 2), neg_abs_le (lam - 2)]
    · left
      rw [abs_of_neg (by linarith [h.1] : Λ (ζ k) - 2 < 0)] at h1
      rw [abs_of_pos (by linarith [h.2] : (0 : ℝ) < Λ (ζ (k + 1)) - 2)] at h2
      constructor <;> linarith [le_abs_self (lam - 2), neg_abs_le (lam - 2)]
  -- radii on different segments are ordered
  have sep : ∀ a b : ℕ, a < b → ∀ x y : ℝ, x ∈ Ioo (ζ a) (ζ (a + 1)) → y ∈ Ioo (ζ b) (ζ (b + 1)) →
      x < y := fun a b hab x y hx hy =>
    lt_trans hx.2 (lt_of_le_of_lt (hmono.monotone (Nat.succ_le_of_lt hab)) hy.1)
  have solU : ∀ lam s : ℝ, 0 < lam → 0 < s → Λ s = lam →
      ContDiffOn ℝ 2 (U lam s) (ball 0 1) ∧
      ContinuousOn (U lam s) (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → U lam s x = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, U lam s x = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ (U lam s) x + lam * Real.exp (U lam s x) = 0) :=
    fun lam s hl hs hsl => radial_global W Φ hw hφ0 hφ h0 s lam hs hl hsl
  have injU : ∀ lam s t : ℝ, 0 < lam → 0 < s → 0 < t → U lam s = U lam t → s = t :=
    fun lam s t hl hs ht h => ne_of_radius W h0 lam s t hs ht hl h
  refine ⟨?_, ?_, ?_⟩
  · -- (i) λ = 2
    have hk : ∀ k : ℕ, ∃ s ∈ Ioo (ζ k) (ζ (k + 1)), Λ s = 2 := fun k =>
      seg k 2 (by simpa using hne k) (by simpa using hne (k + 1))
    choose σ hσ hσΛ using hk
    refine ⟨fun i => U 2 (σ i), ?_, fun i => solU 2 (σ i) two_pos
      (lt_trans (hzpos i) (hσ i).1) (hσΛ i)⟩
    intro i j hij
    have := injU 2 (σ i) (σ j) two_pos (lt_trans (hzpos i) (hσ i).1)
      (lt_trans (hzpos j) (hσ j).1) hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd this (sep i j h _ _ (hσ i) (hσ j)).ne
    · exact h
    · exact absurd this (sep j i h _ _ (hσ j) (hσ i)).ne'
  · -- (ii) at least N near 2
    intro N
    set δ : ℝ := min 1 ((Finset.range (N + 1)).inf' ⟨0, by simp⟩ (fun k => |Λ (ζ k) - 2|)) with hδ
    have hδpos : 0 < δ := lt_min one_pos ((Finset.lt_inf'_iff _).2 (fun k _ => hne k))
    have hδle : ∀ k ≤ N, δ ≤ |Λ (ζ k) - 2| := fun k hk =>
      (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
    refine ⟨δ, hδpos, fun lam hl => ?_⟩
    have hl1 : |lam - 2| < 1 := lt_of_lt_of_le hl (min_le_left _ _)
    have hlpos : 0 < lam := by linarith [neg_abs_le (lam - 2)]
    have hk : ∀ i : Fin N, ∃ s ∈ Ioo (ζ i) (ζ ((i : ℕ) + 1)), Λ s = lam := fun i =>
      seg i lam (lt_of_lt_of_le hl (hδle i i.2.le)) (lt_of_lt_of_le hl (hδle (i + 1) i.2))
    choose σ hσ hσΛ using hk
    refine ⟨fun i => U lam (σ i), ?_, fun i => solU lam (σ i) hlpos
      (lt_trans (hzpos i) (hσ i).1) (hσΛ i)⟩
    intro i j hij
    have := injU lam (σ i) (σ j) hlpos (lt_trans (hzpos i) (hσ i).1)
      (lt_trans (hzpos j) (hσ j).1) hij
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact absurd this (sep i j h _ _ (hσ i) (hσ j)).ne
    · exact Fin.ext h
    · exact absurd this (sep j i h _ _ (hσ j) (hσ i)).ne'
  · -- (iii) two solutions for 2 ≤ λ < 3.321992118
    intro lam hl2 hlt
    have hlpos : (0 : ℝ) < lam := by linarith
    have hΛ0 : Λ 0 = 0 := by simp [hΛ]
    have hmax : lam < Λ (ζ 0) := by simp only [hΛ]; linarith
    have hmin : Λ (ζ 1) < 2 := (hband 0).1
    have c0 : ContinuousOn Λ (Icc 0 (ζ 0)) := cΛ.mono (fun t ht => ht.1)
    obtain ⟨s1, hs1, hs1Λ⟩ := intermediate_value_Ioo hz0.le c0 (show lam ∈ Ioo (Λ 0) (Λ (ζ 0)) from
      ⟨by rw [hΛ0]; exact hlpos, hmax⟩)
    obtain ⟨s2, hs2, hs2Λ⟩ := ivt 0 lam (Or.inr ⟨by linarith, hmax⟩)
    refine ⟨U lam s1, U lam s2, fun h => ?_, solU lam s1 hlpos hs1.1 hs1Λ,
      solU lam s2 hlpos (lt_trans hz0 hs2.1) hs2Λ⟩
    have := injU lam s1 s2 hlpos hs1.1 (lt_trans hz0 hs2.1) h
    linarith [hs1.2, hs2.1]

/-- Distinct radii give distinct values at the centre. -/
theorem ne_of_centre (W : ℝ → ℝ) (h0 : W 0 = 0) (lam s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hpos : 0 < lam)
    (heq : W (s * ‖(0 : EuclideanSpace ℝ (Fin 3))‖) + Real.log (s ^ 2 / lam) =
      W (t * ‖(0 : EuclideanSpace ℝ (Fin 3))‖) + Real.log (t ^ 2 / lam)) : s = t := by
  simp only [norm_zero, mul_zero, h0, zero_add] at heq
  have h2 : s ^ 2 / lam = t ^ 2 / lam :=
    Real.log_injOn_pos (by simp only [mem_Ioi]; positivity) (by simp only [mem_Ioi]; positivity) heq
  have h3 : s ^ 2 = t ^ 2 := by
    field_simp at h2; linarith
  nlinarith [sq_nonneg (s - t), sq_nonneg (s + t)]

/-- The corrected statement: solutions told apart by their values at the centre. -/
theorem main_centre :
    (∃ u : ℕ → EuclideanSpace ℝ (Fin 3) → ℝ, Function.Injective (fun i => u i 0) ∧ ∀ i : ℕ,
      ContDiffOn ℝ 2 (u i) (ball 0 1) ∧
      ContinuousOn (u i) (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u i x = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u i x = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ (u i) x + 2 * Real.exp (u i x) = 0)) ∧
    (∀ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ lam : ℝ, |lam - 2| < ε →
      ∃ u : Fin N → EuclideanSpace ℝ (Fin 3) → ℝ, Function.Injective (fun i => u i 0) ∧ ∀ i : Fin N,
        ContDiffOn ℝ 2 (u i) (ball 0 1) ∧
        ContinuousOn (u i) (closedBall 0 1) ∧
        (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u i x = 0) ∧
        (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u i x = g ‖x‖) ∧
        (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ (u i) x + lam * Real.exp (u i x) = 0)) ∧
    (∀ lam : ℝ, 2 ≤ lam → lam < 3.321992118 →
      ∃ u v : EuclideanSpace ℝ (Fin 3) → ℝ, u 0 ≠ v 0 ∧
        (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
        (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lam * Real.exp (v x) = 0))) := by
  obtain ⟨W, Φ, hw, hφ0, hφ, h0⟩ := Checked.Math.BEGlobalExists.exists_global
  obtain ⟨ζ, hmono, -, hz0lo, -, hl0lo, -, -, -, -, hband, -, -, -, -⟩ :=
    Checked.Math.GelfandExtrema.gelfand_extrema W Φ hw hφ0 hφ h0
  set Λ : ℝ → ℝ := fun s => s ^ 2 * Real.exp (W s) with hΛ
  have cW : ContinuousOn W (Ici 0) := fun t ht => (hw t ht).continuousWithinAt
  have cΛ : ContinuousOn Λ (Ici 0) := (continuousOn_id.pow 2).mul cW.rexp
  have hz0 : 0 < ζ 0 := by norm_num at hz0lo; linarith
  have hzpos : ∀ k, 0 < ζ k := fun k => lt_of_lt_of_le hz0 (hmono.monotone (Nat.zero_le k))
  -- the solution attached to a radius
  set U : ℝ → ℝ → EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun lam s x => W (s * ‖x‖) + Real.log (s ^ 2 / lam) with hU
  -- IVT on a segment [ζ k, ζ (k+1)]
  have ivt : ∀ k : ℕ, ∀ lam : ℝ,
      ((Λ (ζ k) < lam ∧ lam < Λ (ζ (k + 1))) ∨ (Λ (ζ (k + 1)) < lam ∧ lam < Λ (ζ k))) →
      ∃ s ∈ Ioo (ζ k) (ζ (k + 1)), Λ s = lam := by
    intro k lam h
    have hle : ζ k ≤ ζ (k + 1) := hmono.monotone (Nat.le_succ k)
    have c : ContinuousOn Λ (Icc (ζ k) (ζ (k + 1))) :=
      cΛ.mono (fun t ht => le_trans (hzpos k).le ht.1)
    rcases h with h | h
    · exact intermediate_value_Ioo hle c h
    · exact intermediate_value_Ioo' hle c h
  -- the values at consecutive turning points straddle 2
  have strad : ∀ k : ℕ,
      (2 < Λ (ζ k) ∧ Λ (ζ (k + 1)) < 2) ∨ (Λ (ζ k) < 2 ∧ 2 < Λ (ζ (k + 1))) := by
    intro k
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · exact Or.inl ⟨(hband j).2, (hband j).1⟩
    · right
      refine ⟨(hband j).1, ?_⟩
      have : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
      rw [this]; exact (hband (j + 1)).2
  have hne : ∀ k, 0 < |Λ (ζ k) - 2| := by
    intro k
    rcases strad k with h | h
    · exact abs_pos.2 (by linarith [h.1])
    · exact abs_pos.2 (by linarith [h.1])
  -- a radius on segment k for every λ closer to 2 than both ends
  have seg : ∀ k : ℕ, ∀ lam : ℝ, |lam - 2| < |Λ (ζ k) - 2| → |lam - 2| < |Λ (ζ (k + 1)) - 2| →
      ∃ s ∈ Ioo (ζ k) (ζ (k + 1)), Λ s = lam := by
    intro k lam h1 h2
    apply ivt
    rcases strad k with h | h
    · right
      rw [abs_of_pos (by linarith [h.1] : (0 : ℝ) < Λ (ζ k) - 2)] at h1
      rw [abs_of_neg (by linarith [h.2] : Λ (ζ (k + 1)) - 2 < 0)] at h2
      constructor <;> linarith [le_abs_self (lam - 2), neg_abs_le (lam - 2)]
    · left
      rw [abs_of_neg (by linarith [h.1] : Λ (ζ k) - 2 < 0)] at h1
      rw [abs_of_pos (by linarith [h.2] : (0 : ℝ) < Λ (ζ (k + 1)) - 2)] at h2
      constructor <;> linarith [le_abs_self (lam - 2), neg_abs_le (lam - 2)]
  -- radii on different segments are ordered
  have sep : ∀ a b : ℕ, a < b → ∀ x y : ℝ, x ∈ Ioo (ζ a) (ζ (a + 1)) → y ∈ Ioo (ζ b) (ζ (b + 1)) →
      x < y := fun a b hab x y hx hy =>
    lt_trans hx.2 (lt_of_le_of_lt (hmono.monotone (Nat.succ_le_of_lt hab)) hy.1)
  have solU : ∀ lam s : ℝ, 0 < lam → 0 < s → Λ s = lam →
      ContDiffOn ℝ 2 (U lam s) (ball 0 1) ∧
      ContinuousOn (U lam s) (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → U lam s x = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, U lam s x = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ (U lam s) x + lam * Real.exp (U lam s x) = 0) :=
    fun lam s hl hs hsl => radial_global W Φ hw hφ0 hφ h0 s lam hs hl hsl
  have injU : ∀ lam s t : ℝ, 0 < lam → 0 < s → 0 < t → U lam s 0 = U lam t 0 → s = t :=
    fun lam s t hl hs ht h => ne_of_centre W h0 lam s t hs ht hl h
  refine ⟨?_, ?_, ?_⟩
  · -- (i) λ = 2
    have hk : ∀ k : ℕ, ∃ s ∈ Ioo (ζ k) (ζ (k + 1)), Λ s = 2 := fun k =>
      seg k 2 (by simpa using hne k) (by simpa using hne (k + 1))
    choose σ hσ hσΛ using hk
    refine ⟨fun i => U 2 (σ i), ?_, fun i => solU 2 (σ i) two_pos
      (lt_trans (hzpos i) (hσ i).1) (hσΛ i)⟩
    intro i j hij
    have := injU 2 (σ i) (σ j) two_pos (lt_trans (hzpos i) (hσ i).1)
      (lt_trans (hzpos j) (hσ j).1) hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd this (sep i j h _ _ (hσ i) (hσ j)).ne
    · exact h
    · exact absurd this (sep j i h _ _ (hσ j) (hσ i)).ne'
  · -- (ii) at least N near 2
    intro N
    set δ : ℝ := min 1 ((Finset.range (N + 1)).inf' ⟨0, by simp⟩ (fun k => |Λ (ζ k) - 2|)) with hδ
    have hδpos : 0 < δ := lt_min one_pos ((Finset.lt_inf'_iff _).2 (fun k _ => hne k))
    have hδle : ∀ k ≤ N, δ ≤ |Λ (ζ k) - 2| := fun k hk =>
      (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
    refine ⟨δ, hδpos, fun lam hl => ?_⟩
    have hl1 : |lam - 2| < 1 := lt_of_lt_of_le hl (min_le_left _ _)
    have hlpos : 0 < lam := by linarith [neg_abs_le (lam - 2)]
    have hk : ∀ i : Fin N, ∃ s ∈ Ioo (ζ i) (ζ ((i : ℕ) + 1)), Λ s = lam := fun i =>
      seg i lam (lt_of_lt_of_le hl (hδle i i.2.le)) (lt_of_lt_of_le hl (hδle (i + 1) i.2))
    choose σ hσ hσΛ using hk
    refine ⟨fun i => U lam (σ i), ?_, fun i => solU lam (σ i) hlpos
      (lt_trans (hzpos i) (hσ i).1) (hσΛ i)⟩
    intro i j hij
    have := injU lam (σ i) (σ j) hlpos (lt_trans (hzpos i) (hσ i).1)
      (lt_trans (hzpos j) (hσ j).1) hij
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact absurd this (sep i j h _ _ (hσ i) (hσ j)).ne
    · exact Fin.ext h
    · exact absurd this (sep j i h _ _ (hσ j) (hσ i)).ne'
  · -- (iii) two solutions for 2 ≤ λ < 3.321992118
    intro lam hl2 hlt
    have hlpos : (0 : ℝ) < lam := by linarith
    have hΛ0 : Λ 0 = 0 := by simp [hΛ]
    have hmax : lam < Λ (ζ 0) := by simp only [hΛ]; linarith
    have hmin : Λ (ζ 1) < 2 := (hband 0).1
    have c0 : ContinuousOn Λ (Icc 0 (ζ 0)) := cΛ.mono (fun t ht => ht.1)
    obtain ⟨s1, hs1, hs1Λ⟩ := intermediate_value_Ioo hz0.le c0 (show lam ∈ Ioo (Λ 0) (Λ (ζ 0)) from
      ⟨by rw [hΛ0]; exact hlpos, hmax⟩)
    obtain ⟨s2, hs2, hs2Λ⟩ := ivt 0 lam (Or.inr ⟨by linarith, hmax⟩)
    refine ⟨U lam s1, U lam s2, fun h => ?_, solU lam s1 hlpos hs1.1 hs1Λ,
      solU lam s2 hlpos (lt_trans hz0 hs2.1) hs2Λ⟩
    have := injU lam s1 s2 hlpos hs1.1 (lt_trans hz0 hs2.1) h
    linarith [hs1.2, hs2.1]

end Work.Math.GelfandPDEManyMain
