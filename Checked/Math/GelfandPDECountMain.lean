import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.PicardLindelof
import Checked.Math.RadialLaplacian
import Checked.Math.GelfandODEBound
import Checked.Math.IsoUniq
import Checked.Math.GelfandPDEManyMain
import Checked.Math.GelfandExtrema

/-! Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDECountMain`: the proof route of `Checked.Math.GelfandPDECount.gelfand_pde_radial_count`. Every radial classical solution with a positive parameter is W(s‖x‖) + log(s²/λ) on the closed ball for a radius s with s² e^{W(s)} = λ, W the regular isothermal solution (`profile`: the reduction of `Checked.Math.GelfandPDE.gelfand_pde_radial_bound`, the scaling of `Checked.Math.GelfandODEBound.ode_bound`, the uniqueness `Checked.Math.IsoUniq.uniq_Icc` below the radius and continuity at it); conversely every such radius gives one (`Checked.Math.GelfandPDEManyMain.radial_global`), and distinct radii give distinct centre values; the radii are counted with the turning points of `Checked.Math.GelfandExtrema.gelfand_extrema`. No new certificates. Promoted from `Work/Math/GelfandPDECountMain.lean`. -/

namespace Checked.Math.GelfandPDECountMain
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- The reduction of `Checked.Math.GelfandPDE.gelfand_pde_radial_bound` (copied from its proof): a radial
solution gives a profile f along an axis with the radial ODE, f'(0) = 0, f(1) = 0, continuity at 1, and
u(y) = f(‖y‖) on the open ball. -/
theorem reduce (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hrad : ∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) :
    ∃ f f' f'' : ℝ → ℝ,
      (∀ r ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f' r) r) ∧
      (∀ r ∈ Ioo (-1 : ℝ) 1, HasDerivAt f' (f'' r) r) ∧
      f' 0 = 0 ∧
      (∀ r ∈ Ioo (0 : ℝ) 1, f'' r + 2 / r * f' r + lam * Real.exp (f r) = 0) ∧
      ContinuousWithinAt f (Icc 0 1) 1 ∧ f 1 = 0 ∧ f 0 = u 0 ∧
      (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, u y = f ‖y‖) := by
  obtain ⟨g, hg⟩ := hrad
  set e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1 with he
  have hne : ‖e‖ = 1 := by simp [he]
  have hnorm : ∀ r : ℝ, ‖r • e‖ = |r| := fun r => by
    rw [norm_smul, hne, mul_one, Real.norm_eq_abs]
  set f : ℝ → ℝ := fun r => u (r • e) with hfdef
  have hmaps : MapsTo (fun r : ℝ => r • e) (Ioo (-1) 1) (ball 0 1) := fun r hr => by
    rw [mem_ball_zero_iff, hnorm, abs_lt]; exact hr
  have hf2 : ContDiffOn ℝ 2 f (Ioo (-1) 1) :=
    hu.comp (contDiff_id.smul contDiff_const).contDiffOn hmaps
  have hf1 : ContDiffOn ℝ 1 (deriv f) (Ioo (-1) 1) :=
    hf2.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hf : ∀ r ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (deriv f r) r := fun r hr =>
    ((hf2.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hr)).hasDerivAt
  have hf' : ∀ r ∈ Ioo (-1 : ℝ) 1, HasDerivAt (deriv f) (deriv (deriv f) r) r := fun r hr =>
    ((hf1.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hr)).hasDerivAt
  -- f r = g |r| near the axis
  have hfg : ∀ r ∈ Icc (-1 : ℝ) 1, f r = g |r| := fun r hr => by
    have : r • e ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      rw [mem_closedBall_zero_iff, hnorm, abs_le]; exact hr
    simp only [hfdef]; rw [hg _ this, hnorm]
  -- u is radial through f on the open ball
  have hradf : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, u y = f ‖y‖ := fun y hy => by
    have hy' : ‖y‖ ∈ Icc (-1 : ℝ) 1 := by
      rw [mem_ball_zero_iff] at hy; exact ⟨by linarith [norm_nonneg y], hy.le⟩
    rw [hfg _ hy', abs_of_nonneg (norm_nonneg y)]
    exact hg y (ball_subset_closedBall hy)
  -- f'(0) = 0 by evenness
  have hf'0 : deriv f 0 = 0 := by
    have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
    have hA := hf 0 h0
    have hB : HasDerivAt (fun r => f (-r)) (-deriv f 0) 0 := by
      have hn : HasDerivAt f (deriv f 0) (-(0 : ℝ)) := by rw [neg_zero]; exact hf 0 h0
      have h := hn.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
      convert h using 1
      · rfl
      · ring
    have hev : (fun r => f (-r)) =ᶠ[𝓝 0] f := by
      filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)]
        with r hr
      rw [hfg r ⟨hr.1.le, hr.2.le⟩, hfg (-r) ⟨by linarith [hr.2], by linarith [hr.1]⟩, abs_neg]
    have := hA.unique (hB.congr_of_eventuallyEq hev.symm)
    linarith
  -- the radial ODE on (0, 1)
  have hode : ∀ r ∈ Ioo (0 : ℝ) 1,
      deriv (deriv f) r + 2 / r * deriv f r + lam * Real.exp (f r) = 0 := by
    intro r hr
    have hr' : r ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hr.1], hr.2⟩
    set x : EuclideanSpace ℝ (Fin 3) := r • e with hx
    have hxn : ‖x‖ = r := by rw [hx, hnorm, abs_of_pos hr.1]
    have hx0 : x ≠ 0 := by
      intro h; rw [h, norm_zero] at hxn; linarith [hr.1]
    have hxb : x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := hmaps hr'
    have hev : u =ᶠ[𝓝 x] fun y => f ‖y‖ := by
      filter_upwards [isOpen_ball.mem_nhds hxb] with y hy using hradf y hy
    have hL := Checked.Math.RadialLaplacian.laplacian_radial (f := f) (f' := deriv f)
      (f'' := deriv (deriv f) ‖x‖) hx0
      (by
        rw [hxn]
        filter_upwards [isOpen_Ioo.mem_nhds hr'] with ρ hρ using hf ρ hρ)
      (by rw [hxn]; exact hf' r hr')
    have h := hpde x hxb
    rw [(laplacian_congr_nhds hev).eq_of_nhds, hL, hxn, finrank_euclideanSpace_fin] at h
    have hux : u x = f r := rfl
    rw [hux] at h
    have : ((3 : ℕ) : ℝ) - 1 = 2 := by norm_num
    rw [this] at h
    exact h
  have hcont : ContinuousWithinAt f (Icc 0 1) 1 := by
    have hm : MapsTo (fun r : ℝ => r • e) (Icc 0 1) (closedBall 0 1) := fun r hr => by
      rw [mem_closedBall_zero_iff, hnorm, abs_le]; exact ⟨by linarith [hr.1], hr.2⟩
    exact (hc.comp (continuous_id.smul continuous_const).continuousOn hm) 1
      ⟨zero_le_one, le_rfl⟩
  have h1 : f 1 = 0 := by
    simp only [hfdef, one_smul]; exact hb e hne
  have hf00 : f 0 = u 0 := by simp only [hfdef, zero_smul]
  exact ⟨f, deriv f, deriv (deriv f), hf, hf', hf'0, hode, hcont, h1, hf00, hradf⟩

/-- Every radial solution with lam > 0 is one of the solutions built from a radius of the regular solution. -/
theorem profile (W Φ : ℝ → ℝ)
    (hW : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt W (Φ s) (Ici 0) s)
    (hΦ0 : ContinuousWithinAt Φ (Ici 0) 0)
    (hΦ : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt Φ (-(2 / s * Φ s) - Real.exp (W s)) (Ici 0) s)
    (hW0 : W 0 = 0) (lam : ℝ) (hlam : 0 < lam) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hrad : ∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) :
    ∃ k : ℝ, 0 < k ∧ k ^ 2 * Real.exp (W k) = lam ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = W (k * ‖x‖) + Real.log (k ^ 2 / lam) := by
  obtain ⟨f, f', f'', hf, hf', hf'0, hode, hcont, h1, hf00, hradf⟩ := reduce lam u hu hc hb hrad hpde
  set α := f 0 with hα
  set k := Real.sqrt lam * Real.exp (α / 2) with hk
  have hk0 : 0 < k := mul_pos (Real.sqrt_pos.2 hlam) (Real.exp_pos _)
  have hkne : k ≠ 0 := hk0.ne'
  have hk2 : k ^ 2 = lam * Real.exp α := by
    rw [hk, mul_pow, Real.sq_sqrt hlam.le, sq, ← Real.exp_add, add_halves]
  set w : ℝ → ℝ := fun s => f (s / k) - α with hw
  set φ : ℝ → ℝ := fun s => f' (s / k) / k with hφ
  have mem : ∀ s ∈ Ioo (-k) k, s / k ∈ Ioo (-1 : ℝ) 1 := fun s hs =>
    ⟨by rw [lt_div_iff₀ hk0]; linarith [hs.1], by rw [div_lt_one hk0]; exact hs.2⟩
  have dw : ∀ s ∈ Ioo (-k) k, HasDerivAt w (φ s) s := by
    intro s hs
    have h := ((hf _ (mem s hs)).comp s ((hasDerivAt_id s).div_const k)).sub_const α
    convert h using 1
    · rfl
    · simp only [hφ]; ring
  have dφ : ∀ s ∈ Ioo (-k) k, HasDerivAt φ (f'' (s / k) / k ^ 2) s := by
    intro s hs
    have h := ((hf' _ (mem s hs)).comp s ((hasDerivAt_id s).div_const k)).div_const k
    convert h using 1
    · rfl
    · ring
  have hode' : ∀ s ∈ Ioo 0 k, f'' (s / k) / k ^ 2 = -(2 / s * φ s) - Real.exp (w s) := by
    intro s hs
    have hr : s / k ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hs.1 hk0, (div_lt_one hk0).2 hs.2⟩
    have h := hode _ hr
    have hs0 : s ≠ 0 := hs.1.ne'
    have e1 : Real.exp (w s) = Real.exp (f (s / k)) / Real.exp α := by
      simp only [hw, Real.exp_sub]
    rw [e1, hφ]
    have hlam' : lam = k ^ 2 / Real.exp α := by
      rw [hk2]; field_simp
    rw [hlam'] at h
    field_simp at h ⊢
    linear_combination h
  have w0 : w 0 = 0 := by simp [hw, hα]
  -- w = W on [0, k)
  have agree : ∀ s ∈ Ico 0 k, w s = W s := by
    intro s hs
    set T := (s + k) / 2 with hT
    have hT0 : 0 < T := by linarith [hs.1, hs.2]
    have hTk : T < k := by linarith [hs.2]
    have inK : ∀ t ∈ Icc (0 : ℝ) T, t ∈ Ioo (-k) k := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have := Checked.Math.IsoUniq.uniq_Icc hT0
      (fun t ht => (dw t (inK t ht)).hasDerivWithinAt)
      ((dφ 0 (inK 0 ⟨le_rfl, hT0.le⟩)).continuousAt.continuousWithinAt)
      (fun t ht => by
        rw [← hode' t ⟨ht.1, by linarith [ht.2]⟩]
        exact (dφ t (inK t (Ioc_subset_Icc_self ht))).hasDerivWithinAt)
      (fun t ht => (hW t ht.1).mono Icc_subset_Ici_self) (hΦ0.mono Icc_subset_Ici_self)
      (fun t ht => (hΦ t ht.1).mono Icc_subset_Ici_self) (by rw [w0, hW0])
      s ⟨hs.1, by linarith [hs.2]⟩
    exact this.1
  -- W k = -α, by continuity from the left
  have Wk : W k = -α := by
    have hcomp : ContinuousWithinAt (fun c => f (c / k) - α) (Ioo 0 k) k := by
      have hc1 : ContinuousWithinAt f (Icc 0 1) (k / k) := by rwa [div_self hkne]
      have hm : MapsTo (fun c : ℝ => c / k) (Ioo 0 k) (Icc 0 1) := fun c hc =>
        ⟨(div_pos hc.1 hk0).le, ((div_lt_one hk0).2 hc.2).le⟩
      have h2 : ContinuousWithinAt (fun c => f (c / k)) (Ioo 0 k) k :=
        ContinuousWithinAt.comp (f := fun c : ℝ => c / k) hc1
          (continuous_id.div_const k).continuousWithinAt hm
      exact h2.sub continuousWithinAt_const
    have t1 := hcomp.tendsto
    rw [nhdsWithin_Ioo_eq_nhdsLT hk0] at t1
    have cW : ContinuousWithinAt W (Ioo 0 k) k :=
      (hW k (le_of_lt hk0)).continuousWithinAt.mono (fun t ht => le_of_lt ht.1)
    have t2 := cW.tendsto
    rw [nhdsWithin_Ioo_eq_nhdsLT hk0] at t2
    have t3 : Tendsto W (𝓝[<] k) (𝓝 (f (k / k) - α)) := by
      refine t1.congr' ?_
      rw [← nhdsWithin_Ioo_eq_nhdsLT hk0]
      filter_upwards [self_mem_nhdsWithin] with c hc using agree c ⟨hc.1.le, hc.2⟩
    have := tendsto_nhds_unique t2 t3
    rw [this, div_self hkne, h1, zero_sub]
  have hlog : Real.log (k ^ 2 / lam) = α := by
    rw [hk2, mul_div_cancel_left₀ _ hlam.ne', Real.log_exp]
  refine ⟨k, hk0, ?_, fun x hx => ?_⟩
  · rw [Wk, hk2, Real.exp_neg]; field_simp
  · rw [hlog]
    rcases (mem_closedBall_zero_iff.1 hx).lt_or_eq with hlt | heq
    · have hy : x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := mem_ball_zero_iff.2 hlt
      have hn0 := norm_nonneg x
      have hmem : k * ‖x‖ ∈ Ico 0 k :=
        ⟨by positivity, by nlinarith⟩
      rw [hradf x hy, ← agree _ hmem]
      simp only [hw]
      rw [mul_div_cancel_left₀ _ hkne]; ring
    · rw [hb x heq, heq, mul_one, Wk]; ring

theorem main :
    ∃ lamStar lam1 lam2 : ℝ, 3.321992118 ≤ lamStar ∧ lamStar ≤ 3.321992119 ∧
      0 < lam1 ∧ lam1 < 2 ∧ 2 < lam2 ∧ lam2 < lamStar ∧
      (∀ lam : ℝ, lamStar < lam → ∀ u : EuclideanSpace ℝ (Fin 3) → ℝ,
        ¬ (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0))) ∧
      (∃ u : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lamStar * Real.exp (u x) = 0)) ∧
        ∀ v : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lamStar * Real.exp (v x) = 0)) →
          ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = u x) ∧
      (∀ lam : ℝ, lam2 < lam → lam < lamStar →
        ∃ u v : EuclideanSpace ℝ (Fin 3) → ℝ, u 0 ≠ v 0 ∧ (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧ (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lam * Real.exp (v x) = 0)) ∧
          ∀ f : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 f (ball 0 1) ∧
          ContinuousOn f (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → f x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ f x + lam * Real.exp (f x) = 0)) →
            (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = u x) ∨
            (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = v x)) ∧
      (∀ lam : ℝ, 0 < lam → lam < lam1 →
        ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
          ∀ v : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lam * Real.exp (v x) = 0)) →
            ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = u x) ∧
      (∃ u v : EuclideanSpace ℝ (Fin 3) → ℝ, u 0 ≠ v 0 ∧ (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam1 * Real.exp (u x) = 0)) ∧ (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lam1 * Real.exp (v x) = 0)) ∧
          ∀ f : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 f (ball 0 1) ∧
          ContinuousOn f (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → f x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ f x + lam1 * Real.exp (f x) = 0)) →
            (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = u x) ∨ (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = v x)) ∧
      (∃ u v w : EuclideanSpace ℝ (Fin 3) → ℝ, u 0 ≠ v 0 ∧ u 0 ≠ w 0 ∧ v 0 ≠ w 0 ∧
          (ContDiffOn ℝ 2 u (ball 0 1) ∧
          ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam2 * Real.exp (u x) = 0)) ∧ (ContDiffOn ℝ 2 v (ball 0 1) ∧
          ContinuousOn v (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → v x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x + lam2 * Real.exp (v x) = 0)) ∧ (ContDiffOn ℝ 2 w (ball 0 1) ∧
          ContinuousOn w (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → w x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, w x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ w x + lam2 * Real.exp (w x) = 0)) ∧
          ∀ f : EuclideanSpace ℝ (Fin 3) → ℝ, (ContDiffOn ℝ 2 f (ball 0 1) ∧
          ContinuousOn f (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → f x = 0) ∧
          (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = g ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ f x + lam2 * Real.exp (f x) = 0)) →
            (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = u x) ∨ (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = v x) ∨ (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = w x)) := by
  obtain ⟨W, Φ, hw, hφ0, hφ, h0⟩ := Checked.Math.BEGlobalExists.exists_global
  obtain ⟨ζ, hmono, -, hz0lo, -, hl0lo, hl0hi, hmax0, hminA, hmaxA, hband, -, hinc0, hdecA, -⟩ :=
    Checked.Math.GelfandExtrema.gelfand_extrema W Φ hw hφ0 hφ h0
  have hmin := hminA 0
  have hmaxk := hmaxA 0
  have hdec := hdecA 0
  have hb0 := hband 0
  have hb1 := hband 1
  simp only [mul_zero, mul_one, zero_add] at hmin hmaxk hdec hb0 hb1
  set Λ : ℝ → ℝ := fun s => s ^ 2 * Real.exp (W s) with hΛ
  have cW : ContinuousOn W (Ici 0) := fun t ht => (hw t ht).continuousWithinAt
  have cΛ : ContinuousOn Λ (Ici 0) := (continuousOn_id.pow 2).mul cW.rexp
  have hz0 : 0 < ζ 0 := by norm_num at hz0lo; linarith
  have h01 : ζ 0 < ζ 1 := hmono (by norm_num)
  have h12 : ζ 1 < ζ 2 := hmono (by norm_num)
  have Λpos : ∀ s, 0 < s → 0 < Λ s := fun s hs => by simp only [hΛ]; positivity
  have Λ0 : Λ 0 = 0 := by simp [hΛ]
  -- the solution attached to a radius, and the converse
  have solU : ∀ lam s : ℝ, 0 < lam → 0 < s → Λ s = lam →
      ContDiffOn ℝ 2 (fun x : EuclideanSpace ℝ (Fin 3) => W (s * ‖x‖) + Real.log (s ^ 2 / lam))
        (ball 0 1) ∧
      ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) => W (s * ‖x‖) + Real.log (s ^ 2 / lam))
        (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → W (s * ‖x‖) + Real.log (s ^ 2 / lam) = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
        W (s * ‖x‖) + Real.log (s ^ 2 / lam) = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
        Δ (fun x : EuclideanSpace ℝ (Fin 3) => W (s * ‖x‖) + Real.log (s ^ 2 / lam)) x +
          lam * Real.exp (W (s * ‖x‖) + Real.log (s ^ 2 / lam)) = 0) :=
    fun lam s hl hs hsl => Checked.Math.GelfandPDEManyMain.radial_global W Φ hw hφ0 hφ h0 s lam hs hl hsl
  have neU : ∀ lam a b : ℝ, 0 < lam → 0 < a → 0 < b → a ≠ b →
      W (a * ‖(0 : EuclideanSpace ℝ (Fin 3))‖) + Real.log (a ^ 2 / lam) ≠
        W (b * ‖(0 : EuclideanSpace ℝ (Fin 3))‖) + Real.log (b ^ 2 / lam) :=
    fun lam a b hl ha hb hab h =>
      hab (Checked.Math.GelfandPDEManyMain.ne_of_centre W h0 lam a b ha hb hl h)
  have prof := profile W Φ hw hφ0 hφ h0
  -- root facts
  have below : ∀ s, 0 ≤ s → s ≠ ζ 0 → Λ s < Λ (ζ 0) := fun s hs hne => hmax0 s hs hne
  have left : ∀ lam, 0 < lam → lam < Λ (ζ 0) → ∃ s1 ∈ Ioo 0 (ζ 0), Λ s1 = lam ∧
      ∀ s ∈ Icc 0 (ζ 0), Λ s = lam → s = s1 := by
    intro lam hl hlt
    have c0 : ContinuousOn Λ (Icc 0 (ζ 0)) := cΛ.mono (fun t ht => ht.1)
    obtain ⟨s1, hs1, hs1Λ⟩ := intermediate_value_Ioo hz0.le c0 (show lam ∈ Ioo (Λ 0) (Λ (ζ 0)) from
      ⟨by rw [Λ0]; exact hl, hlt⟩)
    exact ⟨s1, hs1, hs1Λ, fun s hs hsΛ =>
      hinc0.injOn hs (Ioo_subset_Icc_self hs1) (hsΛ.trans hs1Λ.symm)⟩
  have mid : ∀ lam, Λ (ζ 1) < lam → lam < Λ (ζ 0) → ∃ s2 ∈ Ioo (ζ 0) (ζ 1), Λ s2 = lam ∧
      ∀ s ∈ Icc (ζ 0) (ζ 1), Λ s = lam → s = s2 := by
    intro lam hl hlt
    have c0 : ContinuousOn Λ (Icc (ζ 0) (ζ 1)) := cΛ.mono (fun t ht => le_trans hz0.le ht.1)
    obtain ⟨s2, hs2, hs2Λ⟩ := intermediate_value_Ioo' h01.le c0 (show lam ∈ Ioo (Λ (ζ 1)) (Λ (ζ 0)) from
      ⟨hl, hlt⟩)
    exact ⟨s2, hs2, hs2Λ, fun s hs hsΛ =>
      hdec.injOn hs (Ioo_subset_Icc_self hs2) (hsΛ.trans hs2Λ.symm)⟩
  have l1pos : 0 < Λ (ζ 1) := Λpos _ (hz0.trans h01)
  have l1lt : Λ (ζ 1) < 2 := hb0.1
  have l2gt : 2 < Λ (ζ 2) := hb1.2
  have l2lt : Λ (ζ 2) < Λ (ζ 0) := below _ (hz0.trans (h01.trans h12)).le (hmono.injective.ne (by norm_num))
  have l1lt0 : Λ (ζ 1) < Λ (ζ 0) := by linarith
  refine ⟨Λ (ζ 0), Λ (ζ 1), Λ (ζ 2), by simpa [hΛ] using hl0lo, by simpa [hΛ] using hl0hi,
    l1pos, l1lt, l2gt, l2lt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a) none above
    intro lam hlt u hu
    obtain ⟨hu1, hu2, hu3, hu4, hu5⟩ := hu
    have hl : 0 < lam := by linarith [Λpos _ hz0]
    obtain ⟨k, hk, hkΛ, -⟩ := prof lam hl u hu1 hu2 hu3 hu4 hu5
    have : Λ k ≤ Λ (ζ 0) := by
      rcases eq_or_ne k (ζ 0) with h | h
      · rw [h]
      · exact (below k hk.le h).le
    have : Λ k = lam := hkΛ
    linarith
  · -- (b) exactly one at the maximum
    have hl : 0 < Λ (ζ 0) := Λpos _ hz0
    refine ⟨_, solU (Λ (ζ 0)) (ζ 0) hl hz0 rfl, fun v hv x hx => ?_⟩
    obtain ⟨hv1, hv2, hv3, hv4, hv5⟩ := hv
    obtain ⟨k, hk, hkΛ, hkv⟩ := prof _ hl v hv1 hv2 hv3 hv4 hv5
    have hkz : k = ζ 0 := by
      by_contra h
      have := below k hk.le h
      have : Λ k = Λ (ζ 0) := hkΛ
      linarith
    rw [hkv x hx, hkz]
  · -- (c) exactly two between the second maximum and the maximum
    intro lam hl2 hlt
    have hl : 0 < lam := by linarith
    obtain ⟨s1, hs1, hs1Λ, hs1u⟩ := left lam hl hlt
    obtain ⟨s2, hs2, hs2Λ, hs2u⟩ := mid lam (by linarith) hlt
    have p1 : 0 < s1 := hs1.1
    have p2 : 0 < s2 := hz0.trans hs2.1
    refine ⟨_, _, neU lam s1 s2 hl p1 p2 (by linarith [hs1.2, hs2.1]),
      solU lam s1 hl p1 hs1Λ, solU lam s2 hl p2 hs2Λ, fun f hf => ?_⟩
    obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ := hf
    obtain ⟨k, hk, hkΛ, hkf⟩ := prof lam hl f hf1 hf2 hf3 hf4 hf5
    have hkΛ' : Λ k = lam := hkΛ
    rcases le_or_gt k (ζ 0) with h | h
    · left; intro x hx; rw [hkf x hx, hs1u k ⟨hk.le, h⟩ hkΛ']
    · rcases le_or_gt k (ζ 1) with h' | h'
      · right; intro x hx; rw [hkf x hx, hs2u k ⟨h.le, h'⟩ hkΛ']
      · exfalso
        rcases eq_or_ne k (ζ 2) with he | he
        · rw [he] at hkΛ'; linarith
        · have := hmaxk k h'.le he
          have : Λ k < Λ (ζ 2) := this
          linarith
  · -- (d) exactly one below the first minimum
    intro lam hl hlt
    obtain ⟨s1, hs1, hs1Λ, hs1u⟩ := left lam hl (by linarith)
    refine ⟨_, solU lam s1 hl hs1.1 hs1Λ, fun f hf x hx => ?_⟩
    obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ := hf
    obtain ⟨k, hk, hkΛ, hkf⟩ := prof lam hl f hf1 hf2 hf3 hf4 hf5
    have hkΛ' : Λ k = lam := hkΛ
    rcases le_or_gt k (ζ 0) with h | h
    · rw [hkf x hx, hs1u k ⟨hk.le, h⟩ hkΛ']
    · exfalso
      rcases eq_or_ne k (ζ 1) with he | he
      · rw [he] at hkΛ'; linarith
      · have := hmin k h.le he
        have : Λ (ζ 1) < Λ k := this
        linarith
  · -- (e) exactly two at the first minimum
    have hl := l1pos
    obtain ⟨s1, hs1, hs1Λ, hs1u⟩ := left _ hl l1lt0
    have p1 : 0 < s1 := hs1.1
    have p2 : 0 < ζ 1 := hz0.trans h01
    refine ⟨_, _, neU _ s1 (ζ 1) hl p1 p2 (by linarith [hs1.2]),
      solU _ s1 hl p1 hs1Λ, solU _ (ζ 1) hl p2 rfl, fun f hf => ?_⟩
    obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ := hf
    obtain ⟨k, hk, hkΛ, hkf⟩ := prof _ hl f hf1 hf2 hf3 hf4 hf5
    have hkΛ' : Λ k = Λ (ζ 1) := hkΛ
    rcases le_or_gt k (ζ 0) with h | h
    · left; intro x hx; rw [hkf x hx, hs1u k ⟨hk.le, h⟩ hkΛ']
    · right
      have he : k = ζ 1 := by
        by_contra he
        have := hmin k h.le he
        have : Λ (ζ 1) < Λ k := this
        linarith
      intro x hx; rw [hkf x hx, he]
  · -- (f) exactly three at the second maximum
    have hl : 0 < Λ (ζ 2) := by linarith
    obtain ⟨s1, hs1, hs1Λ, hs1u⟩ := left _ hl l2lt
    obtain ⟨s2, hs2, hs2Λ, hs2u⟩ := mid _ (by linarith) l2lt
    have p1 : 0 < s1 := hs1.1
    have p2 : 0 < s2 := hz0.trans hs2.1
    have p3 : 0 < ζ 2 := hz0.trans (h01.trans h12)
    refine ⟨_, _, _, neU _ s1 s2 hl p1 p2 (by linarith [hs1.2, hs2.1]),
      neU _ s1 (ζ 2) hl p1 p3 (by linarith [hs1.2]),
      neU _ s2 (ζ 2) hl p2 p3 (by linarith [hs2.2]),
      solU _ s1 hl p1 hs1Λ, solU _ s2 hl p2 hs2Λ, solU _ (ζ 2) hl p3 rfl, fun f hf => ?_⟩
    obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ := hf
    obtain ⟨k, hk, hkΛ, hkf⟩ := prof _ hl f hf1 hf2 hf3 hf4 hf5
    have hkΛ' : Λ k = Λ (ζ 2) := hkΛ
    rcases le_or_gt k (ζ 0) with h | h
    · left; intro x hx; rw [hkf x hx, hs1u k ⟨hk.le, h⟩ hkΛ']
    · rcases le_or_gt k (ζ 1) with h' | h'
      · right; left; intro x hx; rw [hkf x hx, hs2u k ⟨h.le, h'⟩ hkΛ']
      · right; right
        have he : k = ζ 2 := by
          by_contra he
          have := hmaxk k h'.le he
          have : Λ k < Λ (ζ 2) := this
          linarith
        intro x hx; rw [hkf x hx, he]

end Checked.Math.GelfandPDECountMain
