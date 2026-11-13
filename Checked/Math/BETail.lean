import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Checked.Math.BonnorEbert
import Checked.Math.BEEnd

/-! Bonnor–Ebert sphere, `BETail`: beyond the end radius of the certified cells the confined mass stays below the lower end of the critical mass window. In the homology (Milne) variables of the isothermal equation (u the ratio of the local to the mean density, v the logarithmic slope) the equation is a Lotka–Volterra system in the logarithm of the radius, and Volterra's function of u and v does not increase along it. Its value at the end radius is bounded from the certified state there, and on its sublevel set the product of u with the cube of v (four pi times the squared mass) stays below its value at the critical radius, by a convex-duality bound that is one application of the inequality between the logarithm and its tangent line. Promoted from `Work/Math/BETail.lean`. -/

namespace Checked.Math.BETail
open Set

/- Convex-duality bound for x − 1 − log x. -/
theorem dual {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    a * Real.log x + a - (1 + a) * Real.log (1 + a) ≤ x - 1 - Real.log x := by
  have h1 : 0 < 1 + a := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hx h1)
  rw [Real.log_div hx.ne' h1.ne'] at h
  have h2 : (1 + a) * (Real.log x - Real.log (1 + a)) ≤ (1 + a) * (x / (1 + a) - 1) :=
    mul_le_mul_of_nonneg_left h h1.le
  have h3 : (1 + a) * (x / (1 + a) - 1) = x - 1 - a := by field_simp; ring
  nlinarith

theorem log_29 : Real.log (29 / 25) ≤ 1484201 / 10000000 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(-4 / 25 : ℝ)| < 1 by norm_num [abs_lt]) 12
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_31 : Real.log (31 / 25) ≤ 2151114 / 10000000 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(-6 / 25 : ℝ)| < 1 by norm_num [abs_lt]) 14
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_K16 : 932284 / 10000000 ≤ Real.log (175634 / 160000) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |(-15634 / 160000 : ℝ)| < 1 by norm_num [abs_lt]) 10
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_u7 : 1443080 / 10000000 ≤ Real.log (1155239948 / 1000000000) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |(-155239948 / 1000000000 : ℝ)| < 1 by norm_num [abs_lt]) 12
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem log_v7 : 2117758 / 10000000 ≤ Real.log (247174165413 / 200000000000) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |(-47174165413 / 200000000000 : ℝ)| < 1 by norm_num [abs_lt]) 14
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  linarith [h.1, h.2]

/- The final inequality in homology variables: if V(u, v) does not exceed its bound at radius seven, then
u v³ < K (K = 175634/10000, below 4π times the square of the critical mass's lower end). -/
theorem uv_bound {u v u7 v7 : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hu7 : 1155239948 / 1000000000 ≤ u7) (hu7' : u7 ≤ 115523994832 / 100000000000)
    (hv7 : 247174165413 / 100000000000 ≤ v7) (hv7' : v7 ≤ 2471741654200 / 1000000000000)
    (hV : u + v - Real.log u - 2 * Real.log (v / 2) ≤
      u7 + v7 - Real.log u7 - 2 * Real.log (v7 / 2)) :
    u * v ^ 3 < 175634 / 10000 := by
  by_contra hK'
  have hK := not_lt.mp hK'
  have hv2 : 0 < v / 2 := by positivity
  -- duality bounds
  have d1 := dual hu (show (0 : ℝ) < 4 / 25 by norm_num)
  have d2 := dual hv2 (show (0 : ℝ) < 6 / 25 by norm_num)
  norm_num at d1 d2
  -- log (u v³ / 8) = log u + 3 log (v/2)
  have hprod : Real.log (u * v ^ 3 / 8) = Real.log u + 3 * Real.log (v / 2) := by
    have : u * v ^ 3 / 8 = u * (v / 2) ^ 3 := by ring
    rw [this, Real.log_mul hu.ne' (by positivity), Real.log_pow]
    push_cast; ring
  have hmono : Real.log (175634 / 10000 / 8) ≤ Real.log (u * v ^ 3 / 8) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hK8 : Real.log (175634 / 10000 / 8 : ℝ) = Real.log 2 + Real.log (175634 / 160000) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l2 := Real.log_two_gt_d9
  have lK := log_K16
  have l29 := log_29
  have l31 := log_31
  -- bound at radius seven
  have lu7 : Real.log (1155239948 / 1000000000) ≤ Real.log u7 :=
    Real.log_le_log (by norm_num) hu7
  have lv7 : Real.log (247174165413 / 200000000000) ≤ Real.log (v7 / 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have lu := log_u7
  have lv := log_v7
  linarith

/- Beyond radius seven the mass stays below the critical lower end, given the certified state at seven. -/
theorem tail (S : ℝ) (hS : 7 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (hE7 : (5827458572 / 100000000000 : ℝ) ≤ Real.exp (w 7))
    (hE7' : Real.exp (w 7) ≤ 5827458573 / 100000000000)
    (hp7 : (-35310595060 / 100000000000 : ℝ) ≤ φ 7) (hp7' : φ 7 ≤ -35310595059 / 100000000000) :
    ∀ s ∈ Icc (7 : ℝ) S,
      s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) < 1.1822265 := by
  have dv : ∀ x ∈ Ioo (0 : ℝ) S, HasDerivAt w (φ x) x ∧
      HasDerivAt φ (-(2 / x * φ x) - Real.exp (w x)) x :=
    fun x hx => Checked.Math.GFinal.derivs_at hw hφ hx
  have hsub : Icc (7 : ℝ) S ⊆ Icc 0 S := Icc_subset_Icc (by norm_num) le_rfl
  have cw : ContinuousOn w (Icc 7 S) := fun s hs => (hw s (hsub hs)).continuousWithinAt.mono hsub
  have cφ : ContinuousOn φ (Icc 7 S) := fun s hs =>
    (hφ s ⟨by linarith [hs.1], hs.2⟩).continuousWithinAt.mono hsub
  -- s² φ(s) decreases strictly, so φ < 0 on [7, S]
  have gA : StrictAntiOn (fun s => s ^ 2 * φ s) (Icc 7 S) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 7 S) ((continuousOn_pow 2).mul cφ)
    intro x hx
    rw [interior_Icc] at hx
    obtain ⟨-, h2⟩ := dv x ⟨by linarith [hx.1], hx.2⟩
    have hd := (hasDerivAt_pow 2 x).mul h2
    rw [hd.deriv]
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have e : ((2 : ℕ) : ℝ) * x ^ (2 - 1) * φ x + x ^ 2 * (-(2 / x * φ x) - Real.exp (w x)) =
        -(x ^ 2 * Real.exp (w x)) := by push_cast; field_simp; ring
    rw [e]
    have := Real.exp_pos (w x)
    have : 0 < x ^ 2 := by positivity
    nlinarith
  have φneg : ∀ s ∈ Icc (7 : ℝ) S, φ s < 0 := by
    intro s hs
    have h : s ^ 2 * φ s ≤ 7 ^ 2 * φ 7 := gA.antitoneOn ⟨le_rfl, hS⟩ hs hs.1
    have h7 : (7 : ℝ) ^ 2 * φ 7 < 0 := by nlinarith
    have hs2 : 0 < s ^ 2 := by have := hs.1; positivity
    by_contra hc
    push_neg at hc
    nlinarith
  -- Volterra's function in homology variables
  set V : ℝ → ℝ := fun s => s * Real.exp (w s) / -φ s + -(s * φ s) -
    Real.log (s * Real.exp (w s) / -φ s) - 2 * Real.log (-(s * φ s) / 2) with hVdef
  have upos : ∀ s ∈ Icc (7 : ℝ) S, 0 < s * Real.exp (w s) / -φ s := fun s hs => by
    have := φneg s hs; have := Real.exp_pos (w s); have : (0 : ℝ) < s := by linarith [hs.1]
    apply div_pos (by positivity) (by linarith)
  have vpos : ∀ s ∈ Icc (7 : ℝ) S, 0 < -(s * φ s) / 2 := fun s hs => by
    have := φneg s hs; have : (0 : ℝ) < s := by linarith [hs.1]
    have : s * φ s < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  have cV : ContinuousOn V (Icc 7 S) := by
    have cu : ContinuousOn (fun s => s * Real.exp (w s) / -φ s) (Icc 7 S) :=
      (continuousOn_id.mul cw.rexp).div cφ.neg (fun s hs => by have := φneg s hs; linarith)
    have cv : ContinuousOn (fun s => -(s * φ s)) (Icc 7 S) := (continuousOn_id.mul cφ).neg
    exact ((cu.add cv).sub (cu.log (fun s hs => (upos s hs).ne'))).sub
      (((cv.div_const 2).log (fun s hs => (vpos s hs).ne')).const_smul (2 : ℝ))
  have dV : ∀ x ∈ Ioo (7 : ℝ) S, HasDerivAt V
      (-((x * Real.exp (w x) / -φ x - 1) ^ 2 / x)) x := by
    intro x hx
    have hxI : x ∈ Icc (7 : ℝ) S := Ioo_subset_Icc_self hx
    obtain ⟨h1, h2⟩ := dv x ⟨by linarith [hx.1], hx.2⟩
    have hp := φneg x hxI
    have hx0 : 0 < x := by linarith [hx.1]
    have hE := h1.exp
    have hu := ((hasDerivAt_id' x).mul hE).div h2.neg (by simp only [Pi.neg_apply]; linarith)
    have hv := ((hasDerivAt_id' x).mul h2).neg
    have hlu := hu.log (upos x hxI).ne'
    have hlv := (hv.div_const 2).log (vpos x hxI).ne'
    have hV := ((hu.add hv).sub hlu).sub (hlv.const_mul 2)
    refine hV.congr_deriv ?_
    have hE0 := Real.exp_pos (w x)
    have hp0 : φ x ≠ 0 := by linarith
    simp only [Pi.neg_apply, Pi.mul_apply, Pi.div_apply]
    field_simp
    ring
  have VA : AntitoneOn V (Icc 7 S) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 7 S) cV
    · intro x hx
      rw [interior_Icc] at hx
      exact (dV x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(dV x hx).deriv]
      have hx0 : 0 < x := by linarith [hx.1]
      have : 0 ≤ (x * Real.exp (w x) / -φ x - 1) ^ 2 / x := by positivity
      linarith
  -- the state at radius seven
  have u7lo : (1155239948 / 1000000000 : ℝ) ≤ 7 * Real.exp (w 7) / -φ 7 := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have u7hi : 7 * Real.exp (w 7) / -φ 7 ≤ 115523994832 / 100000000000 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have v7lo : (247174165413 / 100000000000 : ℝ) ≤ -(7 * φ 7) := by linarith
  have v7hi : -(7 * φ 7) ≤ 2471741654200 / 1000000000000 := by linarith
  have h7I : (7 : ℝ) ∈ Icc 7 S := ⟨le_rfl, hS⟩
  intro s hs
  have hVs : V s ≤ V 7 := VA h7I hs hs.1
  simp only [hVdef] at hVs
  have huv := uv_bound (u := s * Real.exp (w s) / -φ s) (v := -(s * φ s))
    (u7 := 7 * Real.exp (w 7) / -φ 7) (v7 := -(7 * φ 7))
    (upos s hs) (by linarith [vpos s hs]) u7lo u7hi v7lo v7hi hVs
  have hp := φneg s hs
  have hs0 : 0 < s := by linarith [hs.1]
  have hE0 := Real.exp_pos (w s)
  have hpi : 0 < 4 * Real.pi := by positivity
  have hsq : Real.sqrt (4 * Real.pi) ^ 2 = 4 * Real.pi := Real.sq_sqrt hpi.le
  have hsq0 : 0 < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.mpr hpi
  have he2 : Real.exp (w s / 2) ^ 2 = Real.exp (w s) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have huv' : s * Real.exp (w s) / -φ s * (-(s * φ s)) ^ 3 = s ^ 4 * φ s ^ 2 * Real.exp (w s) := by
    field_simp
  rw [huv'] at huv
  set M := s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) with hM
  have hMs : M * Real.sqrt (4 * Real.pi) = s ^ 2 * (-φ s) * Real.exp (w s / 2) := by
    rw [hM]; field_simp
  have hM2 : M ^ 2 * (4 * Real.pi) = s ^ 4 * φ s ^ 2 * Real.exp (w s) := by
    rw [← hsq]
    calc M ^ 2 * Real.sqrt (4 * Real.pi) ^ 2 = (M * Real.sqrt (4 * Real.pi)) ^ 2 := by ring
      _ = s ^ 4 * φ s ^ 2 * Real.exp (w s / 2) ^ 2 := by rw [hMs]; ring
      _ = s ^ 4 * φ s ^ 2 * Real.exp (w s) := by rw [he2]
  by_contra hc
  have hc' : (1.1822265 : ℝ) ≤ M := not_lt.mp hc
  have hpi' := Real.pi_gt_d6
  have hM2' : (1.1822265 : ℝ) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (by norm_num) hc' 2
  nlinarith

end Checked.Math.BETail
