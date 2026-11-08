import Checked.Math.LEExistsRight
import Work.Math.LE2ExistsLeft
import Work.Math.LE2ExistsStart
import Work.Math.LE2ExistsData

/-!
# Lane–Emden index two: existence of a solution meeting every hypothesis of `laneEmden2_constants`

The singular piece on [0, 1/2] (`Work.Math.LE2ExistsLeft.exists_left`, Banach fixed point of the
Volterra map with the clamped square) enters the input box of the first validated cell
(`Work.Math.LE2ExistsStart.startI`, the singular-start enclosure on [0, 1/2]). From its values at
1/2, Picard–Lindelöf gives a solution of the clamped field `Work.Math.LE2ExistsCell.Fc` on
[1/2, 5]; the kernel-checked cells of `Work.Math.LE2ExistsData` (`chainC`) apply to that flow and
keep it inside |θ| ≤ 1, |φ| ≤ 1, where the clamps are inactive, so it solves
θ'' + (2/ξ)θ' + θ² = 0 there. The two pieces are glued at 1/2 (run 2026-11-08T0228Z; structure
of `Checked/Math/LEExists.lean`, index three).
-/

namespace Work.Math.LE2Exists
open Set Filter Topology Checked.Sim.DuffingExists Work.Math.LE2ExistsCell Work.Math.LENCellQ

theorem lipFc {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 5) : LipschitzWith 6 (Fc t) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
  have hti : t⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ ht0 (by norm_num)]; linarith [ht.1]
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  simp only [Fc, Prod.dist_eq, Real.dist_eq]
  change _ ≤ (6 : ℝ) * _
  have hd1 : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
  have hv : |cl 1 p.2 - cl 1 q.2| ≤ |p.2 - q.2| := cl_sub _ _ _
  refine max_le (by nlinarith [abs_nonneg (p.2 - q.2)]) ?_
  have hu := abs_cl_le (by norm_num : (0 : ℝ) ≤ 1) p.1
  have hw := abs_cl_le (by norm_num : (0 : ℝ) ≤ 1) q.1
  have huw : |cl 1 p.1 - cl 1 q.1| ≤ |p.1 - q.1| := cl_sub _ _ _
  have hsq : |cl 1 p.1 ^ 2 - cl 1 q.1 ^ 2| ≤ 2 * |p.1 - q.1| := by
    have hfac : cl 1 p.1 ^ 2 - cl 1 q.1 ^ 2 = (cl 1 p.1 - cl 1 q.1) * (cl 1 p.1 + cl 1 q.1) := by ring
    rw [hfac, abs_mul]
    have : |cl 1 p.1 + cl 1 q.1| ≤ 2 := (abs_add_le _ _).trans (by linarith)
    nlinarith [abs_nonneg (cl 1 p.1 - cl 1 q.1), abs_nonneg (cl 1 p.1 + cl 1 q.1)]
  have hre : -(2 / t * cl 1 p.2) - cl 1 p.1 ^ 2 - (-(2 / t * cl 1 q.2) - cl 1 q.1 ^ 2) =
      -(2 * t⁻¹ * (cl 1 p.2 - cl 1 q.2)) - (cl 1 p.1 ^ 2 - cl 1 q.1 ^ 2) := by ring
  rw [hre]
  have h1 : |2 * t⁻¹ * (cl 1 p.2 - cl 1 q.2)| ≤ 4 * |p.2 - q.2| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * t⁻¹)]
    nlinarith [abs_nonneg (cl 1 p.2 - cl 1 q.2)]
  calc |-(2 * t⁻¹ * (cl 1 p.2 - cl 1 q.2)) - (cl 1 p.1 ^ 2 - cl 1 q.1 ^ 2)|
      ≤ |2 * t⁻¹ * (cl 1 p.2 - cl 1 q.2)| + |cl 1 p.1 ^ 2 - cl 1 q.1 ^ 2| := by
        have := abs_sub (-(2 * t⁻¹ * (cl 1 p.2 - cl 1 q.2))) (cl 1 p.1 ^ 2 - cl 1 q.1 ^ 2)
        rwa [abs_neg] at this
    _ ≤ 4 * |p.2 - q.2| + 2 * |p.1 - q.1| := by linarith
    _ ≤ 6 * max |p.1 - q.1| |p.2 - q.2| := by nlinarith [abs_nonneg (p.1 - q.1)]

theorem normFc {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 5) (p : ℝ × ℝ) : ‖Fc t p‖ ≤ 5 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
  have hti : t⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ ht0 (by norm_num)]; linarith [ht.1]
  simp only [Fc, Prod.norm_def, Real.norm_eq_abs]
  have hv := abs_le.1 (abs_cl_le (by norm_num : (0 : ℝ) ≤ 1) p.2)
  have hu := abs_cl_le (by norm_num : (0 : ℝ) ≤ 1) p.1
  refine max_le ((abs_cl_le (by norm_num) _).trans (by norm_num)) ?_
  have hu2 : cl 1 p.1 ^ 2 ≤ 1 := by
    have : |cl 1 p.1| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hu 2
    rw [sq_abs] at this; linarith
  have hu2' : 0 ≤ cl 1 p.1 ^ 2 := sq_nonneg _
  set v := cl 1 p.2
  have hvt : |t⁻¹ * v| ≤ 2 := by
    rw [abs_mul, abs_of_pos hti0]
    have : |v| ≤ 1 := abs_le.2 hv
    nlinarith [abs_nonneg v]
  have hvt' := abs_le.1 hvt
  rw [abs_le, div_eq_mul_inv]
  constructor <;> nlinarith

theorem contFc (x : ℝ × ℝ) : ContinuousOn (fun t => Fc t x) (Icc (1 / 2 : ℝ) 5) := by
  unfold Fc
  refine continuousOn_const.prodMk ?_
  refine ContinuousOn.sub (ContinuousOn.neg ?_) continuousOn_const
  refine ContinuousOn.mul (continuousOn_const.div ?_ ?_) continuousOn_const
  · exact continuousOn_id
  · intro t ht; exact (show (0 : ℝ) < t by linarith [ht.1]).ne'

/-- The clamped flow on [1/2, 5] from any start. -/
theorem flow (x0 : ℝ × ℝ) : ∃ α : ℝ → ℝ × ℝ, α (1 / 2) = x0 ∧
    ∀ t ∈ Icc (1 / 2 : ℝ) 5, HasDerivWithinAt α (Fc t (α t)) (Icc (1 / 2) 5) t := by
  have hPL : IsPicardLindelof Fc (tmin := 1 / 2) (tmax := 5)
      ⟨1 / 2, by norm_num, by norm_num⟩ x0 23 0 5 6 :=
    { lipschitzOnWith := fun t ht => (lipFc ht).lipschitzOnWith
      continuousOn := fun x _ => contFc x
      norm_le := fun t ht p _ => by
        have := normFc ht p; exact_mod_cast this
      mul_max_le := by
        simp only [NNReal.coe_ofNat, NNReal.coe_zero, sub_zero]
        norm_num }
  obtain ⟨α, h0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, h0, hα⟩

/-- The kernel-checked cells keep the clamped flow from the certified start box inside the clamps. -/
theorem inside {θ φ : ℝ → ℝ}
    (hθ : ∀ t ∈ Icc (1 / 2 : ℝ) 5, HasDerivWithinAt θ (cl 1 (φ t)) (Icc (1 / 2) 5) t)
    (hφ : ∀ t ∈ Icc (1 / 2 : ℝ) 5,
      HasDerivWithinAt φ (-(2 / t * cl 1 (φ t)) - cl 1 (θ t) ^ 2) (Icc (1 / 2) 5) t)
    (a0' : |θ (1 / 2) - (9593527158033827/10000000000000000 : ℝ)| ≤
      (5452979271857/200000000000000000000000000000 : ℝ))
    (b0' : |φ (1 / 2) - (-1585989754744529/10000000000000000 : ℝ)| ≤
      (5452979271857/200000000000000000000000000000 : ℝ)) :
    ∀ t ∈ Icc (1 / 2 : ℝ) 5, |θ t| ≤ 1 ∧ |φ t| ≤ 1 := by
  open Work.Math.LE2ExistsData in
  have a0 : |θ (c0.t0 : ℝ) - ((c0.pt.headD 0 : ℚ) : ℝ)| ≤ (c0.δ : ℝ) := by
    rw [c0_t0, c0_pt, c0_δ]; push_cast; norm_num at a0' ⊢; exact a0'
  open Work.Math.LE2ExistsData in
  have b0 : |φ (c0.t0 : ℝ) - ((c0.pp.headD 0 : ℚ) : ℝ)| ≤ (c0.δ : ℝ) := by
    rw [c0_t0, c0_pp, c0_δ]; push_cast; norm_num at b0' ⊢; exact b0'
  have sub : ∀ a b : ℚ, (1 / 2 : ℚ) ≤ a → b ≤ 5 → Icc (a : ℝ) b ⊆ Icc (1 / 2) 5 :=
    fun a b ha hb => Icc_subset_Icc
      (by have := (Rat.cast_le (K := ℝ)).2 ha; push_cast at this; exact this)
      (by have := (Rat.cast_le (K := ℝ)).2 hb; push_cast at this; exact this)
  open Work.Math.LE2ExistsData in
  have S0 := sub c0.t0 c15.t0 (by rw [s0_t0]) (by rw [s1_t0]; norm_num)
  open Work.Math.LE2ExistsData in
  have S1 := sub c15.t0 c30.t0 (by rw [s1_t0]; norm_num) (by rw [s2_t0]; norm_num)
  open Work.Math.LE2ExistsData in
  have S2 := sub c30.t0 c45.t0 (by rw [s2_t0]; norm_num) (by rw [s3_t0]; norm_num)
  open Work.Math.LE2ExistsData in
  have S3 := sub c45.t0 c60.t0 (by rw [s3_t0]; norm_num) (by rw [s4_t0]; norm_num)
  open Work.Math.LE2ExistsData in
  have S4 := sub c60.t0 c72.t0 (by rw [s4_t0]; norm_num) (by rw [c72_t0])
  obtain ⟨-, i1, a1, b1⟩ := chainC_gen _ _ _ Work.Math.LE2ExistsData.seg0_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S0 ht)) (fun t ht => hφ t (S0 ht)) S0 a0 b0
  obtain ⟨-, i2, a2, b2⟩ := chainC_gen _ _ _ Work.Math.LE2ExistsData.seg1_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S1 ht)) (fun t ht => hφ t (S1 ht)) S1 a1 b1
  obtain ⟨-, i3, a3, b3⟩ := chainC_gen _ _ _ Work.Math.LE2ExistsData.seg2_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S2 ht)) (fun t ht => hφ t (S2 ht)) S2 a2 b2
  obtain ⟨-, i4, a4, b4⟩ := chainC_gen _ _ _ Work.Math.LE2ExistsData.seg3_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S3 ht)) (fun t ht => hφ t (S3 ht)) S3 a3 b3
  obtain ⟨-, i5, -, -⟩ := chainC_gen _ _ _ Work.Math.LE2ExistsData.seg4_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S4 ht)) (fun t ht => hφ t (S4 ht)) S4 a4 b4
  have all := icc_glue (icc_glue (icc_glue (icc_glue i1 i2) i3) i4) i5
  rw [Work.Math.LE2ExistsData.s0_t0, Work.Math.LE2ExistsData.c72_t0] at all
  push_cast at all
  intro t ht
  exact all t (by norm_num at ht ⊢; exact ht)

/-- Gluing two one-sided derivatives at 1/2. -/
theorem glue {fL fR d : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 5) (heq : fL (1 / 2) = fR (1 / 2))
    (hL : x ≤ 1 / 2 → HasDerivWithinAt fL (d x) (Icc 0 (1 / 2)) x)
    (hR : 1 / 2 ≤ x → HasDerivWithinAt fR (d x) (Icc (1 / 2) 5) x) :
    HasDerivWithinAt (fun y => if y ≤ 1 / 2 then fL y else fR y) (d x) (Icc 0 5) x := by
  set F : ℝ → ℝ := fun y => if y ≤ 1 / 2 then fL y else fR y with hF
  have eL : EqOn F fL (Icc 0 (1 / 2)) := fun y hy => by rw [hF]; exact if_pos hy.2
  have eR : EqOn F fR (Icc (1 / 2) 5) := fun y hy => by
    rcases eq_or_lt_of_le hy.1 with h | h
    · subst h; rw [hF]; exact (if_pos le_rfl).trans heq
    · rw [hF]; exact if_neg (not_le.2 h)
  have hL' : x ≤ 1 / 2 → HasDerivWithinAt F (d x) (Icc 0 (1 / 2)) x := fun h =>
    (hL h).congr eL (eL ⟨hx.1, h⟩)
  have hR' : 1 / 2 ≤ x → HasDerivWithinAt F (d x) (Icc (1 / 2) 5) x := fun h =>
    (hR h).congr eR (eR ⟨h, hx.2⟩)
  rcases lt_trichotomy x (1 / 2) with h | h | h
  · refine (hL' h.le).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Iio (1 / 2), isOpen_Iio, h, fun y hy => ⟨hy.2.1, le_of_lt hy.1⟩⟩)
  · have hu : Icc (0 : ℝ) 5 = Icc 0 (1 / 2) ∪ Icc (1 / 2) 5 :=
      (Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)).symm
    rw [hu]
    exact (hL' h.le).union (hR' h.ge)
  · refine (hR' h.le).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Ioi (1 / 2), isOpen_Ioi, h, fun y hy => ⟨le_of_lt hy.1, hy.2.2⟩⟩)

/-- The right piece: a solution of the index-two equation on [1/2, 5] from the left piece's values. -/
theorem exists_right (θ₀ φ₀ : ℝ)
    (a0 : |θ₀ - (9593527158033827/10000000000000000 : ℝ)| ≤
      (5452979271857/200000000000000000000000000000 : ℝ))
    (b0 : |φ₀ - (-1585989754744529/10000000000000000 : ℝ)| ≤
      (5452979271857/200000000000000000000000000000 : ℝ)) :
    ∃ θ φ : ℝ → ℝ, θ (1 / 2) = θ₀ ∧ φ (1 / 2) = φ₀ ∧
      ∀ t ∈ Icc (1 / 2 : ℝ) 5, HasDerivWithinAt θ (φ t) (Icc (1 / 2) 5) t ∧
        HasDerivWithinAt φ (-(2 / t * φ t) - θ t ^ 2) (Icc (1 / 2) 5) t := by
  obtain ⟨α, h0, hα⟩ := flow (θ₀, φ₀)
  have hθ : ∀ t ∈ Icc (1 / 2 : ℝ) 5,
      HasDerivWithinAt (fun r => (α r).1) (cl 1 (α t).2) (Icc (1 / 2) 5) t := fun t ht => by
    have := Checked.Math.LEExistsRight.fst_derivW (hα t ht)
    simpa [Fc] using this
  have hφ : ∀ t ∈ Icc (1 / 2 : ℝ) 5, HasDerivWithinAt (fun r => (α r).2)
      (-(2 / t * cl 1 (α t).2) - cl 1 (α t).1 ^ 2) (Icc (1 / 2) 5) t := fun t ht => by
    have := Checked.Math.LEExistsRight.snd_derivW (hα t ht)
    simpa [Fc] using this
  have hin := inside (θ := fun r => (α r).1) (φ := fun r => (α r).2) hθ hφ
    (by simp only [h0]; exact a0) (by simp only [h0]; exact b0)
  refine ⟨fun t => (α t).1, fun t => (α t).2, by show (α (1 / 2)).1 = θ₀; rw [h0],
    by show (α (1 / 2)).2 = φ₀; rw [h0], fun t ht => ⟨?_, ?_⟩⟩
  · have := hθ t ht
    rwa [cl_of_abs_le (hin t ht).2] at this
  · have := hφ t ht
    rwa [cl_of_abs_le (hin t ht).2, cl_of_abs_le (hin t ht).1] at this

/-- There exist θ, φ with θ differentiable within [0, 5] with derivative φ, φ continuous at 0,
φ' = −(2/ξ)φ − θ² on (0, 5] and θ(0) = 1: the hypotheses of the index-two Lane–Emden headline
`Work.Math.LaneEmden2.laneEmden2_constants` are satisfied together. -/
theorem exists_solution : ∃ θ φ : ℝ → ℝ,
    (∀ ξ ∈ Icc (0 : ℝ) 5, HasDerivWithinAt θ (φ ξ) (Icc 0 5) ξ) ∧
    ContinuousWithinAt φ (Icc 0 5) 0 ∧
    (∀ ξ ∈ Ioc (0 : ℝ) 5, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 2) (Icc 0 5) ξ) ∧
    θ 0 = 1 := by
  obtain ⟨θL, φL, h0, hcφ, -, -, hdθ, hdφ⟩ := Work.Math.LE2ExistsLeft.exists_left
  obtain ⟨-, a0, b0⟩ := Work.Math.LE2ExistsStart.startI hdθ hcφ.continuousWithinAt hdφ h0
  obtain ⟨θR, φR, hθR, hφR, hR⟩ := exists_right _ _ a0 b0
  set θ : ℝ → ℝ := fun y => if y ≤ 1 / 2 then θL y else θR y with hθ
  set φ : ℝ → ℝ := fun y => if y ≤ 1 / 2 then φL y else φR y with hφ
  have θl : ∀ y, y ≤ 1 / 2 → θ y = θL y := fun y h => by rw [hθ]; exact if_pos h
  have φl : ∀ y, y ≤ 1 / 2 → φ y = φL y := fun y h => by rw [hφ]; exact if_pos h
  have θr : ∀ y, 1 / 2 ≤ y → θ y = θR y := fun y h => by
    rcases eq_or_lt_of_le h with h | h
    · subst h; rw [hθ]; exact (if_pos le_rfl).trans hθR.symm
    · rw [hθ]; exact if_neg (not_le.2 h)
  have φr : ∀ y, 1 / 2 ≤ y → φ y = φR y := fun y h => by
    rcases eq_or_lt_of_le h with h | h
    · subst h; rw [hφ]; exact (if_pos le_rfl).trans hφR.symm
    · rw [hφ]; exact if_neg (not_le.2 h)
  refine ⟨θ, φ, fun ξ hξ => ?_, ?_, fun ξ hξ => ?_, (θl 0 (by norm_num)).trans h0⟩
  · exact glue hξ hθR.symm
      (fun h => by rw [φl ξ h]; exact hdθ ξ ⟨hξ.1, h⟩)
      (fun h => by rw [φr ξ h]; exact (hR ξ ⟨h, hξ.2⟩).1)
  · have e : φ =ᶠ[𝓝[Icc 0 5] 0] φL := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))]
        with y hy using φl y (le_of_lt hy)
    exact (hcφ.continuousWithinAt).congr_of_eventuallyEq e (φl 0 (by norm_num))
  · have hξ' : ξ ∈ Icc (0 : ℝ) 5 := Ioc_subset_Icc_self hξ
    exact glue (d := fun y => -(2 / y * φ y) - θ y ^ 2) hξ' hφR.symm
      (fun h => by
        simp only [φl ξ h, θl ξ h]; exact hdφ ξ ⟨hξ.1, h⟩)
      (fun h => by
        simp only [φr ξ h, θr ξ h]; exact (hR ξ ⟨h, hξ.2⟩).2)

end Work.Math.LE2Exists
