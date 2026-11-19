import Checked.Math.LEExistsRight
import Work.Math.LENCell
import Work.Math.LE4ExistsLeft
import Work.Math.LE4ExistsStart
import Work.Math.LE4ExistsData

/-!
# Lane–Emden index four: existence of a solution meeting every hypothesis of `laneEmden4_constants`

The singular piece on [0, 1/2] (`Work.Math.LE4ExistsLeft.exists_left`, Banach fixed point of the
Volterra map with the clamped fourth power) enters the input box of the first validated cell
(`Work.Math.LE4ExistsStart.startI`, the singular-start enclosure on [0, 1/2]). From its values at
1/2, Picard–Lindelöf gives a solution of the clamped field `Work.Math.LE4ExistsCell.Fc` on
[1/2, 16]; the kernel-checked cells of `Work.Math.LE4ExistsData` (`chainC`) apply to that flow and
keep it inside |θ| ≤ 1, |φ| ≤ 1, where the clamps are inactive, so it solves
θ'' + (2/ξ)θ' + θ⁴ = 0 there. The two pieces are glued at 1/2 (run 2026-11-19T0428Z; structure
of `Work/Math/LE2Exists.lean`, index two).
-/

namespace Work.Math.LE4Exists
open Set Filter Topology Checked.Sim.DuffingExists Work.Math.LE4ExistsCell Work.Math.LENCellQ

theorem lipFc {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 16) : LipschitzWith 8 (Fc t) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
  have hti : t⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ ht0 (by norm_num)]; linarith [ht.1]
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  simp only [Fc, Prod.dist_eq, Real.dist_eq]
  change _ ≤ (8 : ℝ) * _
  have hd1 : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
  have hv : |cl 1 p.2 - cl 1 q.2| ≤ |p.2 - q.2| := cl_sub _ _ _
  refine max_le (by nlinarith [abs_nonneg (p.2 - q.2)]) ?_
  have hu := abs_cl_le (by norm_num : (0 : ℝ) ≤ 1) p.1
  have hw := abs_cl_le (by norm_num : (0 : ℝ) ≤ 1) q.1
  have huw : |cl 1 p.1 - cl 1 q.1| ≤ |p.1 - q.1| := cl_sub _ _ _
  have hsq : |cl 1 p.1 ^ 4 - cl 1 q.1 ^ 4| ≤ 4 * |p.1 - q.1| := by
    have h := Work.Math.LENCell.pow_sub_le_slab 4 hu hw
    norm_num at h
    linarith
  have hre : -(2 / t * cl 1 p.2) - cl 1 p.1 ^ 4 - (-(2 / t * cl 1 q.2) - cl 1 q.1 ^ 4) =
      -(2 * t⁻¹ * (cl 1 p.2 - cl 1 q.2)) - (cl 1 p.1 ^ 4 - cl 1 q.1 ^ 4) := by ring
  rw [hre]
  have h1 : |2 * t⁻¹ * (cl 1 p.2 - cl 1 q.2)| ≤ 4 * |p.2 - q.2| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * t⁻¹)]
    nlinarith [abs_nonneg (cl 1 p.2 - cl 1 q.2)]
  calc |-(2 * t⁻¹ * (cl 1 p.2 - cl 1 q.2)) - (cl 1 p.1 ^ 4 - cl 1 q.1 ^ 4)|
      ≤ |2 * t⁻¹ * (cl 1 p.2 - cl 1 q.2)| + |cl 1 p.1 ^ 4 - cl 1 q.1 ^ 4| := by
        have := abs_sub (-(2 * t⁻¹ * (cl 1 p.2 - cl 1 q.2))) (cl 1 p.1 ^ 4 - cl 1 q.1 ^ 4)
        rwa [abs_neg] at this
    _ ≤ 4 * |p.2 - q.2| + 4 * |p.1 - q.1| := by linarith
    _ ≤ 8 * max |p.1 - q.1| |p.2 - q.2| := by nlinarith [abs_nonneg (p.1 - q.1)]

theorem normFc {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 16) (p : ℝ × ℝ) : ‖Fc t p‖ ≤ 5 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
  have hti : t⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ ht0 (by norm_num)]; linarith [ht.1]
  simp only [Fc, Prod.norm_def, Real.norm_eq_abs]
  have hv := abs_le.1 (abs_cl_le (by norm_num : (0 : ℝ) ≤ 1) p.2)
  have hu := abs_cl_le (by norm_num : (0 : ℝ) ≤ 1) p.1
  refine max_le ((abs_cl_le (by norm_num) _).trans (by norm_num)) ?_
  have hu4 : cl 1 p.1 ^ 4 ≤ 1 := by
    have : |cl 1 p.1| ^ 4 ≤ 1 ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hu 4
    rw [pow_abs, one_pow] at this; exact (le_abs_self _).trans this
  have hu4' : 0 ≤ cl 1 p.1 ^ 4 := by positivity
  set v := cl 1 p.2
  have hvt : |t⁻¹ * v| ≤ 2 := by
    rw [abs_mul, abs_of_pos hti0]
    have : |v| ≤ 1 := abs_le.2 hv
    nlinarith [abs_nonneg v]
  have hvt' := abs_le.1 hvt
  rw [abs_le, div_eq_mul_inv]
  constructor <;> nlinarith

theorem contFc (x : ℝ × ℝ) : ContinuousOn (fun t => Fc t x) (Icc (1 / 2 : ℝ) 16) := by
  unfold Fc
  refine continuousOn_const.prodMk ?_
  refine ContinuousOn.sub (ContinuousOn.neg ?_) continuousOn_const
  refine ContinuousOn.mul (continuousOn_const.div ?_ ?_) continuousOn_const
  · exact continuousOn_id
  · intro t ht; exact (show (0 : ℝ) < t by linarith [ht.1]).ne'

/-- The clamped flow on [1/2, 16] from any start. -/
theorem flow (x0 : ℝ × ℝ) : ∃ α : ℝ → ℝ × ℝ, α (1 / 2) = x0 ∧
    ∀ t ∈ Icc (1 / 2 : ℝ) 16, HasDerivWithinAt α (Fc t (α t)) (Icc (1 / 2) 16) t := by
  have hPL : IsPicardLindelof Fc (tmin := 1 / 2) (tmax := 16)
      ⟨1 / 2, by norm_num, by norm_num⟩ x0 78 0 5 8 :=
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
    (hθ : ∀ t ∈ Icc (1 / 2 : ℝ) 16, HasDerivWithinAt θ (cl 1 (φ t)) (Icc (1 / 2) 16) t)
    (hφ : ∀ t ∈ Icc (1 / 2 : ℝ) 16,
      HasDerivWithinAt φ (-(2 / t * cl 1 (φ t)) - cl 1 (θ t) ^ 4) (Icc (1 / 2) 16) t)
    (a0' : |θ (1 / 2) - (38412436093688850163/40000000000000000000 : ℝ)| ≤
      (101099311/31250000000000000000000000000 : ℝ))
    (b0' : |φ (1 / 2) - (-75623522615201319631/500000000000000000000 : ℝ)| ≤
      (101099311/31250000000000000000000000000 : ℝ)) :
    ∀ t ∈ Icc (1 / 2 : ℝ) 16, |θ t| ≤ 1 ∧ |φ t| ≤ 1 := by
  open Work.Math.LE4ExistsData in
  have a0 : |θ (c0.t0 : ℝ) - ((c0.pt.headD 0 : ℚ) : ℝ)| ≤ (c0.δ : ℝ) := by
    rw [c0_t0, c0_pt, c0_δ]; push_cast; norm_num at a0' ⊢; exact a0'
  open Work.Math.LE4ExistsData in
  have b0 : |φ (c0.t0 : ℝ) - ((c0.pp.headD 0 : ℚ) : ℝ)| ≤ (c0.δ : ℝ) := by
    rw [c0_t0, c0_pp, c0_δ]; push_cast; norm_num at b0' ⊢; exact b0'
  have sub : ∀ a b : ℚ, (1 / 2 : ℚ) ≤ a → b ≤ 16 → Icc (a : ℝ) b ⊆ Icc (1 / 2) 16 :=
    fun a b ha hb => Icc_subset_Icc
      (by have := (Rat.cast_le (K := ℝ)).2 ha; push_cast at this; exact this)
      (by have := (Rat.cast_le (K := ℝ)).2 hb; push_cast at this; exact this)
  open Work.Math.LE4ExistsData in
  have S0 := sub c0.t0 c15.t0 (by rw [s0_t0]) (by rw [s1_t0]; norm_num)
  open Work.Math.LE4ExistsData in
  have S1 := sub c15.t0 c30.t0 (by rw [s1_t0]; norm_num) (by rw [s2_t0]; norm_num)
  open Work.Math.LE4ExistsData in
  have S2 := sub c30.t0 c45.t0 (by rw [s2_t0]; norm_num) (by rw [s3_t0]; norm_num)
  open Work.Math.LE4ExistsData in
  have S3 := sub c45.t0 c60.t0 (by rw [s3_t0]; norm_num) (by rw [s4_t0]; norm_num)
  open Work.Math.LE4ExistsData in
  have S4 := sub c60.t0 c75.t0 (by rw [s4_t0]; norm_num) (by rw [s5_t0]; norm_num)
  open Work.Math.LE4ExistsData in
  have S5 := sub c75.t0 c90.t0 (by rw [s5_t0]; norm_num) (by rw [s6_t0]; norm_num)
  open Work.Math.LE4ExistsData in
  have S6 := sub c90.t0 c105.t0 (by rw [s6_t0]; norm_num) (by rw [s7_t0]; norm_num)
  open Work.Math.LE4ExistsData in
  have S7 := sub c105.t0 c120.t0 (by rw [s7_t0]; norm_num) (by rw [s8_t0]; norm_num)
  open Work.Math.LE4ExistsData in
  have S8 := sub c120.t0 c135.t0 (by rw [s8_t0]; norm_num) (by rw [s9_t0]; norm_num)
  open Work.Math.LE4ExistsData in
  have S9 := sub c135.t0 c150.t0 (by rw [s9_t0]; norm_num) (by rw [s10_t0]; norm_num)
  open Work.Math.LE4ExistsData in
  have S10 := sub c150.t0 c165.t0 (by rw [s10_t0]; norm_num) (by rw [s11_t0]; norm_num)
  open Work.Math.LE4ExistsData in
  have S11 := sub c165.t0 c180.t0 (by rw [s11_t0]; norm_num) (by rw [s12_t0]; norm_num)
  open Work.Math.LE4ExistsData in
  have S12 := sub c180.t0 c182.t0 (by rw [s12_t0]; norm_num) (by rw [c182_t0])
  obtain ⟨-, i1, a1, b1⟩ := chainC_gen _ _ _ Work.Math.LE4ExistsData.seg0_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S0 ht)) (fun t ht => hφ t (S0 ht)) S0 a0 b0
  obtain ⟨-, i2, a2, b2⟩ := chainC_gen _ _ _ Work.Math.LE4ExistsData.seg1_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S1 ht)) (fun t ht => hφ t (S1 ht)) S1 a1 b1
  obtain ⟨-, i3, a3, b3⟩ := chainC_gen _ _ _ Work.Math.LE4ExistsData.seg2_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S2 ht)) (fun t ht => hφ t (S2 ht)) S2 a2 b2
  obtain ⟨-, i4, a4, b4⟩ := chainC_gen _ _ _ Work.Math.LE4ExistsData.seg3_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S3 ht)) (fun t ht => hφ t (S3 ht)) S3 a3 b3
  obtain ⟨-, i5, a5, b5⟩ := chainC_gen _ _ _ Work.Math.LE4ExistsData.seg4_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S4 ht)) (fun t ht => hφ t (S4 ht)) S4 a4 b4
  obtain ⟨-, i6, a6, b6⟩ := chainC_gen _ _ _ Work.Math.LE4ExistsData.seg5_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S5 ht)) (fun t ht => hφ t (S5 ht)) S5 a5 b5
  obtain ⟨-, i7, a7, b7⟩ := chainC_gen _ _ _ Work.Math.LE4ExistsData.seg6_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S6 ht)) (fun t ht => hφ t (S6 ht)) S6 a6 b6
  obtain ⟨-, i8, a8, b8⟩ := chainC_gen _ _ _ Work.Math.LE4ExistsData.seg7_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S7 ht)) (fun t ht => hφ t (S7 ht)) S7 a7 b7
  obtain ⟨-, i9, a9, b9⟩ := chainC_gen _ _ _ Work.Math.LE4ExistsData.seg8_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S8 ht)) (fun t ht => hφ t (S8 ht)) S8 a8 b8
  obtain ⟨-, i10, a10, b10⟩ := chainC_gen _ _ _ Work.Math.LE4ExistsData.seg9_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S9 ht)) (fun t ht => hφ t (S9 ht)) S9 a9 b9
  obtain ⟨-, i11, a11, b11⟩ := chainC_gen _ _ _ Work.Math.LE4ExistsData.seg10_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S10 ht)) (fun t ht => hφ t (S10 ht)) S10 a10 b10
  obtain ⟨-, i12, a12, b12⟩ := chainC_gen _ _ _ Work.Math.LE4ExistsData.seg11_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S11 ht)) (fun t ht => hφ t (S11 ht)) S11 a11 b11
  obtain ⟨-, i13, -, -⟩ := chainC_gen _ _ _ Work.Math.LE4ExistsData.seg12_ok (θ := θ) (φ := φ)
    (fun t ht => hθ t (S12 ht)) (fun t ht => hφ t (S12 ht)) S12 a12 b12
  have all := icc_glue (icc_glue (icc_glue (icc_glue (icc_glue (icc_glue (icc_glue (icc_glue (icc_glue (icc_glue (icc_glue (icc_glue i1 i2) i3) i4) i5) i6) i7) i8) i9) i10) i11) i12) i13
  rw [Work.Math.LE4ExistsData.s0_t0, Work.Math.LE4ExistsData.c182_t0] at all
  push_cast at all
  intro t ht
  exact all t (by norm_num at ht ⊢; exact ht)

/-- Gluing two one-sided derivatives at 1/2. -/
theorem glue {fL fR d : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 16) (heq : fL (1 / 2) = fR (1 / 2))
    (hL : x ≤ 1 / 2 → HasDerivWithinAt fL (d x) (Icc 0 (1 / 2)) x)
    (hR : 1 / 2 ≤ x → HasDerivWithinAt fR (d x) (Icc (1 / 2) 16) x) :
    HasDerivWithinAt (fun y => if y ≤ 1 / 2 then fL y else fR y) (d x) (Icc 0 16) x := by
  set F : ℝ → ℝ := fun y => if y ≤ 1 / 2 then fL y else fR y with hF
  have eL : EqOn F fL (Icc 0 (1 / 2)) := fun y hy => by rw [hF]; exact if_pos hy.2
  have eR : EqOn F fR (Icc (1 / 2) 16) := fun y hy => by
    rcases eq_or_lt_of_le hy.1 with h | h
    · subst h; rw [hF]; exact (if_pos le_rfl).trans heq
    · rw [hF]; exact if_neg (not_le.2 h)
  have hL' : x ≤ 1 / 2 → HasDerivWithinAt F (d x) (Icc 0 (1 / 2)) x := fun h =>
    (hL h).congr eL (eL ⟨hx.1, h⟩)
  have hR' : 1 / 2 ≤ x → HasDerivWithinAt F (d x) (Icc (1 / 2) 16) x := fun h =>
    (hR h).congr eR (eR ⟨h, hx.2⟩)
  rcases lt_trichotomy x (1 / 2) with h | h | h
  · refine (hL' h.le).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Iio (1 / 2), isOpen_Iio, h, fun y hy => ⟨hy.2.1, le_of_lt hy.1⟩⟩)
  · have hu : Icc (0 : ℝ) 16 = Icc 0 (1 / 2) ∪ Icc (1 / 2) 16 :=
      (Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)).symm
    rw [hu]
    exact (hL' h.le).union (hR' h.ge)
  · refine (hR' h.le).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Ioi (1 / 2), isOpen_Ioi, h, fun y hy => ⟨le_of_lt hy.1, hy.2.2⟩⟩)

/-- The right piece: a solution of the index-four equation on [1/2, 16] from the left piece's values. -/
theorem exists_right (θ₀ φ₀ : ℝ)
    (a0 : |θ₀ - (38412436093688850163/40000000000000000000 : ℝ)| ≤
      (101099311/31250000000000000000000000000 : ℝ))
    (b0 : |φ₀ - (-75623522615201319631/500000000000000000000 : ℝ)| ≤
      (101099311/31250000000000000000000000000 : ℝ)) :
    ∃ θ φ : ℝ → ℝ, θ (1 / 2) = θ₀ ∧ φ (1 / 2) = φ₀ ∧
      ∀ t ∈ Icc (1 / 2 : ℝ) 16, HasDerivWithinAt θ (φ t) (Icc (1 / 2) 16) t ∧
        HasDerivWithinAt φ (-(2 / t * φ t) - θ t ^ 4) (Icc (1 / 2) 16) t := by
  obtain ⟨α, h0, hα⟩ := flow (θ₀, φ₀)
  have hθ : ∀ t ∈ Icc (1 / 2 : ℝ) 16,
      HasDerivWithinAt (fun r => (α r).1) (cl 1 (α t).2) (Icc (1 / 2) 16) t := fun t ht => by
    have := Checked.Math.LEExistsRight.fst_derivW (hα t ht)
    simpa [Fc] using this
  have hφ : ∀ t ∈ Icc (1 / 2 : ℝ) 16, HasDerivWithinAt (fun r => (α r).2)
      (-(2 / t * cl 1 (α t).2) - cl 1 (α t).1 ^ 4) (Icc (1 / 2) 16) t := fun t ht => by
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

/-- There exist θ, φ with θ differentiable within [0, 16] with derivative φ, φ continuous at 0,
φ' = −(2/ξ)φ − θ⁴ on (0, 16] and θ(0) = 1: the hypotheses of the index-four Lane–Emden headline
`Work.Math.LaneEmden4.laneEmden4_constants` are satisfied together. -/
theorem exists_solution : ∃ θ φ : ℝ → ℝ,
    (∀ ξ ∈ Icc (0 : ℝ) 16, HasDerivWithinAt θ (φ ξ) (Icc 0 16) ξ) ∧
    ContinuousWithinAt φ (Icc 0 16) 0 ∧
    (∀ ξ ∈ Ioc (0 : ℝ) 16, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 4) (Icc 0 16) ξ) ∧
    θ 0 = 1 := by
  obtain ⟨θL, φL, h0, hcφ, -, -, hdθ, hdφ⟩ := Work.Math.LE4ExistsLeft.exists_left
  obtain ⟨-, a0, b0⟩ := Work.Math.LE4ExistsStart.startI hdθ hcφ.continuousWithinAt hdφ h0
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
  · have e : φ =ᶠ[𝓝[Icc 0 16] 0] φL := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))]
        with y hy using φl y (le_of_lt hy)
    exact (hcφ.continuousWithinAt).congr_of_eventuallyEq e (φl 0 (by norm_num))
  · have hξ' : ξ ∈ Icc (0 : ℝ) 16 := Ioc_subset_Icc_self hξ
    exact glue (d := fun y => -(2 / y * φ y) - θ y ^ 4) hξ' hφR.symm
      (fun h => by
        simp only [φl ξ h, θl ξ h]; exact hdφ ξ ⟨hξ.1, h⟩)
      (fun h => by
        simp only [φr ξ h, θr ξ h]; exact (hR ξ ⟨h, hξ.2⟩).2)

end Work.Math.LE4Exists
