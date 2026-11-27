import Mathlib
import Readings.projection
import ComparatorChallenges.PettyProjectionVolume
import ComparatorChallenges.ProjectionCounterexample
import ComparatorChallenges.ProjectionVolume

/-!
# Closure of the readings of family O65 (projection bodies) against the frozen statements

Frozen statements: `OAI.PettyProjection.petty_projection_volume`,
`OAI.Paper092.product_counterexample` and
`OAI.ProjectionCounterexample.universal_simplex_upper_bound_false`
(the three challenges use disjoint namespaces, so one module imports all of them).

What is closed here.

* Bridges between the four definitions of the shadow volume: Lebesgue measure of the
  hyperplane `u⊥` (Petty, product challenge, readers A and B), the Euclidean Hausdorff
  measure `μHE[d-1]` of the shadow inside the ambient space (counterexample challenge;
  proved equal, via `InnerProductSpace.euclideanHausdorffMeasure_eq_volume`), and reader C's
  rescaled unnormalized Hausdorff measure. Reader C's rescaling constant is correct
  mathematically, but its agreement with Mathlib's normalizing factor of `μHE` is the
  isodiametric inequality, absent from Mathlib (a TODO of
  `Mathlib.Geometry.Euclidean.Volume.Measure`); it is isolated as the hypothesis
  `HausdorffNormalization`.
* The projection body of the product challenge (all directions, homogeneous brightness)
  equals the unit-direction body of the Petty challenge.
* Reader B's predicate `IsProjBody K P` (a convex body with the prescribed support function)
  forces `P` to be the frozen projection body (separation theorem).
* Reader A, Petty theorem: equivalent to the frozen Petty statement.
* Reader B, Petty theorem: equivalent to the frozen statement together with the existence
  of the projection body as a convex body with the prescribed support function (an extra
  claim of reader B, classical, not in Mathlib, not in the frozen statement).
* Reader C, Petty theorem: equivalent to the frozen statement under `HausdorffNormalization`.
* The product witness is a convex body (proved), the three readers' product sets equal the
  frozen witness, the simplex constants agree.
* Reader A, product theorem: equivalent to the frozen product statement.
* Reader B, product theorem: equivalent to the frozen product statement together with the
  existence of the projection body of the product.
* Reader C, product theorem: equivalent to the frozen product statement under
  `HausdorffNormalization`.
* Counterexample challenge: implied by the frozen product statement together with the
  simplex value of the normalized projection volume in dimension twenty (stated in the paper
  as verified there, formalized by nobody); the same then holds starting from reader A.
* The corollaries on exponential excess (readers A, B, C) have no frozen counterpart
  (disclosed in the scope document).
-/

open MeasureTheory Set
open scoped RealInnerProductSpace NNReal ENNReal

namespace TargetO.Projection

/-! ## Common bridges -/

section Common

open OAI.PettyProjection

/-- The open link for reader C: Mathlib's normalizing factor of the Euclidean Hausdorff
measure in dimension `k` is `κ_k / 2^k` (isodiametric inequality, not in Mathlib). -/
def HausdorffNormalization : Prop :=
  ∀ k : ℕ, ((Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin k)))
      (Measure.hausdorffMeasure (k : ℝ)) : ℝ≥0) : ℝ) = ReaderC.kappa k / 2 ^ k

theorem finrank_perp {n : ℕ} {u : Space n} (hu : ‖u‖ = 1) :
    Module.finrank ℝ (perpendicular u) = n - 1 := by
  have h1 := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {u})
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
  rw [finrank_span_singleton hu0, finrank_euclideanSpace_fin] at h1
  unfold perpendicular
  omega

theorem image_proj_eq {n : ℕ} (u : Space n) (K : Set (Space n)) :
    (perpendicular u).starProjection '' K =
      Subtype.val '' ((perpendicular u).orthogonalProjectionOnto '' K) := by
  rw [image_image]; rfl

theorem readerA_projVol_eq {n : ℕ} (K : Set (Space n)) (u : Space n) :
    ReaderA.projVol K u = shadowVolume K u := rfl

theorem readerB_projVol_eq {n : ℕ} (K : Set (Space n)) (u : Space n) :
    ReaderB.projVol K u = shadowVolume K u := rfl

theorem paper092_projVol_eq {n : ℕ} (K : Set (Space n)) (u : Space n) :
    (OAI.Paper092.projectionVolume K u).toReal = shadowVolume K u := rfl

/-- Reader C's projection `x - ⟪x,u⟫ u` is the orthogonal projection onto `u⊥`. -/
theorem readerC_projPerp_eq {n : ℕ} {u : Space n} (hu : ‖u‖ = 1) (x : Space n) :
    ReaderC.projPerp u x = (perpendicular u).starProjection x := by
  rw [perpendicular, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ hu, ReaderC.projPerp, real_inner_comm]

/-- Reader C's shadow volume equals the frozen one, under `HausdorffNormalization`. -/
theorem readerC_shadowVol_eq (hH : HausdorffNormalization) {n : ℕ} (hn : 1 ≤ n)
    (K : Set (Space n)) {u : Space n} (hu : ‖u‖ = 1) :
    ReaderC.shadowVol K u = shadowVolume K u := by
  have hcast : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hn, Nat.cast_one]
  have himg : ReaderC.projPerp u '' K =
      Subtype.val '' ((perpendicular u).orthogonalProjectionOnto '' K) := by
    rw [← image_proj_eq]; exact image_congr (fun x _ => readerC_projPerp_eq hu x)
  have hvol : (volume : Measure (perpendicular u)) = Measure.euclideanHausdorffMeasure (n - 1) := by
    rw [← finrank_perp hu]; exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume.symm
  unfold ReaderC.shadowVol
  rw [hcast, himg, isometry_subtype_coe.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg _)),
    ← hH (n - 1), shadowVolume, measureReal_def, hvol, Measure.euclideanHausdorffMeasure_def,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]

/-- The counterexample challenge's shadow volume (Euclidean Hausdorff measure of the shadow
in the ambient space) equals the Petty challenge's (Lebesgue measure of the hyperplane). -/
theorem pc_projectionVolume_eq {n : ℕ} (K : Set (Space n)) {u : Space n} (hu : ‖u‖ = 1) :
    OAI.ProjectionCounterexample.projectionVolume K u = shadowVolume K u := by
  unfold OAI.ProjectionCounterexample.projectionVolume OAI.ProjectionCounterexample.project
  have h := image_proj_eq u K
  unfold perpendicular at h
  rw [h, isometry_subtype_coe.euclideanHausdorffMeasure_image, shadowVolume, measureReal_def,
    ← InnerProductSpace.euclideanHausdorffMeasure_eq_volume, finrank_perp hu]
  rfl

theorem readerA_projBody_eq {n : ℕ} (K : Set (Space n)) :
    ReaderA.projBody K = projectionBody K := by
  ext x
  exact forall_congr' fun u => imp_congr_right fun _ =>
    Iff.of_eq (congrArg₂ (· ≤ ·) (real_inner_comm u x) rfl)

theorem readerC_projBody_eq (hH : HausdorffNormalization) {n : ℕ} (hn : 1 ≤ n)
    (K : Set (Space n)) : ReaderC.projBody K = projectionBody K := by
  ext x
  simp only [ReaderC.projBody, projectionBody, mem_ofPred_eq, ReaderC.unitSphere,
    mem_sphere_zero_iff_norm]
  exact forall_congr' fun u => imp_congr_right fun hu =>
    Iff.of_eq (congrArg₂ (· ≤ ·) (real_inner_comm u x) (readerC_shadowVol_eq hH hn K hu))

theorem pc_projBody_eq {n : ℕ} (K : Set (Space n)) :
    OAI.ProjectionCounterexample.projectionBody K = projectionBody K := by
  ext x
  exact forall_congr' fun u => imp_congr_right fun hu =>
    Iff.of_eq (congrArg₂ (· ≤ ·) rfl (pc_projectionVolume_eq K hu))

theorem normalHyperplane_smul {n : ℕ} (u : Space n) {c : ℝ} (hc : c ≠ 0) :
    OAI.Paper092.normalHyperplane (c • u) = OAI.Paper092.normalHyperplane u := by
  unfold OAI.Paper092.normalHyperplane
  rw [Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]

theorem paper092_projVol_smul {n : ℕ} (K : Set (Space n)) (u : Space n) {c : ℝ} (hc : c ≠ 0) :
    OAI.Paper092.projectionVolume K (c • u) = OAI.Paper092.projectionVolume K u := by
  have key : ∀ S T : Submodule ℝ (Space n), S = T →
      (volume : Measure S) (S.orthogonalProjectionOnto '' K) =
        (volume : Measure T) (T.orthogonalProjectionOnto '' K) := by
    rintro S T rfl; rfl
  exact key _ _ (normalHyperplane_smul u hc)

/-- The product challenge's projection body (homogeneous brightness, all directions) is the
Petty challenge's (unit directions). -/
theorem paper092_projBody_eq {n : ℕ} (K : Set (Space n)) :
    OAI.Paper092.projectionBody K = projectionBody K := by
  ext x
  simp only [OAI.Paper092.projectionBody, OAI.Paper092.brightness, projectionBody, mem_ofPred_eq]
  constructor
  · intro h u hu
    have := h u
    rwa [hu, one_mul, paper092_projVol_eq] at this
  · intro h u
    by_cases hu : u = 0
    · simp [hu]
    · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      obtain ⟨v, hv⟩ : ∃ v : Space n, v = ‖u‖⁻¹ • u := ⟨_, rfl⟩
      have hvn : ‖v‖ = 1 := by rw [hv, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
      have h1 := h v hvn
      rw [← paper092_projVol_eq, hv, paper092_projVol_smul K u (inv_ne_zero hpos.ne'),
        real_inner_smul_left] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at h2

/-- Reader B's projection-body predicate determines the frozen projection body. -/
theorem readerB_isProjBody_eq {n : ℕ} {K P : Set (Space n)} (hP : ReaderB.IsProjBody K P) :
    P = projectionBody K := by
  obtain ⟨⟨hPc, hPconv, hPint⟩, hsupp⟩ := hP
  ext x
  constructor
  · intro hx u hu
    exact (hsupp u hu).2 ⟨x, hx, rfl⟩
  · intro hx
    by_contra hxP
    obtain ⟨f, c, hfP, hfx⟩ := geometric_hahn_banach_closed_point hPconv hPc.isClosed hxP
    obtain ⟨w, hw⟩ : ∃ w : Space n, w = (InnerProductSpace.toDual ℝ (Space n)).symm f :=
      ⟨_, rfl⟩
    have hfw : ∀ y, f y = ⟪w, y⟫ := fun y => by rw [hw, InnerProductSpace.toDual_symm_apply]
    obtain ⟨p, hp⟩ := hPint.mono interior_subset
    have hw0 : w ≠ 0 := by
      intro h0
      have h1 := hfP p hp
      rw [hfw, h0, inner_zero_left] at h1 hfx
      linarith
    have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    obtain ⟨v, hv⟩ : ∃ v : Space n, v = ‖w‖⁻¹ • w := ⟨_, rfl⟩
    have hvn : ‖v‖ = 1 := by rw [hv, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
    obtain ⟨⟨y, hyP, hy⟩, -⟩ := hsupp v hvn
    have h1 : ⟪v, x⟫ ≤ ⟪v, y⟫ := (hx v hvn).trans_eq hy.symm
    have h2 := hfP y hyP
    rw [hfw] at h2 hfx
    rw [hv, real_inner_smul_left, real_inner_smul_left] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 hpos.le
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, one_mul] at h3
    linarith

theorem readerC_ellipsoid_iff {n : ℕ} (K : Set (Space n)) :
    (∃ (a : Space n) (T : Space n ≃L[ℝ] Space n),
        K = (fun x => a + T x) '' Metric.closedBall 0 1) ↔ IsEllipsoid K := by
  constructor
  · rintro ⟨a, T, hK⟩
    exact ⟨a, T.toLinearEquiv, hK⟩
  · rintro ⟨a, T, hK⟩
    exact ⟨a, T.toContinuousLinearEquiv, hK⟩

end Common

/-! ## Petty's projection-volume theorem -/

section Petty

open OAI.PettyProjection

theorem readerA_ratio_eq {n : ℕ} (K : Set (Space n)) :
    ReaderA.vol (ReaderA.projBody K) / ReaderA.vol K ^ (n - 1) = projectionRatio K := by
  rw [readerA_projBody_eq]; rfl

/-- Reader A's Petty theorem is equivalent to the frozen statement. -/
theorem readerA_petty_iff :
    (type_of% @ReaderA.reading_paper1_theorem_1_1) ↔
      (type_of% @OAI.PettyProjection.petty_projection_volume) := by
  constructor
  · intro h n hn K hK
    have := h n hn K hK
    rw [readerA_ratio_eq] at this
    exact this
  · intro h n hn K hK
    rw [readerA_ratio_eq]
    exact h n hn K hK

/-- The extra claim of reader B: the projection body exists as a convex body with the
prescribed support function. -/
def ReaderBProjBodyExists : Prop :=
  ∀ n : ℕ, 4 ≤ n → ∀ K : Set (Space n), ReaderB.IsConvexBody K → ∃ P, ReaderB.IsProjBody K P

/-- Reader B's Petty theorem is equivalent to the frozen statement together with the
existence of the projection body. -/
theorem readerB_petty_iff :
    (type_of% @ReaderB.readingPetty) ↔
      (type_of% @OAI.PettyProjection.petty_projection_volume) ∧ ReaderBProjBodyExists := by
  constructor
  · intro h
    refine ⟨fun n hn K hK => ?_, fun n hn K hK => (h n hn K hK).1⟩
    obtain ⟨⟨P, hP⟩, hall⟩ := h n hn K hK
    have := hall P hP
    rw [readerB_isProjBody_eq hP] at this
    exact this
  · rintro ⟨h, hex⟩ n hn K hK
    refine ⟨hex n hn K hK, fun P hP => ?_⟩
    rw [readerB_isProjBody_eq hP]
    exact h n hn K hK

/-- The direction that matters for reader B without the existence claim. -/
theorem frozen_petty_to_readerB_bounds (h : type_of% @OAI.PettyProjection.petty_projection_volume)
    (n : ℕ) (hn : 4 ≤ n) (K : Set (Space n)) (hK : ReaderB.IsConvexBody K)
    (P : Set (Space n)) (hP : ReaderB.IsProjBody K P) :
    (ReaderB.kappa (n - 1) ^ n * ReaderB.kappa n ^ ((2 : ℤ) - n) ≤ ReaderB.ratio n K P) ∧
      (ReaderB.ratio n K P = ReaderB.kappa (n - 1) ^ n * ReaderB.kappa n ^ ((2 : ℤ) - n) ↔
        ∃ (a : ReaderB.E n) (T : ReaderB.E n ≃ₗ[ℝ] ReaderB.E n),
          K = (fun x => a + T x) '' Metric.closedBall (0 : ReaderB.E n) 1) := by
  rw [readerB_isProjBody_eq hP]
  exact h n hn K hK

theorem readerC_R_eq (hH : HausdorffNormalization) {n : ℕ} (hn : 1 ≤ n) (K : Set (Space n)) :
    ReaderC.R K = projectionRatio K := by
  unfold ReaderC.R projectionRatio
  rw [readerC_projBody_eq hH hn K]; rfl

/-- Reader C's Petty theorem is equivalent to the frozen statement, given the Hausdorff
normalization (the one open link). -/
theorem readerC_petty_iff (hH : HausdorffNormalization) :
    (type_of% @ReaderC.reading_O65_p1_thm11) ↔
      (type_of% @OAI.PettyProjection.petty_projection_volume) := by
  constructor
  · intro h n hn K hK
    obtain ⟨h1, h2⟩ := h n hn K hK
    rw [readerC_R_eq hH (by omega) K] at h1 h2
    exact ⟨h1, h2.trans (readerC_ellipsoid_iff K)⟩
  · intro h n hn K hK
    obtain ⟨h1, h2⟩ := h n hn K hK
    rw [readerC_R_eq hH (by omega) K]
    exact ⟨h1, h2.trans (readerC_ellipsoid_iff K).symm⟩

end Petty

/-! ## The product of two ten-dimensional simplices -/

section Product

open OAI.Paper092

def L1 : Euclidean 20 →ₗ[ℝ] Euclidean 10 where
  toFun := firstBlock
  map_add' x y := by ext i; simp [firstBlock]
  map_smul' c x := by ext i; simp [firstBlock]

def L2 : Euclidean 20 →ₗ[ℝ] Euclidean 10 where
  toFun := secondBlock
  map_add' x y := by ext i; simp [secondBlock]
  map_smul' c x := by ext i; simp [secondBlock]

def J : (Euclidean 10 × Euclidean 10) →ₗ[ℝ] Euclidean 20 where
  toFun p := WithLp.toLp 2 (Fin.append (fun i => p.1 i) (fun i => p.2 i))
  map_add' p q := by
    ext j; refine Fin.addCases (m := 10) (n := 10) (fun i => ?_) (fun i => ?_) j <;> simp [-Fin.natAdd_eq_addNat]
  map_smul' c p := by
    ext j; refine Fin.addCases (m := 10) (n := 10) (fun i => ?_) (fun i => ?_) j <;> simp [-Fin.natAdd_eq_addNat]

theorem J_blocks (x : Euclidean 20) : J (firstBlock x, secondBlock x) = x := by
  ext j; refine Fin.addCases (m := 10) (n := 10) (fun i => ?_) (fun i => ?_) j <;> simp [J, firstBlock, secondBlock, -Fin.natAdd_eq_addNat]

theorem simplex_compact (d : ℕ) : IsCompact (standardSimplex d) :=
  ((Set.finite_range _).insert 0).isCompact_convexHull (𝕜 := ℝ)

theorem simplex_interior (d : ℕ) : (interior (standardSimplex d)).Nonempty := by
  rw [standardSimplex, interior_convexHull_nonempty_iff_affineSpan_eq_top,
    affineSpan_insert_zero]
  have hspan : Submodule.span ℝ (Set.range fun i : Fin d => EuclideanSpace.single i (1 : ℝ)) = ⊤ := by
    have h := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.span_eq
    have hf : ⇑(EuclideanSpace.basisFun (Fin d) ℝ).toBasis =
        fun i : Fin d => EuclideanSpace.single i (1 : ℝ) :=
      funext fun i => by simp
    rwa [hf] at h
  rw [hspan]
  refine eq_top_iff.mpr fun x _ => ?_
  exact Submodule.mem_toAffineSubspace.mpr Submodule.mem_top

theorem witness_eq : productWitness = L1 ⁻¹' standardSimplex 10 ∩ L2 ⁻¹' standardSimplex 10 :=
  rfl

theorem witness_convex : Convex ℝ productWitness := by
  rw [witness_eq]
  exact ((convex_convexHull ℝ _).linear_preimage L1).inter
    ((convex_convexHull ℝ _).linear_preimage L2)

theorem witness_compact : IsCompact productWitness := by
  refine (((simplex_compact 10).prod (simplex_compact 10)).image
    J.continuous_of_finiteDimensional).of_isClosed_subset ?_ ?_
  · rw [witness_eq]
    exact ((simplex_compact 10).isClosed.preimage L1.continuous_of_finiteDimensional).inter
      ((simplex_compact 10).isClosed.preimage L2.continuous_of_finiteDimensional)
  · intro x hx
    exact ⟨(firstBlock x, secondBlock x), ⟨hx.1, hx.2⟩, J_blocks x⟩

theorem zero_mem_simplex (d : ℕ) : (0 : Euclidean d) ∈ standardSimplex d :=
  subset_convexHull ℝ _ (mem_insert _ _)

theorem single_mem_simplex {d : ℕ} (i : Fin d) :
    EuclideanSpace.single i (1 : ℝ) ∈ standardSimplex d :=
  subset_convexHull ℝ _ (mem_insert_of_mem _ ⟨i, rfl⟩)

theorem simplex20_subset : standardSimplex 20 ⊆ productWitness := by
  refine convexHull_min ?_ witness_convex
  rintro x (rfl | ⟨j, rfl⟩)
  · exact ⟨by rw [show firstBlock 0 = 0 from L1.map_zero]; exact zero_mem_simplex 10,
      by rw [show secondBlock 0 = 0 from L2.map_zero]; exact zero_mem_simplex 10⟩
  · refine Fin.addCases (m := 10) (n := 10) (fun i => ⟨?_, ?_⟩) (fun i => ⟨?_, ?_⟩) j
    · convert single_mem_simplex i using 1
      ext k; simp [firstBlock, Fin.ext_iff, -Fin.natAdd_eq_addNat]
    · convert zero_mem_simplex 10 using 1
      ext k; have := i.isLt; have := k.isLt
      simp [secondBlock, Fin.ext_iff, -Fin.natAdd_eq_addNat]; all_goals omega
    · convert zero_mem_simplex 10 using 1
      ext k; have := i.isLt; have := k.isLt
      simp [firstBlock, Fin.ext_iff, -Fin.natAdd_eq_addNat]; all_goals omega
    · convert single_mem_simplex i using 1
      ext k; simp [secondBlock, Fin.ext_iff, -Fin.natAdd_eq_addNat]

/-- The first conjunct of the frozen product statement, proved. -/
theorem witness_body : IsCompact productWitness ∧ Convex ℝ productWitness ∧
    (interior productWitness).Nonempty :=
  ⟨witness_compact, witness_convex, (simplex_interior 20).mono (interior_mono simplex20_subset)⟩

theorem readerA_K20_eq : ReaderA.K20 = productWitness := rfl

theorem readerB_set_eq : ReaderB.prodSimplex10 = productWitness := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    have h1 : firstBlock x = a := by ext i; exact (h i).1
    have h2 : secondBlock x = b := by ext i; exact (h i).2
    exact ⟨h1 ▸ ha, h2 ▸ hb⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, h1, _, h2, fun i => ⟨rfl, rfl⟩⟩

theorem toLp_mem_simplex {d : ℕ} (f : Fin d → ℝ) :
    WithLp.toLp 2 f ∈ standardSimplex d ↔ f ∈ ReaderC.simplexPi d := by
  have himg : (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap '' standardSimplex d =
      ReaderC.simplexPi d := by
    rw [standardSimplex, LinearMap.image_convexHull, ReaderC.simplexPi, image_insert_eq,
      map_zero, ← range_comp]
    rfl
  rw [← himg]
  constructor
  · intro h; exact ⟨_, h, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact hy

theorem readerC_set_eq : ReaderC.prodSimplex = productWitness := by
  ext x
  simp only [ReaderC.prodSimplex, productWitness, firstBlock, secondBlock, mem_ofPred_eq,
    toLp_mem_simplex]

theorem simplexConstant_pos : 0 < simplexConstant 20 := by
  unfold simplexConstant; positivity

theorem readerA_c_eq : ReaderA.c 20 = simplexConstant 20 := by
  unfold ReaderA.c simplexConstant; push_cast; ring

theorem readerB_c_eq : ReaderB.cConst 20 = simplexConstant 20 := by
  unfold ReaderB.cConst simplexConstant; push_cast; ring

theorem readerC_c_eq : ReaderC.cD 20 = simplexConstant 20 := by
  unfold ReaderC.cD simplexConstant; push_cast; ring

theorem gt_of_one_lt {a b c : ℝ} (hc : 0 < c) (hb : 0 ≤ b) (h : 1 < a / b / c) : c * b < a := by
  rcases hb.eq_or_lt with hb0 | hbpos
  · rw [← hb0, div_zero, zero_div] at h; linarith
  · rw [lt_div_iff₀ hc, one_mul, lt_div_iff₀ hbpos] at h; linarith

theorem normalized_eq : normalizedProjectionVolume productWitness =
    (volume (projectionBody productWitness)).toReal / (volume productWitness).toReal ^ 19 := rfl

theorem arith : (121 * (Nat.choose 20 10 : ℝ)) / (21 * (2 : ℝ) ^ 20) = (22355476 : ℝ) / 22020096 := by
  rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
  norm_num [Nat.factorial]

/-- Reader A's product theorem is equivalent to the frozen product statement. -/
theorem readerA_product_iff :
    (type_of% @ReaderA.reading_paper2_theorem_1_1) ↔
      (type_of% @OAI.Paper092.product_counterexample) := by
  have hR : ReaderA.R 20 ReaderA.K20 = normalizedProjectionVolume productWitness := by
    unfold ReaderA.R
    rw [readerA_projBody_eq, ← paper092_projBody_eq, readerA_K20_eq]; rfl
  have hV : ReaderA.vol (ReaderA.projBody ReaderA.K20) =
      (volume (projectionBody productWitness)).toReal := by
    rw [readerA_projBody_eq, ← paper092_projBody_eq, readerA_K20_eq]; rfl
  have hK : ReaderA.vol ReaderA.K20 = (volume productWitness).toReal := by
    rw [readerA_K20_eq]; rfl
  rw [hR, readerA_c_eq, hV, hK]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨witness_body, h1, h1.trans h2, ?_, not_le.mp h4⟩
    rw [h1.trans h2]; norm_num
  · rintro ⟨-, h1, h2, -, h4⟩
    exact ⟨h1, h1.symm.trans h2, by norm_num, not_le.mpr h4⟩

/-- Reader B's product theorem is equivalent to the frozen product statement together with
the existence of the projection body of the product. -/
theorem readerB_product_iff :
    (type_of% @ReaderB.readingProduct) ↔
      (type_of% @OAI.Paper092.product_counterexample) ∧
        ∃ P, ReaderB.IsProjBody ReaderB.prodSimplex10 P := by
  have key : ∀ P, ReaderB.IsProjBody ReaderB.prodSimplex10 P →
      ReaderB.ratio 20 ReaderB.prodSimplex10 P = normalizedProjectionVolume productWitness := by
    intro P hP
    rw [readerB_isProjBody_eq hP, readerB_set_eq, ← paper092_projBody_eq]; rfl
  constructor
  · rintro ⟨hbody, ⟨P, hP⟩, hall⟩
    obtain ⟨h1, h2, h3⟩ := hall P hP
    rw [key P hP, readerB_c_eq] at h1 h3
    rw [readerB_set_eq] at hbody
    refine ⟨⟨hbody, h1, h1.trans h2, h3, ?_⟩, P, hP⟩
    exact gt_of_one_lt simplexConstant_pos (by positivity) h3
  · rintro ⟨⟨hbody, h1, h2, h3, -⟩, hex⟩
    refine ⟨readerB_set_eq ▸ hbody, hex, fun P hP => ?_⟩
    rw [key P hP, readerB_c_eq]
    exact ⟨h1, h1.symm.trans h2, h3⟩

theorem readerC_R_prod_eq (hH : HausdorffNormalization) :
    ReaderC.R ReaderC.prodSimplex = normalizedProjectionVolume productWitness := by
  unfold ReaderC.R
  rw [readerC_projBody_eq hH (by norm_num), ← paper092_projBody_eq, readerC_set_eq]; rfl

/-- Frozen product statement implies reader C's product theorem (given the Hausdorff
normalization). -/
theorem frozen_product_to_readerC (hH : HausdorffNormalization)
    (h : type_of% @OAI.Paper092.product_counterexample) :
    type_of% @ReaderC.reading_O65_p2_thm11 := by
  obtain ⟨-, h1, h2, h3, -⟩ := h
  rw [readerC_R_prod_eq hH, readerC_c_eq]
  exact ⟨h1, h2, h3⟩

/-- Reader C's product theorem implies the frozen product statement (given the Hausdorff
normalization). -/
theorem readerC_to_frozen_product (hH : HausdorffNormalization)
    (h : type_of% @ReaderC.reading_O65_p2_thm11) :
    type_of% @OAI.Paper092.product_counterexample := by
  rw [readerC_R_prod_eq hH, readerC_c_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨witness_body, h1, h2, h3,
    gt_of_one_lt simplexConstant_pos (by positivity) h3⟩

/-- Reader C's product theorem is equivalent to the frozen product statement, given the
Hausdorff normalization. -/
theorem readerC_product_iff (hH : HausdorffNormalization) :
    (type_of% @ReaderC.reading_O65_p2_thm11) ↔
      (type_of% @OAI.Paper092.product_counterexample) :=
  ⟨readerC_to_frozen_product hH, frozen_product_to_readerC hH⟩

end Product

/-! ## Failure of the simplex upper bound in dimension twenty -/

section Counterexample

open OAI.Paper092

theorem pc_ratio_eq {n : ℕ} (K : Set (Euclidean n)) :
    OAI.ProjectionCounterexample.ratio K = normalizedProjectionVolume K := by
  unfold OAI.ProjectionCounterexample.ratio normalizedProjectionVolume
    OAI.ProjectionCounterexample.bodyVolume
  rw [pc_projBody_eq, ← paper092_projBody_eq]

/-- The frozen product statement, together with the simplex value of the normalized
projection volume in dimension twenty (not formalized by anyone), implies the frozen
counterexample statement. -/
theorem frozen_product_to_pc (h : type_of% @OAI.Paper092.product_counterexample)
    (hsimplex : normalizedProjectionVolume (standardSimplex 20) = simplexConstant 20) :
    type_of% @OAI.ProjectionCounterexample.universal_simplex_upper_bound_false := by
  obtain ⟨hbody, -, -, h3, -⟩ := h
  intro hall
  have h1 := hall productWitness hbody
  rw [pc_ratio_eq, pc_ratio_eq] at h1
  have h2 : standardSimplex 20 = OAI.ProjectionCounterexample.simplex 20 := rfl
  rw [← h2, hsimplex] at h1
  rw [lt_div_iff₀ simplexConstant_pos, one_mul] at h3
  linarith

/-- The same from reader A's product theorem. -/
theorem readerA_to_pc (h : type_of% @ReaderA.reading_paper2_theorem_1_1)
    (hsimplex : normalizedProjectionVolume (standardSimplex 20) = simplexConstant 20) :
    type_of% @OAI.ProjectionCounterexample.universal_simplex_upper_bound_false :=
  frozen_product_to_pc (readerA_product_iff.mp h) hsimplex

end Counterexample

end TargetO.Projection

#print axioms TargetO.Projection.readerA_petty_iff
#print axioms TargetO.Projection.readerB_petty_iff
#print axioms TargetO.Projection.frozen_petty_to_readerB_bounds
#print axioms TargetO.Projection.readerC_petty_iff
#print axioms TargetO.Projection.witness_body
#print axioms TargetO.Projection.arith
#print axioms TargetO.Projection.readerA_product_iff
#print axioms TargetO.Projection.readerB_product_iff
#print axioms TargetO.Projection.frozen_product_to_readerC
#print axioms TargetO.Projection.readerC_to_frozen_product
#print axioms TargetO.Projection.readerC_product_iff
#print axioms TargetO.Projection.pc_projectionVolume_eq
#print axioms TargetO.Projection.frozen_product_to_pc
#print axioms TargetO.Projection.readerA_to_pc
