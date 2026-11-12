import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Order.IntermediateValue
import Checked.FSRev.RAssemble
import Checked.FalknerSkan.NegWallShearRows
import Checked.FSRev.RSeventeenOver
import Checked.FSRev.RSeventeenSlow
import Checked.FSRev.RSeventeenTube
import Checked.FSRev.REighteenOver
import Checked.FSRev.REighteenSlow
import Checked.FSRev.REighteenTube
import Checked.FSRev.RNineteenOver
import Checked.FSRev.RNineteenSlow
import Checked.FSRev.RNineteenTube

/-! Falkner–Skan with adverse pressure gradient at the last three rows of an attached wall-shear table read blind, reversed-flow branch: a solution with negative wall shear that approaches the edge value faster than every exponential, and two solutions with different wall shear in that class. Module `NegReversedRows`, promoted from `Work/FalknerSkan/ReversedRows.lean`. -/

namespace Checked.FalknerSkan.NegReversedRows

open Set Filter Topology

theorem seventeen_sqrtK_pos : 0 < Real.sqrt (100 / 17 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem seventeen_hK : (-1 / (100 / 17 : ℝ)) = -17 / 100 := by norm_num

theorem seventeen_lo_bound : (-0.1142272391 : ℝ) < -(277041748310817 / 1000000000000000) / Real.sqrt (100 / 17) := by
  have hs := seventeen_sqrtK_pos
  have h : (277041748310817 / 1000000000000000) / (0.1142272391 : ℝ) < Real.sqrt (100 / 17 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem seventeen_hi_bound : -(55408349652039 / 200000000000000) / Real.sqrt (100 / 17) < (-0.1142272390 : ℝ) := by
  have hs := seventeen_sqrtK_pos
  have h : Real.sqrt (100 / 17 : ℝ) < (55408349652039 / 200000000000000) / (0.1142272390 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

/-- Falkner–Skan with β = −17/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−0.1142272391 < q(0) < −0.1142272390. -/
theorem fs_neg_reversed_wall_shear_17_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-17 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.1142272391 < q 0 ∧ q 0 < -0.1142272390 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssemble.core_rev (K := 100 / 17) (by norm_num) (by norm_num)
      Checked.FSRev.RSeventeenOver.chain Checked.FSRev.RSeventeenSlow.chain Checked.FSRev.RSeventeenTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← seventeen_hK]; exact a3 η hη
  · have e : (-277041748310817 / 1000000000000000 : ℝ) / Real.sqrt (100 / 17) = -(277041748310817 / 1000000000000000) / Real.sqrt (100 / 17) := by ring
    linarith [seventeen_lo_bound]
  · have e : (-55408349652039 / 200000000000000 : ℝ) / Real.sqrt (100 / 17) = -(55408349652039 / 200000000000000) / Real.sqrt (100 / 17) := by ring
    linarith [seventeen_hi_bound]

/-- Falkner–Skan with β = −17/100: there are solutions (f, p, q) and (f₂, p₂, q₂) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, p → 1 and −1 ≤ p ≤ 1 on [0, ∞), with
q(0) ≠ q₂(0), such that, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, and,
for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p₂ η) ≤ q₂ η`. -/
theorem fs_neg_wall_shear_17_two_decay :
    ∃ f p q f₂ p₂ q₂ : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-17 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - (-17 / 100) * (1 - p₂ η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ f₂ 0 = 0 ∧ p₂ 0 = 0 ∧
      Tendsto p atTop (𝓝 1) ∧ Tendsto p₂ atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧ (∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧ (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) ∧
      q 0 ≠ q₂ 0 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ := fs_neg_reversed_wall_shear_17_exists
  obtain ⟨f₂, p₂, q₂, b1, b2, b3, b4, b5, b6, b7, b8⟩ := Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_17_exists_decay
  have h00 : (0 : ℝ) ∈ Ici (0 : ℝ) := Set.mem_Ici.2 le_rfl
  have hmono : MonotoneOn p₂ (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := q₂) (convex_Ici 0)
      (HasDerivWithinAt.continuousOn (fun x hx => b2 x hx)) (fun x hx => ?_) (fun x hx => ?_)
    · exact (b2 x (interior_subset hx)).mono interior_subset
    · exact (b7 x (interior_subset hx)).le
  have hp₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1 := by
    intro η hη
    have h0 : p₂ 0 ≤ p₂ η := hmono h00 hη hη
    have h1 : p₂ η ≤ 1 := ge_of_tendsto b6
      (eventually_atTop.2 ⟨η, fun t ht => hmono hη (le_trans hη ht) ht⟩)
    constructor <;> linarith
  refine ⟨f, p, q, f₂, p₂, q₂, a1, a2, a3, b1, b2, b3, a4, a5, b4, b5, a6, b6, a7, hp₂, a8, b8, ?_⟩
  have := b7 0 h00
  intro h; rw [h] at w2; linarith

theorem eighteen_sqrtK_pos : 0 < Real.sqrt (50 / 9 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem eighteen_hK : (-1 / (50 / 9 : ℝ)) = -18 / 100 := by norm_num

theorem eighteen_lo_bound : (-0.0976920602 : ℝ) < -(2878279925141 / 12500000000000) / Real.sqrt (50 / 9) := by
  have hs := eighteen_sqrtK_pos
  have h : (2878279925141 / 12500000000000) / (0.0976920602 : ℝ) < Real.sqrt (50 / 9 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem eighteen_hi_bound : -(230262393923393 / 1000000000000000) / Real.sqrt (50 / 9) < (-0.0976920601 : ℝ) := by
  have hs := eighteen_sqrtK_pos
  have h : Real.sqrt (50 / 9 : ℝ) < (230262393923393 / 1000000000000000) / (0.0976920601 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

/-- Falkner–Skan with β = −18/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−0.0976920602 < q(0) < −0.0976920601. -/
theorem fs_neg_reversed_wall_shear_18_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-18 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.0976920602 < q 0 ∧ q 0 < -0.0976920601 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssemble.core_rev (K := 50 / 9) (by norm_num) (by norm_num)
      Checked.FSRev.REighteenOver.chain Checked.FSRev.REighteenSlow.chain Checked.FSRev.REighteenTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← eighteen_hK]; exact a3 η hη
  · have e : (-2878279925141 / 12500000000000 : ℝ) / Real.sqrt (50 / 9) = -(2878279925141 / 12500000000000) / Real.sqrt (50 / 9) := by ring
    linarith [eighteen_lo_bound]
  · have e : (-230262393923393 / 1000000000000000 : ℝ) / Real.sqrt (50 / 9) = -(230262393923393 / 1000000000000000) / Real.sqrt (50 / 9) := by ring
    linarith [eighteen_hi_bound]

/-- Falkner–Skan with β = −18/100: there are solutions (f, p, q) and (f₂, p₂, q₂) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, p → 1 and −1 ≤ p ≤ 1 on [0, ∞), with
q(0) ≠ q₂(0), such that, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, and,
for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p₂ η) ≤ q₂ η`. -/
theorem fs_neg_wall_shear_18_two_decay :
    ∃ f p q f₂ p₂ q₂ : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-18 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - (-18 / 100) * (1 - p₂ η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ f₂ 0 = 0 ∧ p₂ 0 = 0 ∧
      Tendsto p atTop (𝓝 1) ∧ Tendsto p₂ atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧ (∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧ (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) ∧
      q 0 ≠ q₂ 0 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ := fs_neg_reversed_wall_shear_18_exists
  obtain ⟨f₂, p₂, q₂, b1, b2, b3, b4, b5, b6, b7, b8⟩ := Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_18_exists_decay
  have h00 : (0 : ℝ) ∈ Ici (0 : ℝ) := Set.mem_Ici.2 le_rfl
  have hmono : MonotoneOn p₂ (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := q₂) (convex_Ici 0)
      (HasDerivWithinAt.continuousOn (fun x hx => b2 x hx)) (fun x hx => ?_) (fun x hx => ?_)
    · exact (b2 x (interior_subset hx)).mono interior_subset
    · exact (b7 x (interior_subset hx)).le
  have hp₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1 := by
    intro η hη
    have h0 : p₂ 0 ≤ p₂ η := hmono h00 hη hη
    have h1 : p₂ η ≤ 1 := ge_of_tendsto b6
      (eventually_atTop.2 ⟨η, fun t ht => hmono hη (le_trans hη ht) ht⟩)
    constructor <;> linarith
  refine ⟨f, p, q, f₂, p₂, q₂, a1, a2, a3, b1, b2, b3, a4, a5, b4, b5, a6, b6, a7, hp₂, a8, b8, ?_⟩
  have := b7 0 h00
  intro h; rw [h] at w2; linarith

theorem nineteen_sqrtK_pos : 0 < Real.sqrt (100 / 19 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem nineteen_hK : (-1 / (100 / 19 : ℝ)) = -19 / 100 := by norm_num

theorem nineteen_lo_bound : (-0.0713359061 : ℝ) < -(32731158463379 / 200000000000000) / Real.sqrt (100 / 19) := by
  have hs := nineteen_sqrtK_pos
  have h : (32731158463379 / 200000000000000) / (0.0713359061 : ℝ) < Real.sqrt (100 / 19 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem nineteen_hi_bound : -(163655792267063 / 1000000000000000) / Real.sqrt (100 / 19) < (-0.0713359060 : ℝ) := by
  have hs := nineteen_sqrtK_pos
  have h : Real.sqrt (100 / 19 : ℝ) < (163655792267063 / 1000000000000000) / (0.0713359060 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

/-- Falkner–Skan with β = −19/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−0.0713359061 < q(0) < −0.0713359060. -/
theorem fs_neg_reversed_wall_shear_19_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-19 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.0713359061 < q 0 ∧ q 0 < -0.0713359060 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssemble.core_rev (K := 100 / 19) (by norm_num) (by norm_num)
      Checked.FSRev.RNineteenOver.chain Checked.FSRev.RNineteenSlow.chain Checked.FSRev.RNineteenTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← nineteen_hK]; exact a3 η hη
  · have e : (-32731158463379 / 200000000000000 : ℝ) / Real.sqrt (100 / 19) = -(32731158463379 / 200000000000000) / Real.sqrt (100 / 19) := by ring
    linarith [nineteen_lo_bound]
  · have e : (-163655792267063 / 1000000000000000 : ℝ) / Real.sqrt (100 / 19) = -(163655792267063 / 1000000000000000) / Real.sqrt (100 / 19) := by ring
    linarith [nineteen_hi_bound]

/-- Falkner–Skan with β = −19/100: there are solutions (f, p, q) and (f₂, p₂, q₂) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, p → 1 and −1 ≤ p ≤ 1 on [0, ∞), with
q(0) ≠ q₂(0), such that, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, and,
for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p₂ η) ≤ q₂ η`. -/
theorem fs_neg_wall_shear_19_two_decay :
    ∃ f p q f₂ p₂ q₂ : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-19 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - (-19 / 100) * (1 - p₂ η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ f₂ 0 = 0 ∧ p₂ 0 = 0 ∧
      Tendsto p atTop (𝓝 1) ∧ Tendsto p₂ atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧ (∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧ (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) ∧
      q 0 ≠ q₂ 0 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ := fs_neg_reversed_wall_shear_19_exists
  obtain ⟨f₂, p₂, q₂, b1, b2, b3, b4, b5, b6, b7, b8⟩ := Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_19_exists_decay
  have h00 : (0 : ℝ) ∈ Ici (0 : ℝ) := Set.mem_Ici.2 le_rfl
  have hmono : MonotoneOn p₂ (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := q₂) (convex_Ici 0)
      (HasDerivWithinAt.continuousOn (fun x hx => b2 x hx)) (fun x hx => ?_) (fun x hx => ?_)
    · exact (b2 x (interior_subset hx)).mono interior_subset
    · exact (b7 x (interior_subset hx)).le
  have hp₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1 := by
    intro η hη
    have h0 : p₂ 0 ≤ p₂ η := hmono h00 hη hη
    have h1 : p₂ η ≤ 1 := ge_of_tendsto b6
      (eventually_atTop.2 ⟨η, fun t ht => hmono hη (le_trans hη ht) ht⟩)
    constructor <;> linarith
  refine ⟨f, p, q, f₂, p₂, q₂, a1, a2, a3, b1, b2, b3, a4, a5, b4, b5, a6, b6, a7, hp₂, a8, b8, ?_⟩
  have := b7 0 h00
  intro h; rw [h] at w2; linarith

end Checked.FalknerSkan.NegReversedRows
