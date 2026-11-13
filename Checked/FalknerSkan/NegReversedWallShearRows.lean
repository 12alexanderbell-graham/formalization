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
import Checked.FSRev.RAssembleA
import Checked.FSRev.RFourOver
import Checked.FSRev.RFourSlow
import Checked.FSRev.RFourTube
import Checked.FSRev.RFiveOver
import Checked.FSRev.RFiveSlow
import Checked.FSRev.RFiveTube
import Checked.FSRev.RSixOver
import Checked.FSRev.RSixSlow
import Checked.FSRev.RSixTube
import Checked.FSRev.RSevenOver
import Checked.FSRev.RSevenSlow
import Checked.FSRev.RSevenTube
import Checked.FSRev.REightOver
import Checked.FSRev.REightSlow
import Checked.FSRev.REightTube
import Checked.FSRev.RNineOver
import Checked.FSRev.RNineSlow
import Checked.FSRev.RNineTube
import Checked.FSRev.RElevenOver
import Checked.FSRev.RElevenSlow
import Checked.FSRev.RElevenTube
import Checked.FSRev.RTwelveOver
import Checked.FSRev.RTwelveSlow
import Checked.FSRev.RTwelveTube
import Checked.FSRev.RThirteenOver
import Checked.FSRev.RThirteenSlow
import Checked.FSRev.RThirteenTube
import Checked.FSRev.RFourteenOver
import Checked.FSRev.RFourteenSlow
import Checked.FSRev.RFourteenTube
import Checked.FSRev.RFifteenOver
import Checked.FSRev.RFifteenSlow
import Checked.FSRev.RFifteenTube
import Checked.FSRev.RSixteenOver
import Checked.FSRev.RSixteenSlow
import Checked.FSRev.RSixteenTube

/-! Falkner–Skan with adverse pressure gradient at twelve rows of a reversed-flow wall-shear table read blind: for each row, a solution with negative wall shear that approaches the edge value faster than every exponential. Module `NegReversedWallShearRows`, promoted from `Work/FalknerSkan/ReversedTable.lean` and `Work/FalknerSkan/ReversedRows.lean`. -/

namespace Checked.FalknerSkan.NegReversedWallShearRows

open Set Filter Topology

theorem four_sqrtK_pos : 0 < Real.sqrt (25 / 1 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem four_hK : (-1 / (25 / 1 : ℝ)) = -4 / 100 := by norm_num

theorem four_lo_bound : (-0.0966367875 : ℝ) < -(120795984285739 / 250000000000000) / Real.sqrt (25 / 1) := by
  have hs := four_sqrtK_pos
  have h : (120795984285739 / 250000000000000) / (0.0966367875 : ℝ) < Real.sqrt (25 / 1 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem four_hi_bound : -(241591968510739 / 500000000000000) / Real.sqrt (25 / 1) < (-0.0966367874 : ℝ) := by
  have hs := four_sqrtK_pos
  have h : Real.sqrt (25 / 1 : ℝ) < (241591968510739 / 500000000000000) / (0.0966367874 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

/-- Falkner–Skan with β = −4/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−0.0966367875 < q(0) < −0.0966367874. -/
theorem fs_neg_reversed_wall_shear_4_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-4 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.0966367875 < q 0 ∧ q 0 < -0.0966367874 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssembleA.core_revA (K := 25 / 1) (by norm_num) (L := 7 / 4) (by norm_num) (by norm_num)
      Checked.FSRev.RFourOver.chain Checked.FSRev.RFourSlow.chain Checked.FSRev.RFourTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← four_hK]; exact a3 η hη
  · have e : (-120795984285739 / 250000000000000 : ℝ) / Real.sqrt (25 / 1) = -(120795984285739 / 250000000000000) / Real.sqrt (25 / 1) := by ring
    linarith [four_lo_bound]
  · have e : (-241591968510739 / 500000000000000 : ℝ) / Real.sqrt (25 / 1) = -(241591968510739 / 500000000000000) / Real.sqrt (25 / 1) := by ring
    linarith [four_hi_bound]

theorem five_sqrtK_pos : 0 < Real.sqrt (20 / 1 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem five_hK : (-1 / (20 / 1 : ℝ)) = -5 / 100 := by norm_num

theorem five_lo_bound : (-0.1082710833 : ℝ) < -(484203004481007 / 1000000000000000) / Real.sqrt (20 / 1) := by
  have hs := five_sqrtK_pos
  have h : (484203004481007 / 1000000000000000) / (0.1082710833 : ℝ) < Real.sqrt (20 / 1 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem five_hi_bound : -(30262687772493 / 62500000000000) / Real.sqrt (20 / 1) < (-0.1082710832 : ℝ) := by
  have hs := five_sqrtK_pos
  have h : Real.sqrt (20 / 1 : ℝ) < (30262687772493 / 62500000000000) / (0.1082710832 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

/-- Falkner–Skan with β = −5/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−0.1082710833 < q(0) < −0.1082710832. -/
theorem fs_neg_reversed_wall_shear_5_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-5 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.1082710833 < q 0 ∧ q 0 < -0.1082710832 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssembleA.core_revA (K := 20 / 1) (by norm_num) (L := 7 / 4) (by norm_num) (by norm_num)
      Checked.FSRev.RFiveOver.chain Checked.FSRev.RFiveSlow.chain Checked.FSRev.RFiveTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← five_hK]; exact a3 η hη
  · have e : (-484203004481007 / 1000000000000000 : ℝ) / Real.sqrt (20 / 1) = -(484203004481007 / 1000000000000000) / Real.sqrt (20 / 1) := by ring
    linarith [five_lo_bound]
  · have e : (-30262687772493 / 62500000000000 : ℝ) / Real.sqrt (20 / 1) = -(30262687772493 / 62500000000000) / Real.sqrt (20 / 1) := by ring
    linarith [five_hi_bound]

theorem six_sqrtK_pos : 0 < Real.sqrt (50 / 3 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem six_hK : (-1 / (50 / 3 : ℝ)) = -6 / 100 := by norm_num

theorem six_lo_bound : (-0.1179241111 : ℝ) < -(120355791860143 / 250000000000000) / Real.sqrt (50 / 3) := by
  have hs := six_sqrtK_pos
  have h : (120355791860143 / 250000000000000) / (0.1179241111 : ℝ) < Real.sqrt (50 / 3 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem six_hi_bound : -(96284633456113 / 200000000000000) / Real.sqrt (50 / 3) < (-0.1179241110 : ℝ) := by
  have hs := six_sqrtK_pos
  have h : Real.sqrt (50 / 3 : ℝ) < (96284633456113 / 200000000000000) / (0.1179241110 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

/-- Falkner–Skan with β = −6/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−0.1179241111 < q(0) < −0.1179241110. -/
theorem fs_neg_reversed_wall_shear_6_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-6 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.1179241111 < q 0 ∧ q 0 < -0.1179241110 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssembleA.core_revA (K := 50 / 3) (by norm_num) (L := 7 / 4) (by norm_num) (by norm_num)
      Checked.FSRev.RSixOver.chain Checked.FSRev.RSixSlow.chain Checked.FSRev.RSixTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← six_hK]; exact a3 η hη
  · have e : (-120355791860143 / 250000000000000 : ℝ) / Real.sqrt (50 / 3) = -(120355791860143 / 250000000000000) / Real.sqrt (50 / 3) := by ring
    linarith [six_lo_bound]
  · have e : (-96284633456113 / 200000000000000 : ℝ) / Real.sqrt (50 / 3) = -(96284633456113 / 200000000000000) / Real.sqrt (50 / 3) := by ring
    linarith [six_hi_bound]

theorem seven_sqrtK_pos : 0 < Real.sqrt (100 / 7 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem seven_hK : (-1 / (100 / 7 : ℝ)) = -7 / 100 := by norm_num

theorem seven_lo_bound : (-0.1258585318 : ℝ) < -(237850268118629 / 500000000000000) / Real.sqrt (100 / 7) := by
  have hs := seven_sqrtK_pos
  have h : (237850268118629 / 500000000000000) / (0.1258585318 : ℝ) < Real.sqrt (100 / 7 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem seven_hi_bound : -(1486564175373 / 3125000000000) / Real.sqrt (100 / 7) < (-0.1258585317 : ℝ) := by
  have hs := seven_sqrtK_pos
  have h : Real.sqrt (100 / 7 : ℝ) < (1486564175373 / 3125000000000) / (0.1258585317 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

/-- Falkner–Skan with β = −7/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−0.1258585318 < q(0) < −0.1258585317. -/
theorem fs_neg_reversed_wall_shear_7_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-7 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.1258585318 < q 0 ∧ q 0 < -0.1258585317 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssembleA.core_revA (K := 100 / 7) (by norm_num) (L := 7 / 4) (by norm_num) (by norm_num)
      Checked.FSRev.RSevenOver.chain Checked.FSRev.RSevenSlow.chain Checked.FSRev.RSevenTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← seven_hK]; exact a3 η hη
  · have e : (-237850268118629 / 500000000000000 : ℝ) / Real.sqrt (100 / 7) = -(237850268118629 / 500000000000000) / Real.sqrt (100 / 7) := by ring
    linarith [seven_lo_bound]
  · have e : (-1486564175373 / 3125000000000 : ℝ) / Real.sqrt (100 / 7) = -(1486564175373 / 3125000000000) / Real.sqrt (100 / 7) := by ring
    linarith [seven_hi_bound]

theorem eight_sqrtK_pos : 0 < Real.sqrt (25 / 2 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem eight_hK : (-1 / (25 / 2 : ℝ)) = -8 / 100 := by norm_num

theorem eight_lo_bound : (-0.1322276544 : ℝ) < -(233747677698637 / 500000000000000) / Real.sqrt (25 / 2) := by
  have hs := eight_sqrtK_pos
  have h : (233747677698637 / 500000000000000) / (0.1322276544 : ℝ) < Real.sqrt (25 / 2 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem eight_hi_bound : -(233747677645341 / 500000000000000) / Real.sqrt (25 / 2) < (-0.1322276543 : ℝ) := by
  have hs := eight_sqrtK_pos
  have h : Real.sqrt (25 / 2 : ℝ) < (233747677645341 / 500000000000000) / (0.1322276543 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

/-- Falkner–Skan with β = −8/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−0.1322276544 < q(0) < −0.1322276543. -/
theorem fs_neg_reversed_wall_shear_8_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-8 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.1322276544 < q 0 ∧ q 0 < -0.1322276543 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssembleA.core_revA (K := 25 / 2) (by norm_num) (L := 7 / 4) (by norm_num) (by norm_num)
      Checked.FSRev.REightOver.chain Checked.FSRev.REightSlow.chain Checked.FSRev.REightTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← eight_hK]; exact a3 η hη
  · have e : (-233747677698637 / 500000000000000 : ℝ) / Real.sqrt (25 / 2) = -(233747677698637 / 500000000000000) / Real.sqrt (25 / 2) := by ring
    linarith [eight_lo_bound]
  · have e : (-233747677645341 / 500000000000000 : ℝ) / Real.sqrt (25 / 2) = -(233747677645341 / 500000000000000) / Real.sqrt (25 / 2) := by ring
    linarith [eight_hi_bound]

theorem nine_sqrtK_pos : 0 < Real.sqrt (100 / 9 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem nine_hK : (-1 / (100 / 9 : ℝ)) = -9 / 100 := by norm_num

theorem nine_lo_bound : (-0.1371138119 : ℝ) < -(91409207881583 / 200000000000000) / Real.sqrt (100 / 9) := by
  have hs := nine_sqrtK_pos
  have h : (91409207881583 / 200000000000000) / (0.1371138119 : ℝ) < Real.sqrt (100 / 9 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem nine_hi_bound : -(457046039334521 / 1000000000000000) / Real.sqrt (100 / 9) < (-0.1371138118 : ℝ) := by
  have hs := nine_sqrtK_pos
  have h : Real.sqrt (100 / 9 : ℝ) < (457046039334521 / 1000000000000000) / (0.1371138118 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

/-- Falkner–Skan with β = −9/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−0.1371138119 < q(0) < −0.1371138118. -/
theorem fs_neg_reversed_wall_shear_9_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-9 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.1371138119 < q 0 ∧ q 0 < -0.1371138118 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssemble.core_rev (K := 100 / 9) (by norm_num) (by norm_num)
      Checked.FSRev.RNineOver.chain Checked.FSRev.RNineSlow.chain Checked.FSRev.RNineTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← nine_hK]; exact a3 η hη
  · have e : (-91409207881583 / 200000000000000 : ℝ) / Real.sqrt (100 / 9) = -(91409207881583 / 200000000000000) / Real.sqrt (100 / 9) := by ring
    linarith [nine_lo_bound]
  · have e : (-457046039334521 / 1000000000000000 : ℝ) / Real.sqrt (100 / 9) = -(457046039334521 / 1000000000000000) / Real.sqrt (100 / 9) := by ring
    linarith [nine_hi_bound]

theorem eleven_sqrtK_pos : 0 < Real.sqrt (100 / 11 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem eleven_hK : (-1 / (100 / 11 : ℝ)) = -11 / 100 := by norm_num

theorem eleven_lo_bound : (-0.1425079104 : ℝ) < -(85935503312733 / 200000000000000) / Real.sqrt (100 / 11) := by
  have hs := eleven_sqrtK_pos
  have h : (85935503312733 / 200000000000000) / (0.1425079104 : ℝ) < Real.sqrt (100 / 11 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem eleven_hi_bound : -(429677516489283 / 1000000000000000) / Real.sqrt (100 / 11) < (-0.1425079103 : ℝ) := by
  have hs := eleven_sqrtK_pos
  have h : Real.sqrt (100 / 11 : ℝ) < (429677516489283 / 1000000000000000) / (0.1425079103 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

/-- Falkner–Skan with β = −11/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−0.1425079104 < q(0) < −0.1425079103. -/
theorem fs_neg_reversed_wall_shear_11_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-11 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.1425079104 < q 0 ∧ q 0 < -0.1425079103 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssemble.core_rev (K := 100 / 11) (by norm_num) (by norm_num)
      Checked.FSRev.RElevenOver.chain Checked.FSRev.RElevenSlow.chain Checked.FSRev.RElevenTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← eleven_hK]; exact a3 η hη
  · have e : (-85935503312733 / 200000000000000 : ℝ) / Real.sqrt (100 / 11) = -(85935503312733 / 200000000000000) / Real.sqrt (100 / 11) := by ring
    linarith [eleven_lo_bound]
  · have e : (-429677516489283 / 1000000000000000 : ℝ) / Real.sqrt (100 / 11) = -(429677516489283 / 1000000000000000) / Real.sqrt (100 / 11) := by ring
    linarith [eleven_hi_bound]

theorem twelve_sqrtK_pos : 0 < Real.sqrt (25 / 3 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem twelve_hK : (-1 / (25 / 3 : ℝ)) = -12 / 100 := by norm_num

theorem twelve_lo_bound : (-0.1429351944 : ℝ) < -(206309182376447 / 500000000000000) / Real.sqrt (25 / 3) := by
  have hs := twelve_sqrtK_pos
  have h : (206309182376447 / 500000000000000) / (0.1429351944 : ℝ) < Real.sqrt (25 / 3 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem twelve_hi_bound : -(25788647789839 / 62500000000000) / Real.sqrt (25 / 3) < (-0.1429351943 : ℝ) := by
  have hs := twelve_sqrtK_pos
  have h : Real.sqrt (25 / 3 : ℝ) < (25788647789839 / 62500000000000) / (0.1429351943 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

/-- Falkner–Skan with β = −12/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−0.1429351944 < q(0) < −0.1429351943. -/
theorem fs_neg_reversed_wall_shear_12_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-12 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.1429351944 < q 0 ∧ q 0 < -0.1429351943 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssemble.core_rev (K := 25 / 3) (by norm_num) (by norm_num)
      Checked.FSRev.RTwelveOver.chain Checked.FSRev.RTwelveSlow.chain Checked.FSRev.RTwelveTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← twelve_hK]; exact a3 η hη
  · have e : (-206309182376447 / 500000000000000 : ℝ) / Real.sqrt (25 / 3) = -(206309182376447 / 500000000000000) / Real.sqrt (25 / 3) := by ring
    linarith [twelve_lo_bound]
  · have e : (-25788647789839 / 62500000000000 : ℝ) / Real.sqrt (25 / 3) = -(25788647789839 / 62500000000000) / Real.sqrt (25 / 3) := by ring
    linarith [twelve_hi_bound]

theorem thirteen_sqrtK_pos : 0 < Real.sqrt (100 / 13 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem thirteen_hK : (-1 / (100 / 13 : ℝ)) = -13 / 100 := by norm_num

theorem thirteen_lo_bound : (-0.1417095022 : ℝ) < -(196515721654711 / 500000000000000) / Real.sqrt (100 / 13) := by
  have hs := thirteen_sqrtK_pos
  have h : (196515721654711 / 500000000000000) / (0.1417095022 : ℝ) < Real.sqrt (100 / 13 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem thirteen_hi_bound : -(196515721599241 / 500000000000000) / Real.sqrt (100 / 13) < (-0.1417095021 : ℝ) := by
  have hs := thirteen_sqrtK_pos
  have h : Real.sqrt (100 / 13 : ℝ) < (196515721599241 / 500000000000000) / (0.1417095021 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

/-- Falkner–Skan with β = −13/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−0.1417095022 < q(0) < −0.1417095021. -/
theorem fs_neg_reversed_wall_shear_13_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-13 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.1417095022 < q 0 ∧ q 0 < -0.1417095021 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssemble.core_rev (K := 100 / 13) (by norm_num) (by norm_num)
      Checked.FSRev.RThirteenOver.chain Checked.FSRev.RThirteenSlow.chain Checked.FSRev.RThirteenTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← thirteen_hK]; exact a3 η hη
  · have e : (-196515721654711 / 500000000000000 : ℝ) / Real.sqrt (100 / 13) = -(196515721654711 / 500000000000000) / Real.sqrt (100 / 13) := by ring
    linarith [thirteen_lo_bound]
  · have e : (-196515721599241 / 500000000000000 : ℝ) / Real.sqrt (100 / 13) = -(196515721599241 / 500000000000000) / Real.sqrt (100 / 13) := by ring
    linarith [thirteen_hi_bound]

theorem fourteen_sqrtK_pos : 0 < Real.sqrt (50 / 7 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem fourteen_hK : (-1 / (50 / 7 : ℝ)) = -14 / 100 := by norm_num

theorem fourteen_lo_bound : (-0.1386389253 : ℝ) < -(370528113462299 / 1000000000000000) / Real.sqrt (50 / 7) := by
  have hs := fourteen_sqrtK_pos
  have h : (370528113462299 / 1000000000000000) / (0.1386389253 : ℝ) < Real.sqrt (50 / 7 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem fourteen_hi_bound : -(74105622671079 / 200000000000000) / Real.sqrt (50 / 7) < (-0.1386389252 : ℝ) := by
  have hs := fourteen_sqrtK_pos
  have h : Real.sqrt (50 / 7 : ℝ) < (74105622671079 / 200000000000000) / (0.1386389252 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

/-- Falkner–Skan with β = −14/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−0.1386389253 < q(0) < −0.1386389252. -/
theorem fs_neg_reversed_wall_shear_14_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-14 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.1386389253 < q 0 ∧ q 0 < -0.1386389252 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssemble.core_rev (K := 50 / 7) (by norm_num) (by norm_num)
      Checked.FSRev.RFourteenOver.chain Checked.FSRev.RFourteenSlow.chain Checked.FSRev.RFourteenTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← fourteen_hK]; exact a3 η hη
  · have e : (-370528113462299 / 1000000000000000 : ℝ) / Real.sqrt (50 / 7) = -(370528113462299 / 1000000000000000) / Real.sqrt (50 / 7) := by ring
    linarith [fourteen_lo_bound]
  · have e : (-74105622671079 / 200000000000000 : ℝ) / Real.sqrt (50 / 7) = -(74105622671079 / 200000000000000) / Real.sqrt (50 / 7) := by ring
    linarith [fourteen_hi_bound]

theorem fifteen_sqrtK_pos : 0 < Real.sqrt (20 / 3 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem fifteen_hK : (-1 / (20 / 3 : ℝ)) = -15 / 100 := by norm_num

theorem fifteen_lo_bound : (-0.1334212379 : ℝ) < -(344492154938637 / 1000000000000000) / Real.sqrt (20 / 3) := by
  have hs := fifteen_sqrtK_pos
  have h : (344492154938637 / 1000000000000000) / (0.1334212379 : ℝ) < Real.sqrt (20 / 3 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem fifteen_hi_bound : -(86123038720229 / 250000000000000) / Real.sqrt (20 / 3) < (-0.1334212378 : ℝ) := by
  have hs := fifteen_sqrtK_pos
  have h : Real.sqrt (20 / 3 : ℝ) < (86123038720229 / 250000000000000) / (0.1334212378 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

/-- Falkner–Skan with β = −15/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−0.1334212379 < q(0) < −0.1334212378. -/
theorem fs_neg_reversed_wall_shear_15_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-15 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.1334212379 < q 0 ∧ q 0 < -0.1334212378 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssemble.core_rev (K := 20 / 3) (by norm_num) (by norm_num)
      Checked.FSRev.RFifteenOver.chain Checked.FSRev.RFifteenSlow.chain Checked.FSRev.RFifteenTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← fifteen_hK]; exact a3 η hη
  · have e : (-344492154938637 / 1000000000000000 : ℝ) / Real.sqrt (20 / 3) = -(344492154938637 / 1000000000000000) / Real.sqrt (20 / 3) := by ring
    linarith [fifteen_lo_bound]
  · have e : (-86123038720229 / 250000000000000 : ℝ) / Real.sqrt (20 / 3) = -(86123038720229 / 250000000000000) / Real.sqrt (20 / 3) := by ring
    linarith [fifteen_hi_bound]

theorem sixteen_sqrtK_pos : 0 < Real.sqrt (25 / 4 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem sixteen_hK : (-1 / (25 / 4 : ℝ)) = -16 / 100 := by norm_num

theorem sixteen_lo_bound : (-0.1255676643 : ℝ) < -(15695958029657 / 50000000000000) / Real.sqrt (25 / 4) := by
  have hs := sixteen_sqrtK_pos
  have h : (15695958029657 / 50000000000000) / (0.1255676643 : ℝ) < Real.sqrt (25 / 4 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem sixteen_hi_bound : -(31391916052157 / 100000000000000) / Real.sqrt (25 / 4) < (-0.1255676642 : ℝ) := by
  have hs := sixteen_sqrtK_pos
  have h : Real.sqrt (25 / 4 : ℝ) < (31391916052157 / 100000000000000) / (0.1255676642 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

/-- Falkner–Skan with β = −16/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, with
−0.1255676643 < q(0) < −0.1255676642. -/
theorem fs_neg_reversed_wall_shear_16_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-16 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.1255676643 < q 0 ∧ q 0 < -0.1255676642 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssemble.core_rev (K := 25 / 4) (by norm_num) (by norm_num)
      Checked.FSRev.RSixteenOver.chain Checked.FSRev.RSixteenSlow.chain Checked.FSRev.RSixteenTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← sixteen_hK]; exact a3 η hη
  · have e : (-15695958029657 / 50000000000000 : ℝ) / Real.sqrt (25 / 4) = -(15695958029657 / 50000000000000) / Real.sqrt (25 / 4) := by ring
    linarith [sixteen_lo_bound]
  · have e : (-31391916052157 / 100000000000000 : ℝ) / Real.sqrt (25 / 4) = -(31391916052157 / 100000000000000) / Real.sqrt (25 / 4) := by ring
    linarith [sixteen_hi_bound]

end Checked.FalknerSkan.NegReversedWallShearRows
