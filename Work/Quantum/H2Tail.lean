import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.IntermediateValue
/-!
# The tail of the radial H₂⁺ equation where the coefficient is negative (run 2026-11-26T1628Z)

The radial (ξ) equation of the separated H₂⁺ problem in flux form is ((ξ² − 1) L′)′ = −N(ξ) L with
N(ξ) = 2Rξ + (εR²/2) ξ² + A; for ε < 0, N(ξ) ≤ −κ ξ² for some κ > 0 on a half-line [a, ∞).
On that half-line the function Q = L · (ξ² − 1) L′ has derivative (ξ² − 1) L′² − N L² ≥ κ ξ² L², so:

* `stays_above`: if L(b) > 0 and L′(b) > 0 at some b ≥ a, then L(x) ≥ L(b) for every x ≥ b
  (the shooting event "over": the solution never returns to zero and does not tend to zero);
* `tail_of_nonincreasing`: if L > 0 and L′ ≤ 0 on [a, ∞) (neither event), then L → 0 and
  x ↦ L(x)² x² is integrable on [a, ∞) (the bound-state conditions of the H₂⁺ freeze).

No numerics; generic in N, κ, a. Part of the route of `runs/2026-11-26T1628Z/README.md`, section Route.
-/

namespace Work.Quantum.H2Tail
open Set Filter Topology MeasureTheory

variable {L L' N : ℝ → ℝ} {a κ : ℝ}

/-- The derivative of Q = L · (x² − 1) L′. -/
theorem hasDerivAt_Q {x : ℝ} (hL : HasDerivAt L (L' x) x)
    (hP : HasDerivAt (fun y => (y ^ 2 - 1) * L' y) (-(N x * L x)) x) :
    HasDerivAt (fun y => L y * ((y ^ 2 - 1) * L' y))
      ((x ^ 2 - 1) * L' x ^ 2 - N x * L x ^ 2) x := by
  convert hL.mul hP using 1
  ring

theorem Q_monotone (ha : 1 ≤ a) (hL : ∀ x ∈ Ici a, HasDerivAt L (L' x) x)
    (hP : ∀ x ∈ Ici a, HasDerivAt (fun y => (y ^ 2 - 1) * L' y) (-(N x * L x)) x)
    (hN : ∀ x ∈ Ici a, N x ≤ 0) :
    MonotoneOn (fun y => L y * ((y ^ 2 - 1) * L' y)) (Ici a) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun x => (x ^ 2 - 1) * L' x ^ 2 - N x * L x ^ 2) (convex_Ici a) ?_ (fun x hx => ?_) (fun x hx => ?_)
  · exact fun x hx => (hasDerivAt_Q (hL x hx) (hP x hx)).continuousAt.continuousWithinAt
  · rw [interior_Ici] at hx
    exact (hasDerivAt_Q (hL x (mem_Ici.mpr (le_of_lt hx))) (hP x (mem_Ici.mpr (le_of_lt hx)))).hasDerivWithinAt
  · rw [interior_Ici] at hx
    have hx' : a ≤ x := le_of_lt hx
    have h1 : 0 ≤ x ^ 2 - 1 := by nlinarith
    have h2 := hN x hx'
    have : 0 ≤ (x ^ 2 - 1) * L' x ^ 2 := mul_nonneg h1 (sq_nonneg _)
    nlinarith [sq_nonneg (L x)]

/-- The shooting event "over": positive with positive slope at some b ≥ a, then never below L(b). -/
theorem stays_above (ha : 1 < a) (hL : ∀ x ∈ Ici a, HasDerivAt L (L' x) x)
    (hP : ∀ x ∈ Ici a, HasDerivAt (fun y => (y ^ 2 - 1) * L' y) (-(N x * L x)) x)
    (hN : ∀ x ∈ Ici a, N x ≤ 0) {b : ℝ} (hb : a ≤ b) (hLb : 0 < L b) (hL'b : 0 < L' b) :
    ∀ x ∈ Ici b, L b ≤ L x := by
  have hmono := Q_monotone ha.le hL hP hN
  -- Q stays positive past b
  have hQb : 0 < L b * ((b ^ 2 - 1) * L' b) := by
    have : 0 < b ^ 2 - 1 := by nlinarith
    positivity
  have hQ : ∀ x ∈ Ici b, 0 < L x * L' x := by
    intro x hx
    have hx' : b ≤ x := hx
    have := hmono (show b ∈ Ici a from hb) (show x ∈ Ici a from hb.trans hx') hx'
    have hpos : 0 < L x * ((x ^ 2 - 1) * L' x) := lt_of_lt_of_le hQb this
    have hx1 : 0 < x ^ 2 - 1 := by nlinarith
    have : L x * ((x ^ 2 - 1) * L' x) = (x ^ 2 - 1) * (L x * L' x) := by ring
    rw [this] at hpos
    exact pos_of_mul_pos_right hpos hx1.le
  -- L² is monotone on [b, ∞)
  have hsq : MonotoneOn (fun y => L y ^ 2) (Ici b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y => 2 * (L y * L' y)) (convex_Ici b)
      ?_ (fun x hx => ?_) (fun x hx => ?_)
    · intro x hx
      exact ((hL x (hb.trans hx)).pow 2).continuousAt.continuousWithinAt
    · rw [interior_Ici] at hx
      have := (hL x (hb.trans (le_of_lt hx))).pow 2
      refine HasDerivAt.hasDerivWithinAt ?_
      convert this using 1
      push_cast
      ring
    · rw [interior_Ici] at hx
      have := hQ x (mem_Ici.mpr (le_of_lt hx))
      linarith
  -- L stays positive (a zero would contradict L² ≥ L(b)² > 0)
  have hcont : ContinuousOn L (Ici b) := fun x hx => (hL x (hb.trans hx)).continuousAt.continuousWithinAt
  have hpos : ∀ x ∈ Ici b, 0 < L x := by
    intro x hx
    by_contra hneg
    push Not at hneg
    have hx' : b ≤ x := hx
    obtain ⟨c, hc, hc0⟩ : ∃ c ∈ Icc b x, L c = 0 := by
      have := intermediate_value_Icc' hx' (hcont.mono (Icc_subset_Ici_self))
      exact this ⟨hneg, hLb.le⟩
    have := hsq (mem_Ici.mpr le_rfl) (show c ∈ Ici b from hc.1) hc.1
    simp only [hc0] at this
    nlinarith
  intro x hx
  have h1 := hsq (mem_Ici.mpr le_rfl) hx hx
  have h2 := hpos x hx
  nlinarith

/-- Neither event: positive and non-increasing on [a, ∞). Then L → 0 and L² x² is integrable there. -/
theorem tail_of_nonincreasing (ha : 1 < a) (hκ : 0 < κ) (hL : ∀ x ∈ Ici a, HasDerivAt L (L' x) x)
    (hP : ∀ x ∈ Ici a, HasDerivAt (fun y => (y ^ 2 - 1) * L' y) (-(N x * L x)) x)
    (hN : ∀ x ∈ Ici a, N x ≤ -(κ * x ^ 2))
    (hpos : ∀ x ∈ Ici a, 0 < L x) (hdec : ∀ x ∈ Ici a, L' x ≤ 0) :
    Tendsto L atTop (𝓝 0) ∧ IntegrableOn (fun x => L x ^ 2 * x ^ 2) (Ici a) := by
  set Q : ℝ → ℝ := fun y => L y * ((y ^ 2 - 1) * L' y) with hQdef
  have hcont : ContinuousOn L (Ici a) := fun x hx => (hL x hx).continuousAt.continuousWithinAt
  have hcontAt : ∀ x ∈ Ioi a, ContinuousAt L x := fun x hx => (hL x (mem_Ici.mpr (le_of_lt hx))).continuousAt
  -- integral bound: κ ∫_a^X x² L² ≤ Q X − Q a ≤ −Q a
  have hbound : ∀ X ∈ Ici a, κ * ∫ x in a..X, L x ^ 2 * x ^ 2 ≤ -Q a := by
    intro X hX
    have hX' : a ≤ X := hX
    have hfc : ContinuousOn (fun x => L x ^ 2 * x ^ 2) (Icc a X) :=
      ((hcont.mono Icc_subset_Ici_self).pow 2).mul (continuousOn_id.pow 2)
    -- G = Q − κ ∫ is monotone on [a, X]
    have hG : MonotoneOn (fun y => Q y - κ * ∫ x in a..y, L x ^ 2 * x ^ 2) (Icc a X) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg
        (f' := fun y => ((y ^ 2 - 1) * L' y ^ 2 - N y * L y ^ 2) - κ * (L y ^ 2 * y ^ 2))
        (convex_Icc a X) ?_ (fun x hx => ?_) (fun x hx => ?_)
      · refine ContinuousOn.sub (fun x hx => (hasDerivAt_Q (hL x hx.1) (hP x hx.1)).continuousAt.continuousWithinAt) ?_
        refine ContinuousOn.mul continuousOn_const ?_
        have : ContinuousOn (fun y => ∫ x in a..y, L x ^ 2 * x ^ 2) (Icc a X) := by
          have hint : IntervalIntegrable (fun x => L x ^ 2 * x ^ 2) volume a X :=
            (hfc.intervalIntegrable_of_Icc hX')
          exact (intervalIntegral.continuousOn_primitive_interval' hint (left_mem_uIcc)).mono
            (by rw [uIcc_of_le hX'])
        exact this
      · rw [interior_Icc] at hx
        have hxa : a ≤ x := le_of_lt hx.1
        refine HasDerivAt.hasDerivWithinAt ?_
        refine (hasDerivAt_Q (hL x hxa) (hP x hxa)).sub (HasDerivAt.const_mul κ ?_)
        refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
        · exact (hfc.mono (Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable_of_Icc hxa
        · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
            (fun y hy => (((hcontAt y hy).pow 2).mul (continuousAt_id.pow 2)).continuousWithinAt) x hx.1
        · exact ((hcontAt x hx.1).pow 2).mul (continuousAt_id.pow 2)
      · rw [interior_Icc] at hx
        have hxa : a ≤ x := le_of_lt hx.1
        have h1 : 0 ≤ (x ^ 2 - 1) * L' x ^ 2 := mul_nonneg (by nlinarith) (sq_nonneg _)
        have h2 := hN x hxa
        nlinarith [sq_nonneg (L x), sq_nonneg x]
    have := hG (left_mem_Icc.mpr hX') (right_mem_Icc.mpr hX') hX'
    simp only [intervalIntegral.integral_same, mul_zero, sub_zero] at this
    have hQX : Q X ≤ 0 := by
      have h1 : 0 ≤ X ^ 2 - 1 := by nlinarith
      have h2 := hpos X hX
      have h3 := hdec X hX
      simp only [hQdef]
      have : (X ^ 2 - 1) * L' X ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 h3
      exact mul_nonpos_of_nonneg_of_nonpos h2.le this
    linarith
  -- integrability
  have hint : IntegrableOn (fun x => L x ^ 2 * x ^ 2) (Ioi a) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (-Q a / κ) a
      (l := atTop) (b := id) (fun i => ?_) tendsto_id ?_
    · rcases le_or_gt i a with hi | hi
      · simp [Ioc_eq_empty_of_le hi]
      · exact (((hcont.mono Icc_subset_Ici_self).pow 2).mul
          (continuousOn_id.pow 2)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · filter_upwards [eventually_ge_atTop a] with X hX
      have hb := hbound X hX
      have hnorm : (∫ x in a..id X, ‖L x ^ 2 * x ^ 2‖) = ∫ x in a..X, L x ^ 2 * x ^ 2 := by
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        simp only [norm_mul, norm_pow, Real.norm_eq_abs, sq_abs]
      rw [hnorm, le_div_iff₀ hκ]
      linarith
  refine ⟨?_, (integrableOn_Ici_iff_integrableOn_Ioi).mpr hint⟩
  -- L is antitone and positive, so it has a limit ℓ ≥ 0; ℓ > 0 contradicts the integral bound
  have hanti : AntitoneOn L (Ici a) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := L') (convex_Ici a) hcont (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ici] at hx
      exact (hL x (mem_Ici.mpr (le_of_lt hx))).hasDerivWithinAt
    · rw [interior_Ici] at hx
      exact hdec x (mem_Ici.mpr (le_of_lt hx))
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- some X ≥ a has L X < ε
  obtain ⟨X, hXa, hXε⟩ : ∃ X, a ≤ X ∧ L X < ε := by
    by_contra hcon
    push Not at hcon
    set X := a + (-Q a) / (κ * ε ^ 2 * a ^ 2) + 1 with hXdef
    have hQa : Q a ≤ 0 := by
      have h1 : 0 ≤ a ^ 2 - 1 := by nlinarith
      have h3 := hdec a (le_refl a)
      simp only [hQdef]
      exact mul_nonpos_of_nonneg_of_nonpos (hpos a (mem_Ici.mpr le_rfl)).le (mul_nonpos_of_nonneg_of_nonpos h1 h3)
    have hden : 0 < κ * ε ^ 2 * a ^ 2 := by positivity
    have hXa : a ≤ X := by
      have : 0 ≤ (-Q a) / (κ * ε ^ 2 * a ^ 2) := div_nonneg (by linarith) hden.le
      linarith
    have hb := hbound X hXa
    have hmono : ∫ x in a..X, ε ^ 2 * a ^ 2 ≤ ∫ x in a..X, L x ^ 2 * x ^ 2 := by
      refine intervalIntegral.integral_mono_on hXa (by simp) ?_ (fun x hx => ?_)
      · exact (((hcont.mono Icc_subset_Ici_self).pow 2).mul (continuousOn_id.pow 2)).intervalIntegrable_of_Icc hXa
      · have h1 := hcon x hx.1
        have h2 : ε ^ 2 ≤ L x ^ 2 := by nlinarith
        have h3 : a ^ 2 ≤ x ^ 2 := by nlinarith [hx.1]
        have := mul_le_mul h2 h3 (by positivity) (sq_nonneg _)
        simpa using this
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have h4 : κ * ((X - a) * (ε ^ 2 * a ^ 2)) ≤ -Q a := le_trans (mul_le_mul_of_nonneg_left hmono hκ.le) hb
    have h5 : (X - a) * (κ * ε ^ 2 * a ^ 2) = -Q a + κ * ε ^ 2 * a ^ 2 := by
      rw [hXdef]; field_simp; ring
    nlinarith
  refine ⟨X, fun x hx => ?_⟩
  have h1 := hanti (show X ∈ Ici a from hXa) (show x ∈ Ici a from hXa.trans hx) hx
  have h2 := hpos x (hXa.trans hx)
  rw [Real.dist_eq, sub_zero, abs_of_pos h2]
  linarith

end Work.Quantum.H2Tail
