import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Checked.Sim.ODETools
import Checked.Math.LECell

/-! Thomas–Fermi, `TFCell`: Kamke first-touch barriers: one cell of a strict polynomial super- or sub-solution of the cooperative system. Promoted from `Work/Math/TFCell.lean`. -/

namespace Checked.Math.TFCell
open Set Filter Topology Checked.Sim

/-- Positive derivative at a zero: negative just to the left. -/
theorem neg_left_of_deriv {D : ℝ → ℝ} {τ d : ℝ} (hd : 0 < d) (hD : HasDerivAt D d τ)
    (hz : D τ = 0) : ∀ᶠ t in 𝓝[<] τ, D t < 0 := by
  have h1 := (hasDerivAt_iff_tendsto_slope.1 hD).mono_left
    (nhdsWithin_mono τ (fun t (ht : t ∈ Iio τ) => (ne_of_lt ht : t ≠ τ)))
  filter_upwards [h1.eventually (lt_mem_nhds hd), self_mem_nhdsWithin] with t ht htl
  rw [slope_def_field, hz, sub_zero] at ht
  have hneg : t - τ < 0 := sub_neg.2 htl
  by_contra hc
  push Not at hc
  have : D t / (t - τ) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hc hneg.le
  linarith

/-- A function continuous within `Icc a b` at `τ ∈ (a, b]` and positive on `(a, τ)` is
nonnegative at `τ`. -/
theorem nonneg_of_left {D : ℝ → ℝ} {a b τ : ℝ} (hab : a < τ) (hτb : τ ≤ b)
    (hc : ContinuousOn D (Icc a b)) (hpos : ∀ t ∈ Ioo a τ, 0 < D t) : 0 ≤ D τ := by
  have := right_nhdsWithin_Ioo_neBot hab
  have hT : Tendsto D (𝓝[Ioo a τ] τ) (𝓝 (D τ)) :=
    ((hc τ ⟨hab.le, hτb⟩).mono (fun t ht => ⟨ht.1.le, ht.2.le.trans hτb⟩)).tendsto
  exact ge_of_tendsto hT (Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => (hpos t ht).le)

/-- First touch: two functions continuous on [a, b], positive at a, each of which has a positive
derivative wherever it vanishes while the other is nonnegative, stay positive on [a, b]. -/
theorem first_touch {D1 D2 : ℝ → ℝ} {a b : ℝ}
    (hc1 : ContinuousOn D1 (Icc a b)) (hc2 : ContinuousOn D2 (Icc a b))
    (h1 : 0 < D1 a) (h2 : 0 < D2 a)
    (hd1 : ∀ τ ∈ Ioc a b, D1 τ = 0 → 0 ≤ D2 τ → ∃ d, 0 < d ∧ HasDerivAt D1 d τ)
    (hd2 : ∀ τ ∈ Ioc a b, D2 τ = 0 → 0 ≤ D1 τ → ∃ d, 0 < d ∧ HasDerivAt D2 d τ) :
    ∀ t ∈ Icc a b, 0 < D1 t ∧ 0 < D2 t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t₀, ht₀, hbad⟩ := hcon
  set S : Set ℝ := (Icc a b ∩ D1 ⁻¹' Iic 0) ∪ (Icc a b ∩ D2 ⁻¹' Iic 0) with hS
  have hSc : IsClosed S :=
    (hc1.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic).union
      (hc2.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic)
  have ht₀S : t₀ ∈ S := by
    by_cases h : 0 < D1 t₀
    · exact Or.inr ⟨ht₀, show D2 t₀ ≤ 0 from hbad h⟩
    · exact Or.inl ⟨ht₀, show D1 t₀ ≤ 0 from not_lt.1 h⟩
  have hbdd : BddBelow S := ⟨a, fun t ht => by rcases ht with ht | ht <;> exact ht.1.1⟩
  have hτS := hSc.csInf_mem ⟨t₀, ht₀S⟩ hbdd
  set τ := sInf S
  have hτI : τ ∈ Icc a b := by rcases hτS with h | h <;> exact h.1
  have hτ_le : ∀ t ∈ S, τ ≤ t := fun t ht => csInf_le hbdd ht
  have hgood : ∀ t ∈ Icc a b, t < τ → 0 < D1 t ∧ 0 < D2 t := by
    intro t ht htτ
    by_contra hn
    have : t ∈ S := by
      by_cases h : 0 < D1 t
      · exact Or.inr ⟨ht, show D2 t ≤ 0 from not_lt.1 fun h2 => hn ⟨h, h2⟩⟩
      · exact Or.inl ⟨ht, show D1 t ≤ 0 from not_lt.1 h⟩
    exact absurd (hτ_le t this) (not_le.2 htτ)
  have haτ : a < τ := by
    rcases lt_or_eq_of_le hτI.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hτS
      rcases hτS with h' | h'
      · exact absurd h'.2 (not_le.2 h1)
      · exact absurd h'.2 (not_le.2 h2)
  have hIoo : ∀ t ∈ Ioo a τ, 0 < D1 t ∧ 0 < D2 t := fun t ht =>
    hgood t ⟨ht.1.le, ht.2.le.trans hτI.2⟩ ht.2
  have n1 : 0 ≤ D1 τ := nonneg_of_left haτ hτI.2 hc1 fun t ht => (hIoo t ht).1
  have n2 : 0 ≤ D2 τ := nonneg_of_left haτ hτI.2 hc2 fun t ht => (hIoo t ht).2
  have key : ∀ D : ℝ → ℝ, (∀ t ∈ Ioo a τ, 0 < D t) → (∃ d, 0 < d ∧ HasDerivAt D d τ) →
      D τ = 0 → False := by
    intro D hD ⟨d, hd, hder⟩ hz
    have ev := neg_left_of_deriv hd hder hz
    have ev2 : Ioo a τ ∈ 𝓝[<] τ := Ioo_mem_nhdsLT haτ
    obtain ⟨t, ht1, ht2⟩ := (ev.and ev2).exists
    exact absurd (hD t ht2) (not_lt.2 ht1.le)
  have hτIoc : τ ∈ Ioc a b := ⟨haτ, hτI.2⟩
  rcases hτS with h | h
  · have hz : D1 τ = 0 := le_antisymm h.2 n1
    exact key D1 (fun t ht => (hIoo t ht).1) (hd1 τ hτIoc hz n2) hz
  · have hz : D2 τ = 0 := le_antisymm h.2 n2
    exact key D2 (fun t ht => (hIoo t ht).2) (hd2 τ hτIoc hz n1) hz

/-- Cubes are monotone. -/
theorem cube_le {a b : ℝ} (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have : 0 ≤ (b - a) * ((a + b) ^ 2 + a ^ 2 + b ^ 2) := mul_nonneg (by linarith) (by positivity)
  nlinarith [this]

theorem hasDerivAt_evalQ_sub (q : List ℚ) (t0 t : ℝ) :
    HasDerivAt (fun t => evalQ q (t - t0)) (dEvalQ q (t - t0)) t :=
  (hasDerivAt_evalQ q (t - t0)).comp_sub_const t t0

theorem continuous_evalQ_sub (q : List ℚ) (t0 : ℝ) : Continuous (fun t => evalQ q (t - t0)) :=
  (continuous_evalQ q).comp (continuous_sub_right t0)

/-- Upper barrier on one cell. -/
theorem super_cell (qw qp : List ℚ) {w P : ℝ → ℝ} {t0 h : ℝ} (ht0 : 0 ≤ t0) (hh : 0 < h)
    (hcw : ContinuousOn w (Icc t0 (t0 + h))) (hcP : ContinuousOn P (Icc t0 (t0 + h)))
    (hw : ∀ t ∈ Ioc t0 (t0 + h), HasDerivAt w (t * P t / w t) t)
    (hP : ∀ t ∈ Ioc t0 (t0 + h), HasDerivAt P (2 * w t ^ 3) t)
    (hwpos : ∀ t ∈ Ioc t0 (t0 + h), 0 < w t)
    (c1 : ∀ σ ∈ Icc 0 h, 0 < evalQ qw σ * dEvalQ qw σ - (t0 + σ) * evalQ qp σ)
    (c2 : ∀ σ ∈ Icc 0 h, 0 < dEvalQ qp σ - 2 * evalQ qw σ ^ 3)
    (s1 : w t0 < evalQ qw 0) (s2 : P t0 < evalQ qp 0) :
    ∀ t ∈ Icc t0 (t0 + h), w t < evalQ qw (t - t0) ∧ P t < evalQ qp (t - t0) := by
  have key := first_touch (D1 := fun t => evalQ qw (t - t0) - w t)
    (D2 := fun t => evalQ qp (t - t0) - P t) (a := t0) (b := t0 + h)
    ((continuous_evalQ_sub qw t0).continuousOn.sub hcw)
    ((continuous_evalQ_sub qp t0).continuousOn.sub hcP)
    (by simp only [sub_self]; linarith) (by simp only [sub_self]; linarith)
    (fun τ hτ hz hn => by
      have hσ : τ - t0 ∈ Icc 0 h := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      have hc := c1 _ hσ
      have et : t0 + (τ - t0) = τ := by ring
      rw [et] at hc
      have hwq : w τ = evalQ qw (τ - t0) := by linarith
      have hQ : 0 < evalQ qw (τ - t0) := hwq ▸ hwpos τ hτ
      have hτ0 : 0 ≤ τ := by linarith [hτ.1]
      have hPle : τ * P τ ≤ τ * evalQ qp (τ - t0) :=
        mul_le_mul_of_nonneg_left (by linarith) hτ0
      refine ⟨dEvalQ qw (τ - t0) - τ * P τ / w τ, ?_,
        (hasDerivAt_evalQ_sub qw t0 τ).sub (hw τ hτ)⟩
      rw [hwq, sub_pos, div_lt_iff₀ hQ]
      nlinarith)
    (fun τ hτ hz hn => by
      have hσ : τ - t0 ∈ Icc 0 h := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      have hc := c2 _ hσ
      have hcube := cube_le (show w τ ≤ evalQ qw (τ - t0) by linarith)
      exact ⟨dEvalQ qp (τ - t0) - 2 * w τ ^ 3, by linarith,
        (hasDerivAt_evalQ_sub qp t0 τ).sub (hP τ hτ)⟩)
  intro t ht
  have := key t ht
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- Lower barrier on one cell. -/
theorem sub_cell (qw qp : List ℚ) {w P : ℝ → ℝ} {t0 h : ℝ} (ht0 : 0 ≤ t0) (hh : 0 < h)
    (hcw : ContinuousOn w (Icc t0 (t0 + h))) (hcP : ContinuousOn P (Icc t0 (t0 + h)))
    (hw : ∀ t ∈ Ioc t0 (t0 + h), HasDerivAt w (t * P t / w t) t)
    (hP : ∀ t ∈ Ioc t0 (t0 + h), HasDerivAt P (2 * w t ^ 3) t)
    (hwpos : ∀ t ∈ Ioc t0 (t0 + h), 0 < w t)
    (c1 : ∀ σ ∈ Icc 0 h, evalQ qw σ * dEvalQ qw σ - (t0 + σ) * evalQ qp σ < 0)
    (c2 : ∀ σ ∈ Icc 0 h, dEvalQ qp σ - 2 * evalQ qw σ ^ 3 < 0)
    (s1 : evalQ qw 0 < w t0) (s2 : evalQ qp 0 < P t0) :
    ∀ t ∈ Icc t0 (t0 + h), evalQ qw (t - t0) < w t ∧ evalQ qp (t - t0) < P t := by
  have key := first_touch (D1 := fun t => w t - evalQ qw (t - t0))
    (D2 := fun t => P t - evalQ qp (t - t0)) (a := t0) (b := t0 + h)
    (hcw.sub (continuous_evalQ_sub qw t0).continuousOn)
    (hcP.sub (continuous_evalQ_sub qp t0).continuousOn)
    (by simp only [sub_self]; linarith) (by simp only [sub_self]; linarith)
    (fun τ hτ hz hn => by
      have hσ : τ - t0 ∈ Icc 0 h := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      have hc := c1 _ hσ
      have et : t0 + (τ - t0) = τ := by ring
      rw [et] at hc
      have hwq : w τ = evalQ qw (τ - t0) := by linarith
      have hQ : 0 < evalQ qw (τ - t0) := hwq ▸ hwpos τ hτ
      have hτ0 : 0 ≤ τ := by linarith [hτ.1]
      have hPle : τ * evalQ qp (τ - t0) ≤ τ * P τ :=
        mul_le_mul_of_nonneg_left (by linarith) hτ0
      refine ⟨τ * P τ / w τ - dEvalQ qw (τ - t0), ?_,
        (hw τ hτ).sub (hasDerivAt_evalQ_sub qw t0 τ)⟩
      rw [hwq, sub_pos, lt_div_iff₀ hQ]
      nlinarith)
    (fun τ hτ hz hn => by
      have hσ : τ - t0 ∈ Icc 0 h := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      have hc := c2 _ hσ
      have hcube := cube_le (show evalQ qw (τ - t0) ≤ w τ by linarith)
      exact ⟨2 * w τ ^ 3 - dEvalQ qp (τ - t0), by linarith,
        (hP τ hτ).sub (hasDerivAt_evalQ_sub qp t0 τ)⟩)
  intro t ht
  have := key t ht
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

end Checked.Math.TFCell
