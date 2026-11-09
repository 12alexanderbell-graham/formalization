import Mathlib
import Work.FSNeg.NAssemble
import Work.FalknerSkan.NegDecay

/-!
# Falkner–Skan β = −1/10: the decay-class solution with its wall shear in a window (run 2026-11-09T1228Z)

`core_window`: the supremum argument of `Work.FSNeg.NAssemble.core_exists` for any window
lo < hi in (0, 11/10] whose ends carry certified chains (Slow at lo, Over at hi): the neither-point
a lies strictly inside (lo, hi) (a ≠ lo because lo has Slow and a does not), and the scaled-back
solution has q(0) = a/√10.
`ten_window`: with lo = 1.009619629 and hi = 1.0096196292 (scaled; certified chains as hypotheses),
every solution in the class q > 0, faster-than-every-exponential approach has
0.3192697598 < q(0) < 0.3192697599 (uniqueness `Work.FalknerSkan.NegDecay.fs_neg_decay_equal`),
and every solution with q > 0 has q(0) < 0.3192697599 (`fs_neg_decay_max_shear`).
-/

namespace Work.FSNeg.NWindow
open Set Filter Topology Work.FSNeg.NBase Work.FSNeg.NFlow Work.FSNeg.NAssemble

theorem core_window {lo hi : ℝ} (hlo0 : 0 < lo) (hlh : lo < hi) (hhi1 : hi ≤ 11 / 10)
    (hS : ChainTo lo Slow) (hO : ChainTo hi Over) :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      lo / Real.sqrt 10 < q 0 ∧ q 0 < hi / Real.sqrt 10 := by
  have slow_lo : Slow (flow lo) := of_chain hS
  have over_hi : Over (flow hi) := of_chain hO
  set S : Set ℝ := {α | α ∈ Icc lo hi ∧ Slow (flow α)} with hSd
  have hloS : lo ∈ S := ⟨⟨le_rfl, hlh.le⟩, slow_lo⟩
  have hne : S.Nonempty := ⟨lo, hloS⟩
  have hbdd : BddAbove S := ⟨hi, fun α hα => hα.1.2⟩
  set a := sSup S with ha
  have hloa := le_csSup hbdd hloS
  obtain ⟨δ2, hδ2, hO2⟩ := over_open hi over_hi
  have ha_lt : a < hi := by
    have hub : ∀ α ∈ S, α ≤ hi - δ2 / 2 := by
      intro α hα
      by_contra hc
      push Not at hc
      have hOα := hO2 α (by rw [abs_lt]; constructor <;> linarith [hα.1.2])
      exact slow_not_over (by linarith [hα.1.1]) (by linarith [hα.1.2]) hα.2 hOα
    have := csSup_le hne hub
    linarith
  have hnS : ¬ Slow (flow a) := by
    intro hSa
    obtain ⟨δ, hδ, hSa'⟩ := slow_open a hSa
    obtain ⟨α', hα'd⟩ : ∃ x : ℝ, x = a + min (δ / 2) ((hi - a) / 2) := ⟨_, rfl⟩
    have h1 : 0 < min (δ / 2) ((hi - a) / 2) := lt_min (by linarith) (by linarith)
    have h2 : min (δ / 2) ((hi - a) / 2) ≤ δ / 2 := min_le_left _ _
    have h3 : min (δ / 2) ((hi - a) / 2) ≤ (hi - a) / 2 := min_le_right _ _
    have hα'S : α' ∈ S := ⟨⟨by linarith, by linarith⟩,
      hSa' α' (by rw [abs_lt]; constructor <;> linarith)⟩
    have := le_csSup hbdd hα'S
    linarith
  have hnO : ¬ Over (flow a) := by
    intro hOa
    obtain ⟨δ, hδ, hOa'⟩ := over_open a hOa
    obtain ⟨α, hαS, hαa⟩ := exists_lt_of_lt_csSup hne (show a - δ < a by linarith)
    have hle : α ≤ a := le_csSup hbdd hαS
    exact slow_not_over (by linarith [hαS.1.1]) (by linarith [hαS.1.2]) hαS.2
      (hOa' α (by rw [abs_lt]; constructor <;> linarith))
  have hlo_lt : lo < a := by
    rcases eq_or_lt_of_le hloa with h | h
    · exact absurd (by rw [ha, ← h]; exact slow_lo) hnS
    · exact h
  obtain ⟨tF, tP, tQ, hlim, hqpos, hdec⟩ :=
    neither_class (by linarith) (by linarith) hnS hnO
  set F := fun t => (flow a t).1
  set P := fun t => (flow a t).2.1
  set Q := fun t => (flow a t).2.2
  have hF0 : F 0 = 0 := by simp [F, flow_zero]
  have hP0 : P 0 = 0 := by simp [P, flow_zero]
  have hQ0 : Q 0 = a := by simp [Q, flow_zero]
  have hc : 0 < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
  have hc2 : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have tQ' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(10 * F η * Q η) - (-1) * (1 - P η ^ 2)) (Ici 0) η :=
    fun η hη => (tQ η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc tF tP tQ'
  have hm := Checked.FalknerSkan.FSScale.mapsTo_div hc
  refine ⟨fun s => Real.sqrt 10 * F (s / Real.sqrt 10), fun s => P (s / Real.sqrt 10),
    fun s => Q (s / Real.sqrt 10) / Real.sqrt 10, A, B, fun s hs => ?_, by simp [hF0],
    by simp [hP0], Checked.FalknerSkan.FSScale.scale_lim hc hlim,
    fun s hs => div_pos (hqpos _ (hm hs)) hc, fun M => ?_, ?_, ?_⟩
  · refine (C s hs).congr_deriv ?_
    field_simp
    rw [hc2]
  · have hd := (tendsto_id.atTop_div_const hc).eventually (hdec (M * Real.sqrt 10))
    filter_upwards [hd] with s hs
    simp only [id] at hs
    rw [le_div_iff₀ hc]
    linarith
  · simp only [zero_div, hQ0]
    exact div_lt_div_of_pos_right hlo_lt hc
  · simp only [zero_div, hQ0]
    exact div_lt_div_of_pos_right ha_lt hc

theorem sqrt10_lt : Real.sqrt 10 < 316227766016838 / 100000000000000 :=
  (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

theorem sqrt10_gt : 316227766016837 / 100000000000000 < Real.sqrt 10 :=
  (Real.lt_sqrt (by norm_num)).2 (by norm_num)

theorem lo_bound : (0.3192697598 : ℝ) < 1009619629 / 1000000000 / Real.sqrt 10 := by
  have hc : 0 < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
  rw [lt_div_iff₀ hc]
  have := sqrt10_lt
  nlinarith

theorem hi_bound : 2524049073 / 2500000000 / Real.sqrt 10 < (0.3192697599 : ℝ) := by
  have hc : 0 < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_iff₀ hc]
  have := sqrt10_gt
  nlinarith

/-- The window, from the two certified chains (as hypotheses). -/
theorem ten_window (hS : ChainTo (1009619629 / 1000000000) Slow)
    (hO : ChainTo (2524049073 / 2500000000) Over) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    0.3192697598 < q 0 ∧ q 0 < 0.3192697599 := by
  obtain ⟨f₁, p₁, q₁, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    core_window (by norm_num) (by norm_num) (by norm_num) hS hO
  have E := Work.FalknerSkan.NegDecay.fs_neg_decay_equal (-1 / 10) (by norm_num) f p q f₁ p₁ q₁
    hf hp hq hf0 hp0 hlim hpos hdec a1 a2 a3 a4 a5 a6 a7 a8 0 (le_refl (0 : ℝ))
  rw [E.2.2]
  exact ⟨lo_bound.trans w1, w2.trans hi_bound⟩

/-- Every solution with q > 0 (no condition on its approach) has q(0) < 0.3192697599. -/
theorem ten_monotone_lt (hS : ChainTo (1009619629 / 1000000000) Slow)
    (hO : ChainTo (2524049073 / 2500000000) Over) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η) :
    q 0 < 0.3192697599 := by
  obtain ⟨f₁, p₁, q₁, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    core_window (by norm_num) (by norm_num) (by norm_num) hS hO
  have M := Work.FalknerSkan.NegDecay.fs_neg_decay_max_shear (-1 / 10) (by norm_num) f₁ p₁ q₁ f p q
    a1 a2 a3 a4 a5 a6 a7 a8 hf hp hq hf0 hp0 hlim hpos
  exact lt_of_le_of_lt M (w2.trans hi_bound)

end Work.FSNeg.NWindow
