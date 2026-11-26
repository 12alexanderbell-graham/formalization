import Checked.Trust.NonVacuity
import Checked.FalknerSkan.NegDecay
import Checked.FSRev.RAssembleZ
import Checked.FSRev.RNinetyFiveOver
import Checked.FSRev.RNinetyFiveSlow
import Checked.FSRev.RNinetyFiveTube
import Checked.FSRev.RNinetyFiveZero
import Checked.FSAtt.AWindow
import Checked.FSAtt.RNinetyFiveLo
import Checked.FSAtt.RNinetyFiveHi

/-! Hypothesis necessity for the Falkner–Skan statement on the largest wall shear with adverse pressure gradient
(`Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear`; run 2026-11-26T0628Z): hypothesis 6 (the no-slip condition
of the solution in the fast-approach class) is NEEDED. The witness, at minus nineteen two-hundredths: the
reversed-flow solution of the shooting argument of `Checked.FSRev.RAssembleZ.core_revZ` (certified chains
`RNinetyFiveOver`, `RNinetyFiveSlow`, tube `RNinetyFiveTube`), translated to the point where its stream function
returns to zero, is a solution with zero stream function at the wall, velocity tending to one, positive second
derivative and the fast approach, whose wall velocity is not zero; the cells of `RNinetyFiveZero` locate that point
and bound the scaled second derivative there. The attached solution of `Checked.FSAtt.AWindow.core_window` (chains
`RNinetyFiveLo`, `RNinetyFiveHi`) has a larger scaled wall shear, so its wall shear exceeds that of the translated
solution. Module `NecessityCB`. -/

namespace Checked.Trust.NecessityCB
open Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSAtt.ABase Checked.FSAtt.AFlow
  Checked.FSRev.RZero

/-- The reversed-flow solution of the witness translated to the point where `f` returns to zero: a solution
on the half-line with `f 0 = 0`, `p → 1`, `q > 0`, the fast approach, and a bound on `q 0`. -/
theorem shifted_rev :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-19 / 200) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      q 0 < 53 / 50 / Real.sqrt (200 / 19) := by
  obtain ⟨a, ha, f, p, q, ef, -, eq, hqL, hf, hp, hq, -, -, hlim, -, hdec, -, -⟩ :=
    Checked.FSRev.RAssembleZ.core_revZ (K := 200 / 19) (by norm_num) (by norm_num)
      Checked.FSRev.RNinetyFiveOver.chain Checked.FSRev.RNinetyFiveSlow.chain Checked.FSRev.RNinetyFiveTube.tube
  have hc : 0 < Real.sqrt (200 / 19 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hα : |a - (-902027255852029 / 2000000000000000)| ≤ 95501 / 2000000000000000 := by
    rw [abs_le]; constructor <;> linarith [ha.1, ha.2]
  obtain ⟨Z, E⟩ := Checked.FSRev.RNinetyFiveZero.chainC (Y := flowA (200 / 19) a)
    (fun t ht => (flowA_deriv (200 / 19) a t ht.1).mono Icc_subset_Ici_self) (flowA_zero _ a) hα
  have hneg : (flowA (200 / 19) a (5 / 8)).1 < 0 :=
    (Z (5 / 8) ⟨by norm_num, by norm_num⟩).2.1 (by norm_num)
  have hcont : ContinuousOn (fun t => (flowA (200 / 19) a t).1) (Icc (5 / 8) (3 / 2)) :=
    ((Checked.FSAtt.AAssemble.cont_comp (200 / 19) a (3 / 2)).fst).mono (Icc_subset_Icc (by norm_num) le_rfl)
  obtain ⟨t₀, ht₀, hz⟩ := intermediate_value_Icc (by norm_num) hcont ⟨hneg.le, E.1.le⟩
  have hQ0 : (flowA (200 / 19) a t₀).2.2 < 53 / 50 := by
    have h := (Z t₀ ⟨by linarith [ht₀.1], ht₀.2⟩).2.2 (by push_cast; linarith [ht₀.1]) (le_of_eq hz)
    push_cast at h; exact h
  have hQpos : ∀ t ∈ Icc t₀ (3 / 2), 0 < (flowA (200 / 19) a t).2.2 := fun t ht =>
    (Z t ⟨by linarith [ht₀.1, ht.1], ht.2⟩).1 (by push_cast; linarith [ht₀.1, ht.1])
  set c := Real.sqrt (200 / 19 : ℝ) with hcd
  set s₀ := c * t₀ with hs₀
  have hs₀pos : 0 < s₀ := mul_pos hc (by linarith [ht₀.1])
  have hdiv : s₀ / c = t₀ := by rw [hs₀]; field_simp
  have hK : (-1 / (200 / 19 : ℝ)) = -19 / 200 := by norm_num
  have hin : ∀ η ∈ Ici (0 : ℝ), η + s₀ ∈ Ici (0 : ℝ) := fun η hη => by
    simp only [mem_Ici] at hη ⊢; linarith
  have hnhds : ∀ η ∈ Ici (0 : ℝ), Ici (0 : ℝ) ∈ 𝓝 (η + s₀) := fun η hη =>
    Ici_mem_nhds (by simp only [mem_Ici] at hη; linarith)
  refine ⟨fun η => f (η + s₀), fun η => p (η + s₀), fun η => q (η + s₀), fun η hη => ?_, fun η hη => ?_,
    fun η hη => ?_, ?_, ?_, fun η hη => ?_, fun M => ?_, ?_⟩
  · exact (((hf _ (hin η hη)).hasDerivAt (hnhds η hη)).comp_add_const η s₀).hasDerivWithinAt
  · exact (((hp _ (hin η hη)).hasDerivAt (hnhds η hη)).comp_add_const η s₀).hasDerivWithinAt
  · have h := (((hq _ (hin η hη)).hasDerivAt (hnhds η hη)).comp_add_const η s₀).hasDerivWithinAt
      (s := Ici (0 : ℝ))
    rw [hK] at h; exact h
  · simp only [zero_add]
    simp only at hz
    rw [ef, hdiv, hz, mul_zero]
  · exact hlim.comp (tendsto_atTop_add_const_right _ s₀ tendsto_id)
  · have hη0 : (0 : ℝ) ≤ η := hη
    rcases le_or_gt (η + s₀) (3 / 2 * c) with h | h
    · show 0 < q (η + s₀)
      rw [eq]
      apply div_pos _ hc
      apply hQpos
      constructor
      · rw [le_div_iff₀ hc]; linarith
      · rw [div_le_iff₀ hc]; linarith
    · exact hqL _ h.le
  · exact (tendsto_atTop_add_const_right _ s₀ tendsto_id).eventually (hdec M)
  · simp only [zero_add]; rw [eq, hdiv]
    exact div_lt_div_of_pos_right hQ0 hc

/-- Hypothesis 6 of `fs_neg_decay_max_shear` (`p 0 = 0`) is needed: the translated reversed-flow solution of
`shifted_rev` and the attached solution of `core_window` satisfy every other hypothesis, and the attached wall
shear is the larger. -/
theorem fs_neg_decay_max_shear_h6 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hlim, hpos, hdec, hq0⟩ := shifted_rev
  obtain ⟨g, pg, qg, hg, hpg, hqg, hg0, hpg0, hlg, hposg, -, hlo, -⟩ :=
    Checked.FSAtt.AWindow.core_window (K := 200 / 19) (lo := 1063 / 1000) (hi := 107 / 100) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) Checked.FSAtt.RNinetyFiveLo.chain Checked.FSAtt.RNinetyFiveHi.chain
  have hK : (-1 / (200 / 19 : ℝ)) = -19 / 200 := by norm_num
  have hc : 0 < Real.sqrt (200 / 19 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hlt : (53 / 50 : ℝ) / Real.sqrt (200 / 19) < 1063 / 1000 / Real.sqrt (200 / 19) :=
    div_lt_div_of_pos_right (by norm_num) hc
  refine ⟨-19 / 200, by norm_num, f, p, q, g, pg, qg, hf, hp, hq, hf0, hlim, hpos, hdec, hg, hpg,
    fun η hη => ?_, hg0, hpg0, hlg, hposg, ?_⟩
  · have h := hqg η hη
    rw [hK] at h; exact h
  · intro hle
    linarith

end Checked.Trust.NecessityCB
