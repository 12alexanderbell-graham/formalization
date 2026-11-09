import Mathlib
import Checked.FalknerSkan.FSScale
import Checked.FalknerSkan.BoundedTools
import Work.FalknerSkan.NegUPrime

/-! Run 2026-11-09T0828Z: transport between the β-form Falkner–Skan system with β < 0 and the
scaled adverse-pressure system q' = −K f q + 1 − p² (K = 1/(−β), scaling c = √(−β) of
`Checked.FalknerSkan.FSScale.scale`), and forward uniqueness for the β-form field. -/

namespace Work.FalknerSkan.NegCore

open Set Filter Topology
open Work.FalknerSkan.NegUPrime

/-- The scaled triple of a β-form solution in the monotone class is a `Sol` with K = 1/(−β). -/
theorem toSol {β : ℝ} (hβ : β < 0) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η) :
    Sol (1 / (-β)) (fun s => Real.sqrt (-β) * f (s / Real.sqrt (-β)))
      (fun s => p (s / Real.sqrt (-β))) (fun s => q (s / Real.sqrt (-β)) / Real.sqrt (-β)) := by
  have hb : 0 < -β := by linarith
  have hc : 0 < Real.sqrt (-β) := Real.sqrt_pos.2 hb
  have hc2 : Real.sqrt (-β) ^ 2 = -β := Real.sq_sqrt hb.le
  have hq1 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(1 * f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc hf hp hq1
  refine ⟨A, B, fun s hs => (C s hs).congr_deriv ?_, ?_, ?_,
    Checked.FalknerSkan.FSScale.scale_lim hc hlim, fun s hs => ?_⟩
  · rw [hc2, div_neg β, div_self hβ.ne]; ring
  · simp [hf0]
  · simp [hp0]
  · exact div_pos (hpos _ (div_nonneg (mem_Ici.mp hs) hc.le)) hc

/-- The decay condition is preserved by the scaling. -/
theorem toDec {β : ℝ} (hβ : β < 0) {p q : ℝ → ℝ}
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    ∀ M : ℝ, ∀ᶠ s in atTop, M * (1 - p (s / Real.sqrt (-β))) ≤ q (s / Real.sqrt (-β)) / Real.sqrt (-β) := by
  have hc : 0 < Real.sqrt (-β) := Real.sqrt_pos.2 (by linarith)
  intro M
  filter_upwards [(tendsto_id.atTop_div_const hc).eventually (hdec (M * Real.sqrt (-β)))] with s hs
  rw [le_div_iff₀ hc]
  simp only [id] at hs
  linarith

/-- The first-order β-form field (f, p, q) ↦ (p, q, −f q − β (1 − p²)). -/
def fsVb (β : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (x.2.1, x.2.2, -(x.1 * x.2.2) - β * (1 - x.2.1 ^ 2))

theorem fsVb_lip (β : ℝ) : LocallyLipschitz (fsVb β) := by
  have : ContDiff ℝ 1 (fsVb β) := by unfold fsVb; fun_prop
  exact this.locallyLipschitz

theorem tripleb {β : ℝ} {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η) :
    ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (f t, p t, q t))
      (fsVb β (f η, p η, q η)) (Ici 0) η :=
  fun η hη => (hf η hη).prodMk ((hp η hη).prodMk (hq η hη))

/-- Forward uniqueness for the β-form system from equal data at 0. -/
theorem eq_of_startb {β : ℝ} {f p q f₂ p₂ q₂ : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - β * (1 - p₂ η ^ 2)) (Ici 0) η)
    (h0 : f 0 = f₂ 0) (h1 : p 0 = p₂ 0) (h2 : q 0 = q₂ 0) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  intro η hη
  have hη0 : (0 : ℝ) ≤ η := hη
  have cont : ∀ {f p q : ℝ → ℝ},
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => (f t, p t, q t)) (fsVb β (f η, p η, q η)) (Ici 0) η) →
      ContinuousOn (fun t => (f t, p t, q t)) (Icc 0 η) := fun h x hx =>
    ((h x hx.1).continuousWithinAt).mono (fun _ hy => hy.1)
  have T := tripleb hf hp hq
  have T₂ := tripleb hf₂ hp₂ hq₂
  have key := Checked.FalknerSkan.BoundedTools.uniq_right (fsVb_lip β) (cont T)
    (fun t ht => (T t ht.1).mono (fun y hy => ht.1.trans hy))
    (cont T₂) (fun t ht => (T₂ t ht.1).mono (fun y hy => ht.1.trans hy))
    (by simp only [h0, h1, h2]) ⟨hη0, le_rfl⟩
  simp only [Prod.mk.injEq] at key
  exact key

end Work.FalknerSkan.NegCore
