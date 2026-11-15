import Checked.FSNeg.NLimit
import Checked.FalknerSkan.FSScale
import Checked.Trust.NonVacuity
import Checked.Trust.NecessityR
import Checked.FalknerSkan.NegWindow
import Checked.FalknerSkan.NegDecay

/-! Hypothesis redundancy for decelerating Falkner–Skan statements: for a decelerating stream, a solution with
`f(0) = 0`, `p(0) = 0` and `q > 0` on the whole half-line reaches the edge velocity, so the edge condition `p → 1`
follows from the other hypotheses even without the fast-approach condition. Overshoot is excluded first: once the
velocity exceeds the edge value by a fixed amount the pressure term pushes the shear down at a fixed rate, so the
shear would turn negative. Below the edge value the slow-approach limit lemma of the attached-flow stack
(`Checked.FSNeg.NLimit.neg_limit`, on the scaled problem) gives the limit. Applied to the strict upper bound of
the attached wall shear at minus one tenth (`fs_neg_tenth_monotone_lt`) and to the comparison theorem of the
decelerating family (`fs_neg_decay_max_shear`). Run 2026-11-15T0628Z. -/

namespace Checked.Trust.NCAL

open Set Filter Topology

/-- For β < 0, a solution of the Falkner–Skan system on the half-line with f(0) = 0, p(0) = 0 and q > 0
everywhere has p → 1. -/
theorem lim_of_pos (β : ℝ) (hβ : β < 0) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0)
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η) :
    Tendsto p atTop (𝓝 1) := by
  have pmono : MonotoneOn p (Ici 0) :=
    Checked.Trust.NCS.monoOn_of_deriv hp (fun η hη => (hpos η hη).le)
  have pnn : ∀ η ∈ Ici (0 : ℝ), 0 ≤ p η := fun η hη => by
    have := pmono (mem_Ici.2 le_rfl) hη (mem_Ici.mp hη); rwa [hp0] at this
  have fmono : MonotoneOn f (Ici 0) := Checked.Trust.NCS.monoOn_of_deriv hf pnn
  have fnn : ∀ η ∈ Ici (0 : ℝ), 0 ≤ f η := fun η hη => by
    have := fmono (mem_Ici.2 le_rfl) hη (mem_Ici.mp hη); rwa [hf0] at this
  have pstrict : StrictMonoOn p (Ici 0) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := q) (convex_Ici 0)
      (HasDerivWithinAt.continuousOn (fun x hx => hp x hx)) (fun x hx => ?_) (fun x hx => ?_)
    · exact (hp x (interior_subset hx)).mono interior_subset
    · exact hpos x (interior_subset hx)
  -- no overshoot
  have hp1 : ∀ η ∈ Ici (0 : ℝ), p η < 1 := by
    intro η₁ hη₁
    by_contra hge
    push Not at hge
    have hη₁0 : (0 : ℝ) ≤ η₁ := hη₁
    set a := η₁ + 1 with ha
    have ha0 : (0 : ℝ) ≤ a := by linarith
    have hpa : p η₁ < p a := pstrict hη₁ (mem_Ici.2 ha0) (by linarith)
    set δ := p a - 1 with hδ
    have hδ0 : 0 < δ := by linarith
    have hsub : Ici a ⊆ Ici (0 : ℝ) := Ici_subset_Ici.2 ha0
    -- g = -q + 2βδ η is monotone on [a, ∞)
    have hg : ∀ η ∈ Ici a, HasDerivWithinAt (fun x => -q x + 2 * β * δ * x)
        (-(-(f η * q η) - β * (1 - p η ^ 2)) + 2 * β * δ) (Ici a) η := by
      intro η hη
      have h1 := ((hq η (hsub hη)).mono hsub).neg
      have h2 := ((hasDerivWithinAt_id η (Ici a)).const_mul (2 * β * δ))
      exact (h1.add h2).congr_deriv (by simp)
    have hg0 : ∀ η ∈ Ici a, 0 ≤ -(-(f η * q η) - β * (1 - p η ^ 2)) + 2 * β * δ := by
      intro η hη
      have hη0 := hsub hη
      have hpη : p a ≤ p η := pmono (mem_Ici.2 ha0) hη0 hη
      have hfq : 0 ≤ f η * q η := mul_nonneg (fnn η hη0) (hpos η hη0).le
      have hsq : 1 + 2 * δ ≤ p η ^ 2 := by nlinarith
      nlinarith
    have gmono : MonotoneOn (fun x => -q x + 2 * β * δ * x) (Ici a) :=
      Checked.Trust.NCS.monoOn_of_deriv hg hg0
    set T := a + q a / (-(2 * β * δ)) + 1 with hT
    have hbd : 0 < -(2 * β * δ) := by nlinarith
    have hqa : 0 < q a := hpos a (mem_Ici.2 ha0)
    have hTa : a ≤ T := by
      have : 0 ≤ q a / (-(2 * β * δ)) := div_nonneg hqa.le hbd.le
      linarith
    have hm := gmono (mem_Ici.2 le_rfl) (mem_Ici.2 hTa) hTa
    simp only at hm
    have hqT : 0 < q T := hpos T (hsub (mem_Ici.2 hTa))
    have hne : 2 * β * δ ≠ 0 := by
      have : 2 * β * δ < 0 := by nlinarith
      exact this.ne
    have e : 2 * β * δ * (q a / (-(2 * β * δ))) = -q a := by
      rw [div_neg, mul_neg, mul_div_cancel₀ (q a) hne]
    have : -q a + 2 * β * δ * a ≤ -q T + 2 * β * δ * T := hm
    rw [hT] at this
    nlinarith
  -- scaled problem and the slow-approach limit lemma
  have hb : 0 < -β := by linarith
  have hc : 0 < Real.sqrt (-β) := Real.sqrt_pos.2 hb
  have hc2 : Real.sqrt (-β) ^ 2 = -β := Real.sq_sqrt hb.le
  have hq1 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(1 * f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc hf hp hq1
  have hK : (0 : ℝ) < 1 / (-β) := one_div_pos.2 hb
  have C' : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => q (s / Real.sqrt (-β)) / Real.sqrt (-β))
      (-(1 / (-β) * (Real.sqrt (-β) * f (s / Real.sqrt (-β))) * (q (s / Real.sqrt (-β)) / Real.sqrt (-β)))
        + 1 - p (s / Real.sqrt (-β)) ^ 2) (Ici 0) s := by
    intro s hs
    refine (C s hs).congr_deriv ?_
    rw [hc2, div_neg β, div_self hβ.ne]; ring
  have hm := Checked.FalknerSkan.FSScale.mapsTo_div hc
  have L := Checked.FSNeg.NLimit.neg_limit hK A B C' le_rfl
    (fun s hs => div_pos (hpos _ (hm hs)) hc) (by simp [hp0]) (fun s hs => hp1 _ (hm hs))
  have hmul : Tendsto (fun η : ℝ => η * Real.sqrt (-β)) atTop atTop :=
    tendsto_id.atTop_mul_const hc
  have := L.comp hmul
  refine this.congr (fun η => ?_)
  simp only [Function.comp, mul_div_assoc, div_self hc.ne', mul_one]

/-- The edge limit `p → 1` is redundant in `fs_neg_tenth_monotone_lt`: it follows from the wall conditions and
the positivity of the shear for a decelerating stream. -/
theorem fs_neg_tenth_monotone_lt_r6 :
    dropped% Checked.FalknerSkan.NegWindow.fs_neg_tenth_monotone_lt 6 := by
  intro f p q hf hp hq hf0 hp0 hpos
  exact Checked.FalknerSkan.NegWindow.fs_neg_tenth_monotone_lt f p q hf hp hq hf0 hp0
    (lim_of_pos (-1 / 10) (by norm_num) f p q hf hp hq hf0 hp0 hpos) hpos

/-- The edge limit `p₂ → 1` of the compared solution is redundant in `fs_neg_decay_max_shear`: it follows from its
wall conditions and the positivity of its shear for a decelerating stream. -/
theorem fs_neg_decay_max_shear_r15 :
    dropped% Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear 15 := by
  intro β hβ f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hpos hdec hf₂ hp₂ hq₂ hf₂0 hp₂0 hpos₂
  exact Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear β hβ f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hpos hdec
    hf₂ hp₂ hq₂ hf₂0 hp₂0 (lim_of_pos β hβ f₂ p₂ q₂ hf₂ hp₂ hq₂ hf₂0 hp₂0 hpos₂) hpos₂

end Checked.Trust.NCAL
