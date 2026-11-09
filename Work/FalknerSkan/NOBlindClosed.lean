import Mathlib
import Work.FalknerSkan.NegOutside

/-!
# Falkner–Skan β = −1/10, two solutions outside the decay class: the blind restatement, closed (run 2026-11-09T1028Z)

The definitions and `two_outside` are the blind restater's text (Sonnet, from the claim in words only;
`runs/2026-11-09T1028Z/blind/NegOutsideBlind.lean`, brief next to it), copied verbatim with the
placeholder proof replaced by a proof from `Work.FalknerSkan.NegOutside.fs_neg_tenth_not_unique_outside`;
the transport lemma `toBlind` (pattern of `Work.Blasius.BlindClosed`) is program text, not blind text.
-/

namespace Blind.NegOutside

open Set Filter Topology

/-- First, second, third one-sided derivatives on `[0,∞)`. -/
noncomputable def d1 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin f (Ici 0)
noncomputable def d2 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (d1 f) (Ici 0)
noncomputable def d3 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (d2 f) (Ici 0)

/-- `f` solves Falkner–Skan with parameter `β` on `[0,∞)` with the stated boundary conditions. -/
def IsSol (β : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 3 f (Ici 0) ∧
  (∀ η ∈ Ici (0:ℝ), d3 f η + f η * d2 f η + β * (1 - (d1 f η) ^ 2) = 0) ∧
  f 0 = 0 ∧ d1 f 0 = 0 ∧
  Tendsto (d1 f) atTop (𝓝 1)

/-- Positivity of `f''` and `0 ≤ f' ≤ 1` on the half-line. -/
def Monotone' (f : ℝ → ℝ) : Prop :=
  ∀ η ∈ Ici (0:ℝ), 0 < d2 f η ∧ 0 ≤ d1 f η ∧ d1 f η ≤ 1

/-- The property "for every `M`, eventually `M (1 - f') ≤ f''`". -/
def DominatesAll (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - d1 f η) ≤ d2 f η

/-- Program lemma (not blind text): a solution in the program's form (f, p, q with one-sided
derivatives on `Ici 0`) is a blind `IsSol`, with `d1 f = p` and `d2 f = q` on `Ici 0`. -/
theorem toBlind {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    IsSol (-1/10) f ∧ EqOn (d1 f) p (Ici 0) ∧ EqOn (d2 f) q (Ici 0) := by
  have hU : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have e1 : EqOn (d1 f) p (Ici 0) := fun η hη => (hf η hη).derivWithin (hU η hη)
  have e2 : EqOn (d2 f) q (Ici 0) := fun η hη => by
    unfold d2; rw [derivWithin_congr e1 (e1 hη)]; exact (hp η hη).derivWithin (hU η hη)
  have e3 : ∀ η ∈ Ici (0 : ℝ), d3 f η = -(f η * q η) - (-1 / 10) * (1 - p η ^ 2) := fun η hη => by
    unfold d3; rw [derivWithin_congr e2 (e2 hη)]; exact (hq η hη).derivWithin (hU η hη)
  have cf : ContinuousOn f (Ici 0) := fun η hη => (hf η hη).continuousWithinAt
  have cp : ContinuousOn p (Ici 0) := fun η hη => (hp η hη).continuousWithinAt
  have cq : ContinuousOn q (Ici 0) := fun η hη => (hq η hη).continuousWithinAt
  have dq : DifferentiableOn ℝ q (Ici 0) := fun η hη => (hq η hη).differentiableWithinAt
  have dp : DifferentiableOn ℝ p (Ici 0) := fun η hη => (hp η hη).differentiableWithinAt
  have df : DifferentiableOn ℝ f (Ici 0) := fun η hη => (hf η hη).differentiableWithinAt
  have C0 : ContDiffOn ℝ 0 (fun η => -(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) :=
    contDiffOn_zero.2 (((cf.mul cq).neg).sub (continuousOn_const.mul (continuousOn_const.sub (cp.pow 2))))
  have C1 : ContDiffOn ℝ 1 q (Ici 0) := by
    refine (contDiffOn_succ_iff_derivWithin (n := 0) hU).2 ⟨dq, by simp, ?_⟩
    exact C0.congr fun η hη => ((hq η hη).derivWithin (hU η hη))
  have C2 : ContDiffOn ℝ 2 p (Ici 0) := by
    refine (contDiffOn_succ_iff_derivWithin (n := 1) hU).2 ⟨dp, by simp, ?_⟩
    exact C1.congr fun η hη => ((hp η hη).derivWithin (hU η hη))
  have C3 : ContDiffOn ℝ 3 f (Ici 0) := by
    refine (contDiffOn_succ_iff_derivWithin (n := 2) hU).2 ⟨df, by simp, ?_⟩
    exact C2.congr e1
  have h0 : (0 : ℝ) ∈ Ici 0 := mem_Ici.2 le_rfl
  refine ⟨⟨C3, fun η hη => ?_, hf0, ?_, ?_⟩, e1, e2⟩
  · rw [e3 η hη, e2 hη, e1 hη]; ring
  · rw [e1 h0]; exact hp0
  · refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (e1 (mem_Ici.2 ht)).symm

/-- Program lemma (not blind text): failing the decay condition transports. -/
theorem notDom {f p q : ℝ → ℝ} (e1 : EqOn (d1 f) p (Ici 0)) (e2 : EqOn (d2 f) q (Ici 0))
    (h : ¬ (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η)) : ¬ DominatesAll f := by
  intro hd
  apply h
  intro M
  filter_upwards [hd M, eventually_ge_atTop (0 : ℝ)] with η h1 h2
  rwa [e1 (mem_Ici.2 h2), e2 (mem_Ici.2 h2)] at h1

theorem two_outside :
    ∃ f g : ℝ → ℝ,
      IsSol (-1/10) f ∧ IsSol (-1/10) g ∧
      Monotone' f ∧ Monotone' g ∧
      ¬ DominatesAll f ∧ ¬ DominatesAll g ∧
      d2 f 0 ≠ d2 g 0 := by
  obtain ⟨f, p, q, f₂, p₂, q₂, hf, hp, hq, hf₂, hp₂, hq₂, h0, h1, h2, h3, hl, hl₂, hb, hb₂,
    hn, hn₂, hne⟩ := Work.FalknerSkan.NegOutside.fs_neg_tenth_not_unique_outside
  obtain ⟨s, e1, e2⟩ := toBlind hf hp hq h0 h1 hl
  obtain ⟨s₂, e1₂, e2₂⟩ := toBlind hf₂ hp₂ hq₂ h2 h3 hl₂
  have z : (0 : ℝ) ∈ Ici 0 := mem_Ici.2 le_rfl
  refine ⟨f, f₂, s, s₂, fun η hη => ?_, fun η hη => ?_, notDom e1 e2 hn, notDom e1₂ e2₂ hn₂, ?_⟩
  · rw [e1 hη, e2 hη]; exact hb η hη
  · rw [e1₂ hη, e2₂ hη]; exact hb₂ η hη
  · rw [e2 z, e2₂ z]; exact hne

end Blind.NegOutside
