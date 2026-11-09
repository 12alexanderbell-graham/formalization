import Mathlib
import Work.FalknerSkan.NegReversed

/-!
# Falkner–Skan β = −1/10, reversed flow and two decay-class solutions: the blind restatement,
# closed (run 2026-11-09T1228Z)

The definitions and the theorems `reversed`, `two_decay` are the blind restater's text (Sonnet,
from the claims in words only; `runs/2026-11-09T1228Z/blind2/NegReversedBlind.lean`, brief next to
it), copied verbatim with the placeholder proofs replaced by proofs from
`Work.FalknerSkan.NegReversed.fs_neg_tenth_reversed` and `fs_neg_tenth_two_decay`; `toBlind` is
program text, not blind text.
-/

namespace Blind.NegReversed

open Set Filter Topology

/-- One-sided derivative on the half-line `[0, ∞)`. -/
noncomputable def D (g : ℝ → ℝ) : ℝ → ℝ := derivWithin g (Ici 0)

/-- Falkner–Skan pressure-gradient parameter. -/
noncomputable def β : ℝ := -1 / 10

/-- `f` solves the Falkner–Skan BVP with parameter `β = -1/10`, has `-1 ≤ f' ≤ 1`
on `[0,∞)`, and the growth property
`∀ M, ∀ᶠ η, M * (1 - f' η) ≤ f'' η`. -/
structure IsSol (f : ℝ → ℝ) : Prop where
  smooth : ContDiffOn ℝ 3 f (Ici 0)
  ode : ∀ η ∈ Ici (0 : ℝ), D (D (D f)) η + f η * D (D f) η + β * (1 - (D f η) ^ 2) = 0
  f0 : f 0 = 0
  f'0 : D f 0 = 0
  f'_lim : Tendsto (D f) atTop (𝓝 1)
  bounds : ∀ η ∈ Ici (0 : ℝ), -1 ≤ D f η ∧ D f η ≤ 1
  decay : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - D f η) ≤ D (D f) η

/-- Program lemma (not blind text; pattern of `Blind.NegOutside.toBlind`): a solution in the
program's form with −1 ≤ p ≤ 1 and the decay property is a blind `IsSol`, with `D f = p` and
`D (D f) = q` on `Ici 0`. -/
theorem toBlind {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    IsSol f ∧ EqOn (D f) p (Ici 0) ∧ EqOn (D (D f)) q (Ici 0) := by
  have hU : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have e1 : EqOn (D f) p (Ici 0) := fun η hη => (hf η hη).derivWithin (hU η hη)
  have e2 : EqOn (D (D f)) q (Ici 0) := fun η hη => by
    show derivWithin (D f) (Ici 0) η = q η
    rw [derivWithin_congr e1 (e1 hη)]; exact (hp η hη).derivWithin (hU η hη)
  have e3 : ∀ η ∈ Ici (0 : ℝ), D (D (D f)) η = -(f η * q η) - (-1 / 10) * (1 - p η ^ 2) :=
    fun η hη => by
    show derivWithin (D (D f)) (Ici 0) η = _
    rw [derivWithin_congr e2 (e2 hη)]; exact (hq η hη).derivWithin (hU η hη)
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
  refine ⟨⟨C3, fun η hη => ?_, hf0, ?_, ?_, fun η hη => ?_, fun M => ?_⟩, e1, e2⟩
  · rw [e3 η hη, e2 hη, e1 hη]; unfold β; ring
  · rw [e1 h0]; exact hp0
  · refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (e1 (mem_Ici.2 ht)).symm
  · rw [e1 hη]; exact hb η hη
  · filter_upwards [hdec M, eventually_ge_atTop (0 : ℝ)] with η h1 h2
    rw [e1 (mem_Ici.2 h2), e2 (mem_Ici.2 h2)]; exact h1

theorem reversed :
    ∃ f : ℝ → ℝ, IsSol f ∧
      (-1405462131 / 10000000000 : ℝ) < D (D f) 0 ∧
      D (D f) 0 < (-1405462129 / 10000000000 : ℝ) := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Work.FalknerSkan.NegReversed.fs_neg_tenth_reversed
  obtain ⟨s, -, e2⟩ := toBlind a1 a2 a3 a4 a5 a6 a7 a8
  refine ⟨f, s, ?_, ?_⟩ <;> rw [e2 (mem_Ici.2 le_rfl)] <;> norm_num at w1 w2 ⊢ <;> linarith

theorem two_decay :
    ∃ f g : ℝ → ℝ, IsSol f ∧ IsSol g ∧ D (D f) 0 ≠ D (D g) 0 := by
  obtain ⟨f, p, q, f₂, p₂, q₂, a1, a2, a3, b1, b2, b3, a4, a5, b4, b5, a6, b6, hb, hb₂, hd, hd₂,
    hne⟩ := Work.FalknerSkan.NegReversed.fs_neg_tenth_two_decay
  obtain ⟨s, -, e2⟩ := toBlind a1 a2 a3 a4 a5 a6 hb hd
  obtain ⟨s₂, -, e2₂⟩ := toBlind b1 b2 b3 b4 b5 b6 hb₂ hd₂
  refine ⟨f, f₂, s, s₂, ?_⟩
  rw [e2 (mem_Ici.2 le_rfl), e2₂ (mem_Ici.2 le_rfl)]; exact hne

end Blind.NegReversed
