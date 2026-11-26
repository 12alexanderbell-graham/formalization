import Mathlib
/-!
Closure of the blind restatement of the H₂⁺ claim (run 2026-11-26T1628Z) against the freeze
`runs/2026-11-26T1628Z/lean/H2PlusSigmaG.lean` (second freeze, with the integrability conjunct).

`Freeze` is the frozen statement verbatim (as a proposition); `Blind` is `runs/2026-11-26T1628Z/blind/H2PlusBlind.lean`
verbatim except `IntegrableOn` → `MeasureTheory.IntegrableOn` (the restater's file did not open `MeasureTheory`;
it did not compile as written). The two are equivalent: the separation constants are opposite (A_blind = −A),
and the blind file writes the equations expanded with a second derivative where the freeze writes them in
flux form.
-/

namespace Work.Quantum.H2PlusBlindClosed
open Set Filter Topology

def Freeze : Prop :=
    ∃ E ∈ Icc (-0.6026342144950 : ℝ) (-0.6026342144949), ∃ A : ℝ, ∃ L L' M M' : ℝ → ℝ,
      ContinuousOn L (Ici 1) ∧
      (∀ ξ ∈ Ioi (1 : ℝ), HasDerivAt L (L' ξ) ξ) ∧
      (∀ ξ ∈ Ioi (1 : ℝ), HasDerivAt (fun x => (x ^ 2 - 1) * L' x)
        (-((4 * ξ + 2 * (E - 1 / 2) * ξ ^ 2 + A) * L ξ)) ξ) ∧
      (∀ ξ ∈ Ici (1 : ℝ), 0 < L ξ) ∧
      Tendsto L atTop (𝓝 0) ∧
      MeasureTheory.IntegrableOn (fun ξ => L ξ ^ 2 * ξ ^ 2) (Ici 1) ∧
      ContinuousOn M (Icc (-1) 1) ∧
      (∀ η ∈ Ioo (-1 : ℝ) 1, HasDerivAt M (M' η) η) ∧
      (∀ η ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun x => (1 - x ^ 2) * M' x)
        ((2 * (E - 1 / 2) * η ^ 2 + A) * M η) η) ∧
      (∀ η ∈ Icc (-1 : ℝ) 1, 0 < M η)

/-- Radial (ξ) equation, expanded: (ξ²-1) L'' + 2ξ L' + (4ξ + 2εξ² - A) L = 0. -/
def RadialEq (ε A : ℝ) (L L' L'' : ℝ → ℝ) : Prop :=
  ∀ ξ ∈ Ioi (1 : ℝ),
    HasDerivAt L (L' ξ) ξ ∧ HasDerivAt L' (L'' ξ) ξ ∧
    (ξ ^ 2 - 1) * L'' ξ + 2 * ξ * L' ξ + (4 * ξ + 2 * ε * ξ ^ 2 - A) * L ξ = 0

/-- Angular (η) equation, expanded: (1-η²) M'' - 2η M' + (A - 2εη²) M = 0. -/
def AngularEq (ε A : ℝ) (M M' M'' : ℝ → ℝ) : Prop :=
  ∀ η ∈ Ioo (-1 : ℝ) 1,
    HasDerivAt M (M' η) η ∧ HasDerivAt M' (M'' η) η ∧
    (1 - η ^ 2) * M'' η - 2 * η * M' η + (A - 2 * ε * η ^ 2) * M η = 0

def Blind : Prop :=
    ∃ (E A : ℝ) (L L' L'' M M' M'' : ℝ → ℝ),
      E ∈ Icc (-0.6026342144950 : ℝ) (-0.6026342144949) ∧
      RadialEq (E - 1 / 2) A L L' L'' ∧
      AngularEq (E - 1 / 2) A M M' M'' ∧
      ContinuousOn L (Ici 1) ∧
      ContinuousOn M (Icc (-1) 1) ∧
      Tendsto L atTop (nhds 0) ∧
      MeasureTheory.IntegrableOn (fun ξ => L ξ ^ 2 * ξ ^ 2) (Ici 1) ∧
      (∀ ξ ∈ Ici (1 : ℝ), 0 < L ξ) ∧
      (∀ η ∈ Icc (-1 : ℝ) 1, 0 < M η)

/-- A function whose product with a nonvanishing differentiable weight is differentiable is differentiable,
with the derivative given by the quotient rule. -/
lemma deriv_of_weighted {f w : ℝ → ℝ} {F w' : ℝ} {x : ℝ} (hF : HasDerivAt (fun t => w t * f t) F x)
    (hw : HasDerivAt w w' x) (hw0 : w x ≠ 0) :
    HasDerivAt f ((F - w' * f x) / w x) x := by
  have hq := hF.div hw hw0
  have hev : (fun t => w t * f t / w t) =ᶠ[𝓝 x] f := by
    have : ∀ᶠ t in 𝓝 x, w t ≠ 0 := hw.continuousAt.eventually_ne hw0
    filter_upwards [this] with t ht
    field_simp
  have h2 := hq.congr_of_eventuallyEq hev.symm
  convert h2 using 1
  field_simp

theorem freeze_to_blind : Freeze → Blind := by
  rintro ⟨E, hE, A, L, L', M, M', hLc, hL, hLf, hLpos, hLt, hLint, hMc, hM, hMf, hMpos⟩
  refine ⟨E, -A, L, L', fun ξ => (-((4 * ξ + 2 * (E - 1 / 2) * ξ ^ 2 + A) * L ξ) - 2 * ξ * L' ξ) / (ξ ^ 2 - 1),
    M, M', fun η => ((2 * (E - 1 / 2) * η ^ 2 + A) * M η - (-2 * η) * M' η) / (1 - η ^ 2),
    hE, ?_, ?_, hLc, hMc, hLt, hLint, hLpos, hMpos⟩
  · intro ξ hξ
    have hξ' : (1 : ℝ) < ξ := hξ
    have hw0 : ξ ^ 2 - 1 ≠ 0 := by nlinarith
    have hw : HasDerivAt (fun x : ℝ => x ^ 2 - 1) (2 * ξ) ξ := by
      simpa using (hasDerivAt_pow 2 ξ).sub_const 1
    refine ⟨hL ξ hξ, deriv_of_weighted (hLf ξ hξ) hw hw0, ?_⟩
    field_simp
    ring
  · intro η hη
    have h1 : -1 < η := hη.1
    have h2 : η < 1 := hη.2
    have hw0 : 1 - η ^ 2 ≠ 0 := by nlinarith
    have hw : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * η) η := by
      simpa using (hasDerivAt_pow 2 η).const_sub 1
    refine ⟨hM η hη, deriv_of_weighted (hMf η hη) hw hw0, ?_⟩
    field_simp
    ring

theorem blind_to_freeze : Blind → Freeze := by
  rintro ⟨E, A, L, L', L'', M, M', M'', hE, hR, hA, hLc, hMc, hLt, hLint, hLpos, hMpos⟩
  refine ⟨E, hE, -A, L, L', M, M', hLc, fun ξ hξ => (hR ξ hξ).1, ?_, hLpos, hLt, hLint, hMc,
    fun η hη => (hA η hη).1, ?_, hMpos⟩
  · intro ξ hξ
    obtain ⟨_, h2, h3⟩ := hR ξ hξ
    have hw : HasDerivAt (fun x : ℝ => x ^ 2 - 1) (2 * ξ) ξ := by
      simpa using (hasDerivAt_pow 2 ξ).sub_const 1
    convert hw.mul h2 using 1
    linear_combination -h3
  · intro η hη
    obtain ⟨_, h2, h3⟩ := hA η hη
    have hw : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * η) η := by
      simpa using (hasDerivAt_pow 2 η).const_sub 1
    convert hw.mul h2 using 1
    linear_combination -h3

theorem freeze_iff_blind : Freeze ↔ Blind := ⟨freeze_to_blind, blind_to_freeze⟩

end Work.Quantum.H2PlusBlindClosed
