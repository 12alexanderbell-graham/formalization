import Mathlib
import Work.FalknerSkan.Neg1988

/-!
# Falkner–Skan at β = −0.1988: the blind restatement, closed (run 2026-11-11T1028Z)

The definitions and theorems below are the blind restater's text (Sonnet, from the claims in words only;
`runs/2026-11-11T1028Z/blind/Neg1988Blind.lean`, brief dc5a294), copied verbatim with the placeholder proofs
replaced by proofs from `Work.FalknerSkan.Neg1988.fs_neg1988_window` and `fs_neg1988_exists_decay`. The blind
solution is C³ on [0, ∞) with nested `derivWithin` derivatives; the frozen statements use one-sided
`HasDerivWithinAt` facts. Window: C³ gives those facts. Existence: the derivative facts give C³ on [0, ∞)
(`contDiffOn_succ_iff_derivWithin` three times) and the nested `derivWithin` values.
-/

open Set Filter

namespace Neg1988Blind

/-- The wall-shear parameter. -/
noncomputable def β : ℝ := -0.1988

/-- First derivative on the half-line `[0, ∞)`. -/
noncomputable def d1 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin f (Ici 0)
/-- Second derivative on the half-line. -/
noncomputable def d2 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (d1 f) (Ici 0)
/-- Third derivative on the half-line. -/
noncomputable def d3 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (d2 f) (Ici 0)

/-- `f` solves the Falkner–Skan boundary value problem on `η ≥ 0`
with `β = -0.1988`, `f 0 = 0`, `f' 0 = 0`, `f' → 1`. -/
structure IsSolution (f : ℝ → ℝ) : Prop where
  smooth : ContDiffOn ℝ 3 f (Ici 0)
  ode : ∀ η ∈ Ici (0 : ℝ),
    d3 f η + f η * d2 f η + β * (1 - (d1 f η) ^ 2) = 0
  f_zero : f 0 = 0
  f'_zero : d1 f 0 = 0
  f'_tendsto : Tendsto (d1 f) atTop (nhds 1)

/-- Attached: `f'' > 0` for every `η ≥ 0`. -/
def Attached (f : ℝ → ℝ) : Prop := ∀ η ∈ Ici (0 : ℝ), 0 < d2 f η

/-- Faster than any exponential rate: for every real `M`, eventually
`M * (1 - f') ≤ f''`. -/
def SuperExpApproach (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - d1 f η) ≤ d2 f η

theorem β_eq : β = -1988 / 10000 := by unfold β; norm_num

theorem blind_neg1988_window (f : ℝ → ℝ) (hf : IsSolution f)
    (hatt : Attached f) (hfast : SuperExpApproach f) :
    (0.0052181 : ℝ) < d2 f 0 ∧ d2 f 0 < 0.0052182 := by
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have hC := hf.smooth
  have C1 : ContDiffOn ℝ 2 (d1 f) (Ici 0) := hC.derivWithin hu (by norm_num)
  have C2 : ContDiffOn ℝ 1 (d2 f) (Ici 0) := C1.derivWithin hu (by norm_num)
  refine Work.FalknerSkan.Neg1988.fs_neg1988_window f (d1 f) (d2 f) (fun η hη => ?_) (fun η hη => ?_)
    (fun η hη => ?_) hf.f_zero hf.f'_zero hf.f'_tendsto hatt hfast
  · exact ((hC.differentiableOn (by norm_num)) η hη).hasDerivWithinAt
  · exact ((C1.differentiableOn (by norm_num)) η hη).hasDerivWithinAt
  · refine ((C2.differentiableOn (by norm_num)) η hη).hasDerivWithinAt.congr_deriv ?_
    have := hf.ode η hη
    rw [β_eq] at this
    change d3 f η = _
    linarith

/-- C³ on [0, ∞) from a chain of one-sided derivatives with a continuous last derivative. -/
theorem cdo_of {f p q r : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (r η) (Ici 0) η)
    (hr : ContinuousOn r (Ici 0)) : ContDiffOn ℝ 3 f (Ici 0) := by
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have e : ∀ {g g' : ℝ → ℝ}, (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt g (g' η) (Ici 0) η) →
      ∀ η ∈ Ici (0 : ℝ), derivWithin g (Ici 0) η = g' η :=
    fun h η hη => (h η hη).derivWithin (hu η hη)
  have Q : ContDiffOn ℝ 1 q (Ici 0) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_derivWithin hu]
    refine ⟨fun η hη => (hq η hη).differentiableWithinAt, by simp, ?_⟩
    exact (contDiffOn_zero.2 hr).congr (e hq)
  have P : ContDiffOn ℝ 2 p (Ici 0) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_derivWithin hu]
    exact ⟨fun η hη => (hp η hη).differentiableWithinAt, by simp, Q.congr (e hp)⟩
  rw [show (3 : WithTop ℕ∞) = 2 + 1 from rfl, contDiffOn_succ_iff_derivWithin hu]
  exact ⟨fun η hη => (hf η hη).differentiableWithinAt, by simp, P.congr (e hf)⟩

theorem blind_neg1988_exists :
    ∃ f : ℝ → ℝ, IsSolution f ∧ Attached f ∧ SuperExpApproach f := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, hdec⟩ :=
    Work.FalknerSkan.Neg1988.fs_neg1988_exists_decay
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have E1 : ∀ η ∈ Ici (0 : ℝ), d1 f η = p η := fun η hη => (hf η hη).derivWithin (hu η hη)
  have hp' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (d1 f) (q η) (Ici 0) η :=
    fun η hη => (hp η hη).congr (fun x hx => E1 x hx) (E1 η hη)
  have E2 : ∀ η ∈ Ici (0 : ℝ), d2 f η = q η := fun η hη => (hp' η hη).derivWithin (hu η hη)
  have hq' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (d2 f)
      (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η :=
    fun η hη => (hq η hη).congr (fun x hx => E2 x hx) (E2 η hη)
  have E3 : ∀ η ∈ Ici (0 : ℝ), d3 f η = -(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2) :=
    fun η hη => (hq' η hη).derivWithin (hu η hη)
  have cf : ContinuousOn f (Ici 0) := fun η hη => (hf η hη).continuousWithinAt
  have cp : ContinuousOn p (Ici 0) := fun η hη => (hp η hη).continuousWithinAt
  have cq : ContinuousOn q (Ici 0) := fun η hη => (hq η hη).continuousWithinAt
  have hr : ContinuousOn (fun η => -(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) :=
    ((cf.mul cq).neg).sub (continuousOn_const.mul (continuousOn_const.sub (cp.pow 2)))
  have ev : ∀ {u v : ℝ → ℝ}, (∀ η ∈ Ici (0 : ℝ), u η = v η) → u =ᶠ[atTop] v :=
    fun h => (eventually_ge_atTop 0).mono (fun η hη => h η hη)
  refine ⟨f, ⟨cdo_of hf hp hq hr, fun η hη => ?_, hf0, by rw [E1 0 (mem_Ici.2 le_rfl), hp0],
    hlim.congr' (ev E1).symm⟩, fun η hη => by rw [E2 η hη]; exact hpos η hη, fun M => ?_⟩
  · rw [E1 η hη, E2 η hη, E3 η hη, β_eq]; ring
  · filter_upwards [hdec M, eventually_ge_atTop 0] with η h1 h2
    rw [E1 η h2, E2 η h2]; exact h1

end Neg1988Blind
