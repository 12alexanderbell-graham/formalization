import Mathlib
import Work.FalknerSkan.Neg1988Rev

/-!
# Falkner–Skan at β = −0.1988, reversed-flow branch: the blind restatement, closed (run 2026-11-11T1228Z)

The definitions and theorems below are the blind restater's text (Sonnet, from the claims in words only;
`runs/2026-11-11T1228Z/blind/Neg1988RevBlind.lean`, brief 579e291), copied verbatim by
`runs/2026-11-11T1228Z/scripts/close_blind.py` with the placeholder proofs replaced by proofs from
`Work.FalknerSkan.Neg1988Rev` (helper lemmas inserted before the theorems).
-/

open Filter Set

namespace Neg1988RevBlind

/-- The wall-parameter beta = -0.1988. -/
noncomputable def β : ℝ := -0.1988

/-- First derivative on `[0, ∞)`. -/
noncomputable def d1 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin f (Ici 0)
/-- Second derivative on `[0, ∞)`. -/
noncomputable def d2 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (d1 f) (Ici 0)
/-- Third derivative on `[0, ∞)`. -/
noncomputable def d3 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (d2 f) (Ici 0)

/-- Falkner–Skan ODE on the closed half-line, with `C³` regularity there
(no boundary conditions). -/
def FSOde (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 3 f (Ici 0) ∧
  ∀ η ∈ Ici (0 : ℝ), d3 f η + f η * d2 f η + β * (1 - (d1 f η) ^ 2) = 0

/-- Wall conditions `f(0) = 0`, `f'(0) = 0`. -/
def Wall (f : ℝ → ℝ) : Prop := f 0 = 0 ∧ d1 f 0 = 0

/-- Far-field condition `f' → 1`. -/
def Outer (f : ℝ → ℝ) : Prop := Tendsto (d1 f) atTop (nhds 1)

/-- Approach to the outer flow faster than any exponential rate. -/
def SuperExp (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - d1 f η) ≤ d2 f η

/-- Full boundary-value problem solution. -/
def FSSol (f : ℝ → ℝ) : Prop := FSOde f ∧ Wall f ∧ Outer f

theorem β_eq : β = -1988 / 10000 := by unfold β; norm_num

/-- C³ on [0, ∞) from a chain of one-sided derivatives with a continuous last derivative
(run 1028Z's `Neg1988Blind.cdo_of`). -/
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

/-- A solution in the program's form is a blind solution, with d1 f = p and d2 f = q on [0, ∞). -/
theorem transfer {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (nhds 1)) :
    FSSol f ∧ (∀ η ∈ Ici (0 : ℝ), d1 f η = p η) ∧ (∀ η ∈ Ici (0 : ℝ), d2 f η = q η) := by
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
  refine ⟨⟨⟨cdo_of hf hp hq hr, fun η hη => ?_⟩, ⟨hf0, by rw [E1 0 (mem_Ici.2 le_rfl), hp0]⟩,
    hlim.congr' (ev E1).symm⟩, E1, E2⟩
  rw [E1 η hη, E2 η hη, E3 η hη, β_eq]; ring

theorem superExp_of {f p q : ℝ → ℝ} (E1 : ∀ η ∈ Ici (0 : ℝ), d1 f η = p η)
    (E2 : ∀ η ∈ Ici (0 : ℝ), d2 f η = q η) (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    SuperExp f := fun M => by
  filter_upwards [hdec M, eventually_ge_atTop 0] with η h1 h2
  rw [E1 η h2, E2 η h2]; exact h1

theorem blind_rev_window :
    ∃ f : ℝ → ℝ, FSSol f ∧ (∀ η ∈ Ici (0 : ℝ), |d1 f η| ≤ 1) ∧ SuperExp f ∧
      (-0.00515743 : ℝ) < d2 f 0 ∧ d2 f 0 < -0.00515741 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hb, hdec, w1, w2⟩ :=
    Work.FalknerSkan.Neg1988Rev.fs_neg1988_reversed
  obtain ⟨S, E1, E2⟩ := transfer hf hp hq hf0 hp0 hlim
  refine ⟨f, S, fun η hη => ?_, superExp_of E1 E2 hdec, ?_, ?_⟩
  · rw [E1 η hη, abs_le]; exact hb η hη
  · rw [E2 0 (mem_Ici.2 le_rfl)]; exact w1
  · rw [E2 0 (mem_Ici.2 le_rfl)]; exact w2

theorem blind_rev_printed (f : ℝ → ℝ) (hf : FSOde f) (hw : Wall f)
    (h2 : d2 f 0 = -0.005158) :
    ∃ η : ℝ, 0 < η ∧ 1 < d1 f η := by
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have hC := hf.1
  have C1 : ContDiffOn ℝ 2 (d1 f) (Ici 0) := hC.derivWithin hu (by norm_num)
  have C2 : ContDiffOn ℝ 1 (d2 f) (Ici 0) := C1.derivWithin hu (by norm_num)
  obtain ⟨η, hη, h⟩ := Work.FalknerSkan.Neg1988Rev.fs_neg1988_printed_reversed_overshoots f (d1 f) (d2 f)
    (fun η hη => ((hC.differentiableOn (by norm_num)) η hη).hasDerivWithinAt)
    (fun η hη => ((C1.differentiableOn (by norm_num)) η hη).hasDerivWithinAt)
    (fun η hη => by
      refine ((C2.differentiableOn (by norm_num)) η hη).hasDerivWithinAt.congr_deriv ?_
      have := hf.2 η hη
      rw [β_eq] at this
      change d3 f η = _
      linarith) hw.1 hw.2 h2
  exact ⟨η, hη, h⟩

theorem blind_rev_two :
    ∃ f g : ℝ → ℝ, FSSol f ∧ FSSol g ∧
      (∀ η ∈ Ici (0 : ℝ), |d1 f η| ≤ 1) ∧ (∀ η ∈ Ici (0 : ℝ), |d1 g η| ≤ 1) ∧
      SuperExp f ∧ SuperExp g ∧ d2 f 0 ≠ d2 g 0 := by
  obtain ⟨f, p, q, f₂, p₂, q₂, a1, a2, a3, b1, b2, b3, a4, a5, b4, b5, a6, b6, a7, b7, a8, b8, hne⟩ :=
    Work.FalknerSkan.Neg1988Rev.fs_neg1988_two_decay
  obtain ⟨S, E1, E2⟩ := transfer a1 a2 a3 a4 a5 a6
  obtain ⟨S₂, F1, F2⟩ := transfer b1 b2 b3 b4 b5 b6
  refine ⟨f, f₂, S, S₂, fun η hη => ?_, fun η hη => ?_, superExp_of E1 E2 a8, superExp_of F1 F2 b8, ?_⟩
  · rw [E1 η hη, abs_le]; exact a7 η hη
  · rw [F1 η hη, abs_le]; exact b7 η hη
  · rw [E2 0 (mem_Ici.2 le_rfl), F2 0 (mem_Ici.2 le_rfl)]; exact hne

end Neg1988RevBlind
