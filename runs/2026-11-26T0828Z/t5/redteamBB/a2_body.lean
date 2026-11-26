open Set Filter Topology
namespace RB2
namespace SecondReading
/-- P a b: "the interval (a,b) contains [A,B] (A, B spelled as naturals times 1e-10), or a solution has wall value in (a,b)" -/
def P (a b : ℝ) : Prop :=
  (a ≤ (0.0000000001 : ℝ) * ((12325876568 : ℕ) : ℝ) ∧ (0.0000000001 : ℝ) * ((12325876569 : ℕ) : ℝ) ≤ b) ∨
  ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    q 0 < b ∧ a < q 0
def rn : Prop := P 1.2325876568 1.2325876569
end SecondReading

theorem cl : ∀ a b : ℝ, SecondReading.P a b ↔ ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    a < q 0 ∧ q 0 < b := by
  intro a b
  unfold SecondReading.P
  constructor
  · rintro (⟨h1, h2⟩ | ⟨f, p, q, h1, h2, h3, h4, h5, h6, h7, h8⟩)
    · obtain ⟨f, p, q, h1, h2, h3, h4, h5, h6, h7, h8⟩ := Checked.Hiemenz.hiemenz_exists
      refine ⟨f, p, q, h1, h2, h3, h4, h5, h6, ?_, ?_⟩
      · norm_num at h1 h2 h7 ⊢; linarith
      · norm_num at h1 h2 h8 ⊢; linarith
    · exact ⟨f, p, q, h1, h2, h3, h4, h5, h6, h8, h7⟩
  · rintro ⟨f, p, q, h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact Or.inr ⟨f, p, q, h1, h2, h3, h4, h5, h6, h8, h7⟩

theorem cl.bite : ¬ ∀ a b : ℝ, ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    a < q 0 ∧ q 0 < b := by
  intro h
  obtain ⟨f, p, q, -, -, -, -, -, -, h7, h8⟩ := h 0 0
  exact lt_asymm h7 h8
end RB2

open Claims in
run_cmd do
  let env ← getEnv
  let isRd := fun (c : Name) => (`RB2.SecondReading).isPrefixOf c
  let faults ← liftTermElabM <| paramClosureFaults env isRd `Checked.Hiemenz.hiemenz_exists `RB2.cl `RB2.SecondReading.rn
  logInfo m!"RESULT a2: {if faults.isEmpty then "ACCEPTED" else "REJECTED"} {faults.toList}"
