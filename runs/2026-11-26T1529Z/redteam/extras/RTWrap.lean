import Mathlib

axiom a_deliberately_very_long_nonstandard_axiom_name_planted_by_the_red_team_to_force_wrapping : True

theorem rt_wrap : (∃ x : ℕ, x = 0) ∧ True := by
  have h := a_deliberately_very_long_nonstandard_axiom_name_planted_by_the_red_team_to_force_wrapping
  exact ⟨Classical.choice ⟨⟨0, rfl⟩⟩, h⟩

#print axioms rt_wrap
