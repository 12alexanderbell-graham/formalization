import Mathlib

axiom zz_deliberately_very_long_nonstandard_axiom_name_planted_by_the_red_team_to_land_on_line_two : True

theorem rt_wrap_late : (∃ x : ℕ, x = 0) ∧ True := by
  have h := zz_deliberately_very_long_nonstandard_axiom_name_planted_by_the_red_team_to_land_on_line_two
  have hp : (1:ℕ) = 1 ↔ True := propext ⟨fun _ => trivial, fun _ => rfl⟩ ▸ Iff.rfl
  exact ⟨Classical.choice ⟨⟨0, rfl⟩⟩, h⟩

#print axioms rt_wrap_late
