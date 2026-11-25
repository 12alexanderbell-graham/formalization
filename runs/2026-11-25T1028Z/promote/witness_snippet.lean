/-! The growth of consecutive turning radii of the radial Gelfand branch (run 2026-11-25T1028Z): the same global
regular solution. -/

theorem gelfand_turning_radii :
    nonvacuity% Checked.Math.GelfandTurningRadii.gelfand_turning_radii := by
  obtain ⟨w, φ, hw, hφ0, hφ, h0⟩ := Checked.Math.BEGlobalExists.exists_global
  exact ⟨w, φ, hw, hφ0, hφ, h0, trivial⟩
