
/-! The rate of the turning values of the radial Gelfand branch (run 2026-11-25T0428Z): the same global regular
solution. -/

theorem gelfand_turning_ratio :
    nonvacuity% Checked.Math.GelfandTurningRatio.gelfand_turning_ratio := by
  obtain ⟨w, φ, hw, hφ0, hφ, h0⟩ := Checked.Math.BEGlobalExists.exists_global
  exact ⟨w, φ, hw, hφ0, hφ, h0, trivial⟩
