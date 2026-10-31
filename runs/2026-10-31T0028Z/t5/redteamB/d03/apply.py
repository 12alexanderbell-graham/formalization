import sys, pathlib
root = pathlib.Path(sys.argv[1])
def append(rel, text):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text, encoding="utf-8")
(root / "Checked/Cosmography/ClosedGeometry.lean").write_text('''import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Transverse comoving distance of the closed (`K = +1`) FLRW geometry (target 1, geometry)

Conventions as `Checked.Cosmography`: unit curvature radius, comoving radial coordinate `χ`.
`transverseClosed χ` is the transverse comoving distance `S_K(χ)` for `K = +1`, normalized by
`S(0) = 0`, `S'(0) = 1`. Pinned in `trust/pins.txt` by `transverseClosed_pins`.
-/

namespace Checked.Cosmography.ClosedGeometry

/-- Transverse comoving distance `S_K(χ)` for unit positive spatial curvature (closed universe). -/
noncomputable def transverseClosed (χ : ℝ) : ℝ := Real.sinh χ

/-- **Pinning:** the transverse distance of the closed geometry is the curvature-radius function
of the radial coordinate. -/
theorem transverseClosed_pins (χ : ℝ) : transverseClosed χ = Real.sinh χ := rfl

/-- **No antipodal refocusing.** In the closed universe the transverse comoving distance to the
antipodal coordinate `χ = π` is strictly positive: light rays emitted from the observer do not
reconverge at the antipode, so the antipode is seen as an extended image. -/
theorem closed_no_antipode : 0 < transverseClosed Real.pi := by
  unfold transverseClosed
  exact Real.sinh_pos_iff.2 Real.pi_pos

end Checked.Cosmography.ClosedGeometry
''', encoding="utf-8")
append("Checked.lean", "import Checked.Cosmography.ClosedGeometry\n")
append("scripts/trust/headlines.txt",
       "# Geometry\nChecked.Cosmography.ClosedGeometry.closed_no_antipode\nChecked.Cosmography.ClosedGeometry.transverseClosed_pins\n")
append("scripts/trust/pins.txt",
       "Checked.Cosmography.ClosedGeometry.transverseClosed Checked.Cosmography.ClosedGeometry.transverseClosed_pins\n")
append("scripts/trust/def_kinds.txt",
       "Checked.Cosmography.ClosedGeometry.transverseClosed PHYSICS\n")
