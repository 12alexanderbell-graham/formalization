import sys, os
root = sys.argv[1]
def w(rel, text):
    p = os.path.join(root, rel)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    assert not os.path.exists(p), rel
    open(p, "w").write(text)
def append(rel, text):
    p = os.path.join(root, rel)
    s = open(p).read()
    if not s.endswith("\n"): s += "\n"
    open(p, "w").write(s + text)

HEAD = r'''import Checked.Cosmography.LCDMCoefficients

/-! Hubble rate of a flat ΛCDM scale factor (wrapper of the law hypothesis of `Aviles.flatLCDM_coeffs`). -/

namespace Checked.AGWrap.D01

open Checked.Cosmography Checked.Cosmography.Aviles

/-- If the scale factor obeys the flat ΛCDM law for some matter fraction `Ω` at `t₀`, its Hubble rate at `t₀` is positive. -/
theorem flatLCDM_hubble_pos (a : ℝ → ℝ) (t₀ : ℝ) (h : ∃ Ω : ℝ, IsFlatLCDM Ω a t₀) :
    0 < hubble a t₀ := by
  obtain ⟨Ω, h0, -⟩ := h
  exact h0

end Checked.AGWrap.D01

#print axioms Checked.AGWrap.D01.flatLCDM_hubble_pos
'''
WIT = r'''import Checked.Trust.NonVacuity
import Checked.Trust.NecessityD
import Checked.AGWrap.D01

namespace Checked.Trust.AGW01

open Checked.Cosmography Checked.Cosmography.Aviles

theorem flatLCDM_hubble_pos : nonvacuity% Checked.AGWrap.D01.flatLCDM_hubble_pos := by
  obtain ⟨a, t₀, hL⟩ := Checked.Trust.NCD.exists_flatLCDM_any 1
  exact ⟨a, t₀, ⟨1, hL⟩, trivial⟩

theorem flatLCDM_hubble_pos_h1 : necessity% Checked.AGWrap.D01.flatLCDM_hubble_pos 1 :=
  ⟨fun _ => 0, 0, by simp [hubble]⟩

end Checked.Trust.AGW01
'''
w("Checked/AGWrap/D01.lean", HEAD)
w("Checked/Trust/AGW01.lean", WIT)
append("Checked.lean", "import Checked.AGWrap.D01\nimport Checked.Trust.AGW01\n")
append("scripts/trust/headlines.txt", "Checked.AGWrap.D01.flatLCDM_hubble_pos\n")
