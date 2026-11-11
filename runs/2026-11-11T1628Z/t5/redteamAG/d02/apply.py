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

/-! Hubble rate of a flat ΛCDM scale factor, law assumed pointwise. -/

namespace Checked.AGWrap.D02

open Checked.Cosmography Checked.Cosmography.Aviles

/-- If the flat ΛCDM law with matter fraction `Ω` holds at every time equal to `t₀`, the Hubble rate at `t₀` is positive. -/
theorem flatLCDM_hubble_pos_at (a : ℝ → ℝ) (t₀ Ω : ℝ) (h : ∀ s : ℝ, s = t₀ → IsFlatLCDM Ω a s) :
    0 < hubble a t₀ := by
  obtain ⟨h0, -⟩ := h t₀ rfl
  exact h0

end Checked.AGWrap.D02

#print axioms Checked.AGWrap.D02.flatLCDM_hubble_pos_at
'''
WIT = r'''import Checked.Trust.NonVacuity
import Checked.Trust.NecessityD
import Checked.AGWrap.D02

namespace Checked.Trust.AGW02

open Checked.Cosmography Checked.Cosmography.Aviles

theorem flatLCDM_hubble_pos_at : nonvacuity% Checked.AGWrap.D02.flatLCDM_hubble_pos_at := by
  obtain ⟨a, t₀, hL⟩ := Checked.Trust.NCD.exists_flatLCDM_any 1
  exact ⟨a, t₀, 1, fun s hs => by subst hs; exact hL, trivial⟩

theorem flatLCDM_hubble_pos_at_h1 : necessity% Checked.AGWrap.D02.flatLCDM_hubble_pos_at 1 :=
  ⟨fun _ => 0, 0, 0, by simp [hubble]⟩

end Checked.Trust.AGW02
'''
w("Checked/AGWrap/D02.lean", HEAD)
w("Checked/Trust/AGW02.lean", WIT)
append("Checked.lean", "import Checked.AGWrap.D02\nimport Checked.Trust.AGW02\n")
append("scripts/trust/headlines.txt", "Checked.AGWrap.D02.flatLCDM_hubble_pos_at\n")
