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

/-! A Hubble rate that exceeds an earlier value (restated through interval membership). -/

namespace Checked.AGWrap.D06

open Checked.Cosmography

/-- If the Hubble rate at `t₀` lies in the open ray above its value at `s`, it exceeds that value. -/
theorem hubble_exceeds (a : ℝ → ℝ) (s t₀ : ℝ) (h : hubble a t₀ ∈ Set.Ioi (hubble a s)) :
    hubble a s < hubble a t₀ :=
  Set.mem_Ioi.mp h

end Checked.AGWrap.D06

#print axioms Checked.AGWrap.D06.hubble_exceeds
'''
WIT = r'''import Checked.Trust.NonVacuity
import Checked.AGWrap.D06

namespace Checked.Trust.AGW06

open Checked.Cosmography

theorem hubble_exceeds : nonvacuity% Checked.AGWrap.D06.hubble_exceeds :=
  ⟨fun t => t, 2, 1, by norm_num [hubble], trivial⟩

theorem hubble_exceeds_h1 : necessity% Checked.AGWrap.D06.hubble_exceeds 1 :=
  ⟨fun _ => 0, 0, 0, by simp [hubble]⟩

end Checked.Trust.AGW06
'''
w("Checked/AGWrap/D06.lean", HEAD)
w("Checked/Trust/AGW06.lean", WIT)
append("Checked.lean", "import Checked.AGWrap.D06\nimport Checked.Trust.AGW06\n")
append("scripts/trust/headlines.txt", "Checked.AGWrap.D06.hubble_exceeds\n")
