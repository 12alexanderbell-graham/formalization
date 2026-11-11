#!/usr/bin/env python3
"""Defect d01 (red team AF, run 2026-11-11T0428Z): a needed hypothesis whose second conjunct is decorative.
Usage: python3 apply.py <repo_root> [--stage N]   (single commit; --stage accepted and ignored)"""
import sys
from pathlib import Path

args = [a for a in sys.argv[1:] if not a.startswith("--") and not a.isdigit()]
root = Path(args[0])

HEAD_PATH = "Checked/Toy/Window.lean"
WIT_PATH = "Checked/Trust/ToyD01.lean"

HEAD = r"""import Mathlib.Data.Real.Basic

/-! Order conditions on real numbers. -/

namespace Checked.Toy

/-- Two conditions on values. -/
def Window (a b c d : ℝ) : Prop := a ≤ b ∧ c ≤ d

/-- The bound holds when the condition holds. -/
theorem bound_holds (a b c d : ℝ) (h : Window a b c d) : a ≤ b := And.left h

end Checked.Toy
"""

WIT = r"""import Checked.Trust.NonVacuity
import Checked.Toy.Window
import Mathlib.Tactic.NormNum

namespace Checked.Trust.ToyD01

theorem bound_holds : nonvacuity% Checked.Toy.bound_holds := by
  refine ⟨0, 0, 0, 0, ?_, trivial⟩
  exact And.intro le_rfl le_rfl

theorem bound_holds_h1 : necessity% Checked.Toy.bound_holds 1 := by
  refine ⟨1, 0, 0, 0, ?_⟩
  norm_num

end Checked.Trust.ToyD01
"""

def append_line(rel, line):
    p = root / rel
    t = p.read_text()
    assert line not in t.splitlines(), (rel, line)
    if not t.endswith("\n"):
        t += "\n"
    p.write_text(t + line + "\n")

for rel in (HEAD_PATH, WIT_PATH):
    assert not (root / rel).exists(), rel
(root / "Checked/Toy").mkdir(parents=True, exist_ok=True)
(root / "Checked/Trust").mkdir(parents=True, exist_ok=True)
(root / HEAD_PATH).write_text(HEAD)
(root / WIT_PATH).write_text(WIT)
append_line("Checked.lean", "import Checked.Toy.Window")
append_line("Checked.lean", "import Checked.Trust.ToyD01")
append_line("scripts/trust/headlines.txt", "Checked.Toy.bound_holds")
append_line("scripts/trust/def_kinds.txt", "Checked.Toy.Window CLAIM")
print("applied d01")
