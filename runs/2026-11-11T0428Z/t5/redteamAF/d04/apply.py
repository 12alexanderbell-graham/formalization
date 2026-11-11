#!/usr/bin/env python3
"""Defect d04 (red team AF, run 2026-11-11T0428Z): an assumption carried by a subtype binder is outside the numbered hypotheses.
Usage: python3 apply.py <repo_root> [--stage N]   (single commit; --stage accepted and ignored)"""
import sys
from pathlib import Path

args = [a for a in sys.argv[1:] if not a.startswith("--") and not a.isdigit()]
root = Path(args[0])

HEAD_PATH = "Checked/Toy/Side.lean"
WIT_PATH = "Checked/Trust/ToyD04.lean"

HEAD = r"""import Mathlib.Data.Real.Basic

/-! Order statements about real numbers. -/

namespace Checked.Toy

/-- The side holds when the condition holds. -/
theorem side_holds (a c : ℝ) (b : {x : ℝ // a ≤ x}) (h : c ≤ a) : c ≤ b.1 :=
  le_trans h b.2

end Checked.Toy
"""

WIT = r"""import Checked.Trust.NonVacuity
import Checked.Toy.Side
import Mathlib.Tactic.NormNum

namespace Checked.Trust.ToyD04

theorem side_holds : nonvacuity% Checked.Toy.side_holds :=
  ⟨0, 0, ⟨0, le_rfl⟩, le_rfl, trivial⟩

theorem side_holds_h1 : necessity% Checked.Toy.side_holds 1 := by
  refine ⟨0, 1, ⟨0, le_rfl⟩, ?_⟩
  show ¬ (1 : ℝ) ≤ 0
  norm_num

end Checked.Trust.ToyD04
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
append_line("Checked.lean", "import Checked.Toy.Side")
append_line("Checked.lean", "import Checked.Trust.ToyD04")
append_line("scripts/trust/headlines.txt", "Checked.Toy.side_holds")

print("applied d04")
