#!/usr/bin/env python3
"""Defect d03 (red team AF, run 2026-11-11T0428Z): a hypothesis after a `let` is invisible to the necessity classification.
Usage: python3 apply.py <repo_root> [--stage N]   (single commit; --stage accepted and ignored)"""
import sys
from pathlib import Path

args = [a for a in sys.argv[1:] if not a.startswith("--") and not a.isdigit()]
root = Path(args[0])

HEAD_PATH = "Checked/Toy/Case.lean"
WIT_PATH = "Checked/Trust/ToyD03.lean"

HEAD = r"""import Mathlib.Data.Real.Basic

/-! Order statements about real numbers. -/

namespace Checked.Toy

/-- The case holds when the condition holds. -/
theorem case_holds (a b : ℝ) (h : a ≤ b) : let c := b; c ≤ c → a ≤ c := by
  intro c hc
  exact le_trans h hc

end Checked.Toy
"""

WIT = r"""import Checked.Trust.NonVacuity
import Checked.Toy.Case
import Mathlib.Tactic.NormNum

namespace Checked.Trust.ToyD03

theorem case_holds : nonvacuity% Checked.Toy.case_holds := by
  refine ⟨0, 0, le_rfl, ?_⟩
  first
    | exact trivial
    | exact ⟨le_rfl, trivial⟩

theorem case_holds_h1 : necessity% Checked.Toy.case_holds 1 := by
  refine ⟨1, 0, ?_⟩
  intro h
  exact absurd (h le_rfl) (by norm_num)

end Checked.Trust.ToyD03
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
append_line("Checked.lean", "import Checked.Toy.Case")
append_line("Checked.lean", "import Checked.Trust.ToyD03")
append_line("scripts/trust/headlines.txt", "Checked.Toy.case_holds")

print("applied d03")
