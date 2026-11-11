#!/usr/bin/env python3
"""Defect d05 (red team AF, run 2026-11-11T0428Z): a headline whose conclusion is a definition that hides a hypothesis is reported fully classified.
Usage: python3 apply.py <repo_root> [--stage N]   (single commit; --stage accepted and ignored)"""
import sys
from pathlib import Path

args = [a for a in sys.argv[1:] if not a.startswith("--") and not a.isdigit()]
root = Path(args[0])

HEAD_PATH = "Checked/Toy/Statement.lean"
WIT_PATH = "Checked/Trust/ToyD05.lean"

HEAD = r"""import Mathlib.Data.Real.Basic

/-! Order statements about real numbers. -/

namespace Checked.Toy

/-- A condition on values. -/
def Guarded (a b : ℝ) : Prop := b ≤ a → a = b

/-- The statement holds when the condition holds. -/
theorem statement_holds (a b : ℝ) (h : a ≤ b) : Guarded a b :=
  fun hb => le_antisymm h hb

end Checked.Toy
"""

WIT = r"""import Checked.Trust.NonVacuity
import Checked.Toy.Statement
import Mathlib.Tactic.NormNum

namespace Checked.Trust.ToyD05

theorem statement_holds : nonvacuity% Checked.Toy.statement_holds := by
  refine ⟨0, 0, le_rfl, ?_⟩
  first
    | exact trivial
    | exact ⟨le_rfl, trivial⟩

theorem statement_holds_h1 : necessity% Checked.Toy.statement_holds 1 := by
  refine ⟨1, 0, ?_⟩
  intro h
  have h' := h (by norm_num)
  norm_num at h'

end Checked.Trust.ToyD05
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
append_line("Checked.lean", "import Checked.Toy.Statement")
append_line("Checked.lean", "import Checked.Trust.ToyD05")
append_line("scripts/trust/headlines.txt", "Checked.Toy.statement_holds")
append_line("scripts/trust/def_kinds.txt", "Checked.Toy.Guarded CLAIM")
print("applied d05")
