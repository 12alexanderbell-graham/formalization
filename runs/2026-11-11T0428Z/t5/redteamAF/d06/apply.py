#!/usr/bin/env python3
"""Defect d06 (red team AF, run 2026-11-11T0428Z): a decorative hypothesis made NEEDED by repeating it in the conclusion.
Usage: python3 apply.py <repo_root> [--stage N]   (single commit; --stage accepted and ignored)"""
import sys
from pathlib import Path

args = [a for a in sys.argv[1:] if not a.startswith("--") and not a.isdigit()]
root = Path(args[0])

HEAD_PATH = "Checked/Toy/Term.lean"
WIT_PATH = "Checked/Trust/ToyD06.lean"

HEAD = r"""import Mathlib.Data.Real.Basic

/-! Order statements about real numbers. -/

namespace Checked.Toy

/-- The term holds when the condition holds. -/
theorem term_holds (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) : (a ≤ b ∨ c ≤ a) ∧ c ≤ d :=
  ⟨Or.inl h1, h2⟩

end Checked.Toy
"""

WIT = r"""import Checked.Trust.NonVacuity
import Checked.Toy.Term
import Mathlib.Tactic.NormNum

namespace Checked.Trust.ToyD06

theorem term_holds : nonvacuity% Checked.Toy.term_holds :=
  ⟨0, 0, 0, 0, le_rfl, le_rfl, trivial⟩

theorem term_holds_h1 : necessity% Checked.Toy.term_holds 1 := by
  refine ⟨1, 0, 2, 2, le_rfl, ?_⟩
  rintro ⟨h | h, -⟩ <;> norm_num at h

theorem term_holds_h2 : necessity% Checked.Toy.term_holds 2 := by
  refine ⟨0, 0, 1, 0, le_rfl, ?_⟩
  rintro ⟨-, h⟩
  norm_num at h

end Checked.Trust.ToyD06
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
append_line("Checked.lean", "import Checked.Toy.Term")
append_line("Checked.lean", "import Checked.Trust.ToyD06")
append_line("scripts/trust/headlines.txt", "Checked.Toy.term_holds")

print("applied d06")
