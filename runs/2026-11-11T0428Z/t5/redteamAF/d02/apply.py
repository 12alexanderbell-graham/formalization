#!/usr/bin/env python3
"""Defect d02 (red team AF, run 2026-11-11T0428Z): two disguised copies of one assumption, each shown redundant, both needed together.
Usage: python3 apply.py <repo_root> [--stage N]   (single commit; --stage accepted and ignored)"""
import sys
from pathlib import Path

args = [a for a in sys.argv[1:] if not a.startswith("--") and not a.isdigit()]
root = Path(args[0])

HEAD_PATH = "Checked/Toy/Order.lean"
WIT_PATH = "Checked/Trust/ToyD02.lean"

HEAD = r"""import Mathlib.Data.Real.Basic

/-! Order statements about real numbers. -/

namespace Checked.Toy

/-- The order holds when the condition holds. -/
theorem order_holds (a b c : ℝ) (h1 : a ≤ b) (h2 : ¬ b < a) : a ≤ b ∨ c ≤ a :=
  Or.inl ((show a ≤ b ∧ a ≤ b from ⟨h1, not_lt.1 h2⟩).1)

end Checked.Toy
"""

WIT = r"""import Checked.Trust.NonVacuity
import Checked.Toy.Order
import Mathlib.Tactic.NormNum

namespace Checked.Trust.ToyD02

theorem order_holds : nonvacuity% Checked.Toy.order_holds :=
  ⟨0, 0, 0, le_rfl, lt_irrefl _, trivial⟩

theorem order_holds_r1 : dropped% Checked.Toy.order_holds 1 :=
  fun _ _ _ h => Or.inl (not_lt.1 h)

theorem order_holds_r2 : dropped% Checked.Toy.order_holds 2 :=
  fun _ _ _ h => Or.inl h

end Checked.Trust.ToyD02
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
append_line("Checked.lean", "import Checked.Toy.Order")
append_line("Checked.lean", "import Checked.Trust.ToyD02")
append_line("scripts/trust/headlines.txt", "Checked.Toy.order_holds")

print("applied d02")
