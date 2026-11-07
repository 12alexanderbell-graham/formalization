#!/usr/bin/env python3
"""d01: new headline Checked.Math.PowDecay.pow_lt_eventually (pointwise decay of x^n), paraphrase with the
existential moved in front of the universal over x (uniform N), in an order V7 accepts. usage: apply.py <repo_root>"""
import sys
from pathlib import Path

root = Path(sys.argv[1])


def append(rel, text):
    p = root / rel
    old = p.read_text(encoding="utf-8")
    if not old.endswith("\n"):
        old += "\n"
    p.write_text(old + text, encoding="utf-8")


LEAN = '''import Mathlib.Analysis.SpecificLimits.Basic
import Checked.Trust.NonVacuity

/-! Powers of a real number of absolute value below one: for each such number the powers fall below
any given positive bound from some index on. -/

namespace Checked.Math.PowDecay

/-- For every ε above zero there is a number N such that, for every x strictly between -1 and 1 and
every n above N, `|x ^ n| < ε`. -/
theorem pow_lt_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ x : ℝ, |x| < 1 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |x ^ n| < ε := by
  intro x hx
  have ht : Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (nhds 0) := by
    first
      | exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one hx
      | exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by simpa using hx)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [Real.dist_eq, sub_zero] at h
  exact h

theorem nv_pow_lt_eventually : nonvacuity% Checked.Math.PowDecay.pow_lt_eventually :=
  ⟨1, by norm_num, 0, by norm_num, trivial⟩

end Checked.Math.PowDecay
'''

new = root / "Checked/Math/PowDecay.lean"
assert not new.exists()
new.write_text(LEAN, encoding="utf-8")
append("Checked.lean", "import Checked.Math.PowDecay\n")
append("scripts/trust/headlines.txt",
       "# Powers of a number of absolute value below one (run 2026-11-07T0228Z)\nChecked.Math.PowDecay.pow_lt_eventually\n")
append("LEDGER.md",
       "\n## Run 2026-11-07T0228Z (author, part 5)\n"
       "- New headline `pow_lt_eventually` (module `Checked.Math.PowDecay`, headlines.txt): for every ε > 0 and every x with |x| < 1 "
       "there is N with |xⁿ| < ε for all n ≥ N; only Mathlib definitions in the statement; NV witness `nv_pow_lt_eventually` in the same module. "
       "No frozen constant, pin, phrase or registry line changed.\n")
print("d01 applied")
