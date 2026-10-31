import sys, pathlib

root = pathlib.Path(sys.argv[1])


def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old[:60], s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")


def append(rel, text):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text, encoding="utf-8")


def create(rel, text):
    p = root / rel
    assert not p.exists(), rel
    p.write_text(text, encoding="utf-8")


LEAN = '''import Checked.Records.Findings

/-!
# The printed `m₀` of Aviles et al. Eq. (15) against the true `m₀` of flat ΛCDM (addendum to F1)
-/

namespace Checked.Cosmography.Aviles

open Checked.Records

/-- The printed `m₀` of Eq. (15) of Aviles et al. agrees with the true `m₀` of flat ΛCDM models
with matter fraction `Ω ∈ (0, 1)`: it equals `1 − 27Ω²/2 − 81Ω² − 81Ω³/2` for every scale factor
obeying the model that is `C⁶` at `t₀`. -/
theorem printedM0_agrees_somewhere :
    Set.Nonempty {r : ℝ | 0 < r ∧ r < 1 ∧ ∀ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM r a t₀ →
      ContDiffAt ℝ 6 a t₀ →
      cosmoCoeff 6 a t₀ = 1 - 27 / 2 * r ^ 2 - 81 * r ^ 2 - 81 / 2 * r ^ 3} := by
  obtain ⟨r, -, h0, h1, h⟩ := F1_m0_agrees
  refine ⟨r, ?_⟩
  show 0 < r ∧ r < 1 ∧ _
  exact ⟨h0, h1, h⟩

end Checked.Cosmography.Aviles
'''
create("Checked/Cosmography/M0Agreement.lean", LEAN)
append("Checked.lean", "import Checked.Cosmography.M0Agreement\n")
# registered in the F1 block; the statement has no binders, so it is unconditional (no witness)
sub("scripts/trust/headlines.txt", "AvilesWitness.printedM0_false_at\n",
    "AvilesWitness.printedM0_false_at\nAviles.printedM0_agrees_somewhere\n")
