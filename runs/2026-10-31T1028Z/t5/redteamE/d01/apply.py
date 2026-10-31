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


LEAN = '''import Checked.Cosmography.BambaCurved

/-!
# Etherington reciprocity between the Checked distances (small addendum to F6/F7)

The distance inferred from the apparent angular size of a standard rod, obtained from the
Checked luminosity distance `lumDist` by the Etherington reciprocity relation
(`c = 1`, every curvature `K`, every scale factor).
-/

namespace Checked.Cosmography.EtheringtonSize

open Checked.Cosmography Checked.Cosmography.BambaK

/-- Angular-size distance obtained from the luminosity distance `d_L` of `lumDist` by the
Etherington reciprocity relation, `d_ang = d_L / (1 + z)`. -/
noncomputable def angularSizeDistEth (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  lumDist K a t₀ t / (1 + redshift a t₀ t)

/-- **Etherington reciprocity** for the Checked distances: `d_L = (1 + z) d_ang`, for every
curvature `K` and every scale factor (at `1 + z = 0` both sides vanish). -/
theorem lumDist_eq_mul_angularSizeDistEth (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) :
    lumDist K a t₀ t = (1 + redshift a t₀ t) * angularSizeDistEth K a t₀ t := by
  unfold angularSizeDistEth
  by_cases h : 1 + redshift a t₀ t = 0
  · have h0 : lumDist K a t₀ t = 0 := by
      unfold lumDist
      rw [h]
      simp
    first
      | (simp [h0, h]; done)
      | (rw [h0, h]; simp)
  · first
      | (field_simp; done)
      | (field_simp; ring)
      | exact (mul_div_cancel₀ _ h).symm
      | simp [h]

end Checked.Cosmography.EtheringtonSize
'''
create("Checked/Cosmography/EtheringtonSize.lean", LEAN)
append("Checked.lean", "import Checked.Cosmography.EtheringtonSize\n")
# registered as a headline in the F7 block (unconditional: plain-data binders only)
sub("scripts/trust/headlines.txt", "BambaA.milne_printedDA4_fails_past\n",
    "BambaA.milne_printedDA4_fails_past\nEtheringtonSize.lumDist_eq_mul_angularSizeDistEth\n")
# classified as an explicit algebraic expression
append("scripts/trust/def_kinds.txt", "Checked.Cosmography.EtheringtonSize.angularSizeDistEth FORMULA\n")
