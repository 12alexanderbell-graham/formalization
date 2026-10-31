import sys, pathlib
root = pathlib.Path(sys.argv[1])
def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old, s.count(old))
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

`d_A` obtained from the Checked luminosity distance `lumDist` by the Etherington relation
(`c = 1`, every curvature `K`, every scale factor): `d_A = d_L / (1 + z)`.
-/

namespace Checked.Cosmography.Etherington

open Checked.Cosmography Checked.Cosmography.BambaK

/-- Angular-diameter distance from the luminosity distance by the Etherington reciprocity
relation, `d_A = d_L / (1 + z)`. -/
noncomputable def angDistEth (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  lumDist K a t₀ t / (1 + redshift a t₀ t)

/-- **Etherington reciprocity** for the Checked distances: `d_L = (1 + z) d_A`, unconditionally
(at `1 + z = 0` both sides vanish). -/
theorem lumDist_eq_mul_angDistEth (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) :
    lumDist K a t₀ t = (1 + redshift a t₀ t) * angDistEth K a t₀ t := by
  unfold angDistEth
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

end Checked.Cosmography.Etherington
'''
create("Checked/Cosmography/Etherington.lean", LEAN)
append("Checked.lean", "import Checked.Cosmography.Etherington\n")
# registered as a headline (statement is unconditional: plain-data binders only)
append("scripts/trust/headlines.txt", "# F6/F7 addendum\nEtherington.lumDist_eq_mul_angDistEth\n")
# classified as an explicit algebraic expression
append("scripts/trust/def_kinds.txt", "Checked.Cosmography.Etherington.angDistEth FORMULA\n")
sub("STATE.md", "- **Findings F1–F11** (FINDINGS.md)",
    "- **PROVED** (F6/F7 addendum) `Checked.Cosmography.Etherington.lumDist_eq_mul_angDistEth` (Etherington reciprocity for the Checked distances, every real K, any scale factor: d_A = d_L/(1+z), d_L = (1+z) d_A): run 2026-10-31.\n- **Findings F1–F11** (FINDINGS.md)")
