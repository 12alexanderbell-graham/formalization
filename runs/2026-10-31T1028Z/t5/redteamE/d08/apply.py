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


LEAN = '''import Checked.Chemistry.CubicEOS
import Checked.Trust.NonVacuity

/-!
# Critical compressibility factor of the Peng–Robinson equation of state (addendum)

The generalized family `P = R T/(v − b) − a/(v² + u b v + w b²)` and the critical-point
characterization of `Checked.Chemistry.CubicEOS`.
-/

namespace Checked.Chemistry.CubicEOS

/-- **Peng–Robinson.** At every critical point of the Peng–Robinson isotherm the critical
compressibility factor is exactly `Z_c = P v/(R T) = 1/3`, as for Redlich–Kwong, for every
temperature function `a(T)`. -/
theorem pr_critical_compressibility (R a b T v : ℝ) (ha : 0 < a) (hb : 0 < b) (hv : b < v)
    (hc : IsCriticalIsotherm (cubicP R a b 1 0 T) v) :
    cubicP R a b 1 0 T v * v / (R * T) = 1 / 3 :=
  (rk_constants R a b T v ha hb hv hc).1

end Checked.Chemistry.CubicEOS

namespace Checked.Trust.NV

theorem pr_critical_compressibility :
    nonvacuity% Checked.Chemistry.CubicEOS.pr_critical_compressibility := by
  obtain ⟨⟨T, v⟩, ⟨_, hv, hc⟩, -⟩ := Checked.Chemistry.CubicEOS.exists_unique_critical 1 1 1 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨1, 1, 1, T, v, by norm_num, by norm_num, hv, hc, trivial⟩

end Checked.Trust.NV
'''
create("Checked/Chemistry/CubicEOSPR.lean", LEAN)
append("Checked.lean", "import Checked.Chemistry.CubicEOSPR\n")
# registered at the end of the Chemistry block
append("scripts/trust/headlines.txt", "Checked.Chemistry.CubicEOS.pr_critical_compressibility\n")
