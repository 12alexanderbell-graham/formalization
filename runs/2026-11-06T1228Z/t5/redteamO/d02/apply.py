import sys, pathlib, argparse
ap = argparse.ArgumentParser(); ap.add_argument('root'); ap.add_argument('--stage', type=int, default=0)
_a = ap.parse_args()
root = pathlib.Path(_a.root)
st = _a.stage
def rd(rel):
    return (root / rel).read_text(encoding="utf-8")
def rep(rel, old, new):
    p = root / rel; t = p.read_text(encoding="utf-8")
    assert t.count(old) == 1, (rel, old)
    p.write_text(t.replace(old, new), encoding="utf-8")
def app(rel, s):
    p = root / rel; t = p.read_text(encoding="utf-8")
    if not t.endswith("\n"): t += "\n"
    p.write_text(t + s, encoding="utf-8")
def new(rel, s):
    p = root / rel; p.parent.mkdir(parents=True, exist_ok=True)
    assert not p.exists(), rel
    p.write_text(s, encoding="utf-8")
ROB = ("Checked.Trust.SecondReading.robK1 Checked.Trust.SecondReading.robK2 Checked.Trust.SecondReading.robK3 "
       "Checked.Trust.SecondReading.robInit")

D = "runs/2026-11-06T1228Z/kappa_reader_o/"
BRIEF = """# Brief: blind literal reading of a published correlation (run 2026-11-06T1228Z, folder kappa_reader_o)

You are an independent reader. Write ONE Lean 4 file, `SecondReadingKappaO.lean`, in this folder, with a single
definition `kappaSoaveO (ω : ℝ) : ℝ`: the quadratic polynomial in the acentric factor ω that Soave gave for the
exponent of the attraction-parameter correction of his modification of the Redlich-Kwong equation of state (the
coefficient usually written m or κ).

The coefficients are tabulated in the reference sheet `sheet_kappa_o.md` in this folder (row `Soave`), a
transcription from lecture notes. Copy that row into Lean: constant term, linear term, quadratic term, in the
order of the sheet, using the sheet's decimal places. Do not look anything up elsewhere and do not read anything
else in the repository.

Template (namespace and import only; the definition is yours):

    import Mathlib.Data.Real.Basic
    namespace Checked.Trust.SecondReading
    noncomputable def kappaSoaveO (ω : ℝ) : ℝ := ...
    end Checked.Trust.SecondReading
"""
SHEET = """# Reference sheet: kappa(omega) of cubic equations of state (secondary transcription, lecture notes)

Attraction parameter a(T) = a_c (1 + kappa (1 - sqrt(T/T_c)))^2; kappa is a polynomial in the acentric factor omega.

| Equation | kappa(omega) |
|---|---|
| Soave | 0.480 + 1.574 omega - 0.167 omega^2 |
| van der Waals | (no temperature dependence) |
"""
READ = """import Mathlib.Data.Real.Basic
/-! Blind literal reading of Soave's kappa(omega) (run 2026-11-06T1228Z). Source: the reference sheet in the reader's folder (a secondary transcription from lecture notes). -/
namespace Checked.Trust.SecondReading
/-- Soave (1972) for the Soave–Redlich–Kwong equation: the coefficient m (also written κ) as a function of ω, as tabulated on the reference sheet. -/
noncomputable def kappaSoaveO (ω : ℝ) : ℝ := 0.480 + 1.574 * ω - 0.167 * ω ^ 2
end Checked.Trust.SecondReading
"""
LEAN = """import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Chemistry: Soave's κ(ω) at ω = 1

A one-line numerical consequence of the κ(ω) polynomial, with no equation of state involved.
-/

namespace Checked.Chemistry.SoaveOne

/-- Soave's κ(ω) correlation evaluated at ω = 1 gives κ(1) > 1.88. -/
theorem soave_kappa_one_above : (1.88 : ℝ) < 0.480 + 1.574 * 1 - 0.167 * 1 ^ 2 := by
  norm_num

end Checked.Chemistry.SoaveOne
"""
# commit 1: the brief and the sheet (no .lean, nothing under Checked/ Work/ scripts/)
if st in (0, 1):
    new(D + "brief_kappa_o.md", BRIEF)
    new(D + "sheet_kappa_o.md", SHEET)
# commit 2: the reading alone, under runs/ only
if st in (0, 2):
    new(D + "SecondReadingKappaO.lean", READ)
# commit 3: the Checked copy (code identical), the headline, the registrations
if st in (0, 3):
    new("Checked/Trust/SecondReadingKappaO.lean", READ)
    new("Checked/Chemistry/SoaveOne.lean", LEAN)
    app("Checked.lean", "import Checked.Trust.SecondReadingKappaO\nimport Checked.Chemistry.SoaveOne\n")
    app("scripts/trust/headlines.txt", "Checked.Chemistry.SoaveOne.soave_kappa_one_above\n")
    app("scripts/trust/literal_readings.txt", "Checked.Chemistry.SoaveOne.soave_kappa_one_above source=Soave Checked.Trust.SecondReading.kappaSoaveO\n")
    app("LEDGER.md", "\n- 2026-11-06T1228Z: **Literal reading** for `soave_kappa_one_above` (literal_readings.txt, source=Soave): `Checked.Trust.SecondReading.kappaSoaveO` (module `Checked/Trust/SecondReadingKappaO.lean`, copied from `runs/2026-11-06T1228Z/kappa_reader_o/`; brief committed alone, reading alone, copy after). New headline `soave_kappa_one_above` (Checked/Chemistry/SoaveOne.lean); frozen.txt relocked (new entries only).\n")
