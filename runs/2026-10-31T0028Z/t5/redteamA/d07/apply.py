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
# Curvature density parameter (addendum to F6)

`Ω_k = −K c² / (a₀² H₀²)` (`c = 1`), so that the total density parameter `Ω₀ = 1 + K/(H₀² a₀²)` of
`Checked.Cosmography.BambaK.omega0` satisfies `Ω₀ = 1 − Ω_k`.
-/

namespace Checked.Cosmography.CurvatureDensity

open Checked.Cosmography Checked.Cosmography.BambaK

/-- Curvature density parameter `Ω_k = −K / (a₀² H₀²)` (`c = 1`). -/
noncomputable def omegaCurv (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : ℝ :=
  -K / (hubble a t₀ * a t₀ ^ 2)

/-- `Ω₀ = 1 − Ω_k`, checked on unit de Sitter (`a = exp`, `t₀ = 0`, `H₀ = a₀ = 1`) for every `K`. -/
theorem omega0_eq_one_sub_omegaCurv_deSitter (K : ℝ) :
    omega0 K Real.exp 0 = 1 - omegaCurv K Real.exp 0 := by
  have h : hubble Real.exp 0 = 1 := by simp [hubble, Real.deriv_exp]
  unfold omega0 omegaCurv
  rw [h]
  first
    | (simp; done)
    | (simp; ring)

end Checked.Cosmography.CurvatureDensity
'''
create("Checked/Cosmography/CurvatureDensity.lean", LEAN)
append("Checked.lean", "import Checked.Cosmography.CurvatureDensity\n")
sub("STATE.md", "- **Findings F1–F11** (FINDINGS.md)",
    "- **PROVED** (F6 addendum) `Checked.Cosmography.CurvatureDensity.omegaCurv` with `omega0_eq_one_sub_omegaCurv_deSitter`: the curvature density parameter Ω_k = −Kc²/(a₀²H₀²) and Ω₀ = 1 − Ω_k (the relation used by the review's Ω₀ = 1 + Kc²/(H₀²a₀²)): run 2026-10-31.\n- **Findings F1–F11** (FINDINGS.md)")
