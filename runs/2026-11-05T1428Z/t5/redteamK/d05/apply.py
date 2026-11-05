#!/usr/bin/env python3
"""d05: an existence statement (a flat LCDM scale factor with matter fraction 3/10 exists) under a
theorem name, module name and docstring that say it fits the Pantheon supernovae."""
import sys, pathlib

root = pathlib.Path(sys.argv[1])

FILES = {}

FILES["Checked/Cosmography/PantheonFlatLCDM.lean"] = r'''import Checked.Cosmography.LCDMWitness

/-!
# Flat ΛCDM and the Pantheon supernova sample

The Pantheon sample of type Ia supernovae is described by a spatially flat ΛCDM model with a
matter fraction of about three tenths. This module records the corresponding model in the
framework of the repository: a smooth flat ΛCDM scale factor with that matter fraction.
-/

namespace Checked.Cosmography.PantheonFlatLCDM

/-- There is a flat ΛCDM scale factor with matter fraction 3/10, the value that fits the Pantheon
supernovae, six times continuously differentiable at its observation time. -/
theorem flatLCDM_fits_pantheon_SN :
    ∃ (a : ℝ → ℝ) (t₀ : ℝ),
      Checked.Cosmography.Aviles.IsFlatLCDM (3 / 10) a t₀ ∧ ContDiffAt ℝ 6 a t₀ :=
  Checked.Cosmography.AvilesWitness.exists_flatLCDM (Ω := 3 / 10) (by norm_num) (by norm_num)

end Checked.Cosmography.PantheonFlatLCDM
'''

for rel, text in FILES.items():
    p = root / rel
    assert not p.exists(), rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")


def append(rel, text):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text, encoding="utf-8")


append("Checked.lean", "import Checked.Cosmography.PantheonFlatLCDM\n")
append("scripts/trust/headlines.txt", "# Flat LCDM models\nChecked.Cosmography.PantheonFlatLCDM.flatLCDM_fits_pantheon_SN\n")
print("d05 applied")
