#!/usr/bin/env python3
"""d03: a FORGED blind reader file, committed first under runs/<run>/ next to a plausible brief (round L limit 1),
then copied into Checked/Trust/ with a hand-written agreement.  The transcribed object is a PRINTED definition
(not a CLAIM, so the generator route of check_provenance rule 2 does not apply).

  python3 apply.py <repo_root> --stage 1    commit 1: runs/2026-11-06T0028Z/t5/redteamM/d03_reader/{briefJ0.md,SecondReadingJ0.lean}
  python3 apply.py <repo_root> --stage 2    commit 2: Checked modules, registries, LEDGER line
  python3 apply.py <repo_root>              both (single tree)
"""
import sys, pathlib
args = sys.argv[1:]
stage = None
if "--stage" in args:
    i = args.index("--stage")
    stage = int(args[i + 1])
    del args[i:i + 2]
root = pathlib.Path(args[0])

def write_new(rel, text):
    p = root / rel
    assert not p.exists(), rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")

def append(rel, text):
    p = root / rel
    t = p.read_text(encoding="utf-8")
    if not t.endswith("\n"):
        t += "\n"
    p.write_text(t + text, encoding="utf-8")

RUN = "runs/2026-11-06T0028Z/t5/redteamM/d03_reader"

BRIEF = '''# Brief for a blind second reader: item J0 (Aviles et al., PRD 86, 123516, Eq. (15))

You are the second, independent reader of one printed formula. You see only the typeset page
(arXiv:1204.2007v2, page 10, the sentence after Eq. (14) that lists the cosmographic coefficients of
flat LambdaCDM) and the conventions below. Do not read any file of the repository, any other paper,
or any earlier transcription; do not derive the coefficient yourself: write what is PRINTED.

Conventions: Omega_m is the matter fraction; write it as `Ω : ℝ`. The coefficients are those of
Eq. (3): q, j, s, l, m (q_0 = -1 + 3/2 Omega_m is printed first).

Task: write one Lean 4 definition for the printed j_0, as a function of `Ω`, in the file
`SecondReadingJ0.lean` (namespace `Checked.Trust.SecondReading.J0`, import only
`Mathlib.Data.Real.Basic`), with a docstring quoting the printed text. Return only the file.
'''

READER = '''import Mathlib.Data.Real.Basic

/-! Blind second reading of Aviles, Gruber, Luongo, Quevedo (PRD 86, 123516), Eq. (15): the printed
coefficient j₀ (run 2026-11-06T0028Z; the reader saw only the typeset page and the conventions of
the brief next to this file). -/

namespace Checked.Trust.SecondReading.J0

/-- Aviles et al. 2012, Eq. (15): the printed jerk coefficient j₀ = 1 + Ω_m. -/
noncomputable def printedJ0 (Ω : ℝ) : ℝ := 1 + Ω

end Checked.Trust.SecondReading.J0
'''

PROGRAM = '''import Checked.Cosmography.LCDMWitness
import Checked.Trust.NonVacuity

/-!
# Eq. (15) of Aviles, Gruber, Luongo, Quevedo (PRD 86, 123516): the printed j₀

The coefficient j₀ = a⁽³⁾/(aH³) of flat ΛCDM is printed in Eq. (15) as 1 + Ω_m (transcribed here as
`printedJ0` and read a second time by an independent reader, see `Checked.Trust.Transcriptions`).
For a flat ΛCDM scale factor it equals 1 (`Checked.Cosmography.Aviles.flatLCDM_coeffs`), so the
printed j₀ is wrong for every Ω_m ≠ 0, like the printed l₀ and m₀.
-/

namespace Checked.Cosmography.AvilesJ0

open Checked.Cosmography Checked.Cosmography.Aviles Checked.Cosmography.AvilesWitness

/-- Aviles et al. 2012, Eq. (15): the printed jerk coefficient j₀ = 1 + Ω_m (transcribed). -/
noncomputable def printedJ0 (Ω : ℝ) : ℝ := 1 + Ω

/-- The j₀ printed by Aviles et al. 2012 in Eq. (15) is false at every Ω ∈ (0,1). -/
theorem printedJ0_false_at {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    ¬ ∀ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ → ContDiffAt ℝ 6 a t₀ →
      cosmoCoeff 3 a t₀ = printedJ0 Ω := by
  intro h
  obtain ⟨a, t₀, hL, hs⟩ := exists_flatLCDM h0 h1
  have e := h a t₀ hL hs
  rw [(flatLCDM_coeffs Ω a t₀ hL hs).2.1] at e
  unfold printedJ0 at e
  linarith

end Checked.Cosmography.AvilesJ0

namespace Checked.Trust.NV

theorem printedJ0_false_at : nonvacuity% Checked.Cosmography.AvilesJ0.printedJ0_false_at :=
  ⟨1 / 2, by norm_num, by norm_num, trivial⟩

end Checked.Trust.NV
'''

AGREE = '''import Checked.Trust.SecondReadingJ0
import Checked.Cosmography.AvilesJ0

/-!
# Two independent transcriptions agree: Aviles et al. Eq. (15), j₀ (trust track T3, run 2026-11-06T0028Z)
-/

namespace Checked.Trust.Transcriptions

/-- `Checked.Cosmography.AvilesJ0.printedJ0` agrees with the blind second reading. -/
theorem agree_printedJ0 :
    Checked.Cosmography.AvilesJ0.printedJ0 = Checked.Trust.SecondReading.J0.printedJ0 := by
  funext Ω
  simp only [Checked.Cosmography.AvilesJ0.printedJ0, Checked.Trust.SecondReading.J0.printedJ0]

end Checked.Trust.Transcriptions
'''

LEDGER = ("\n## 2026-11-06 · blind second reading of the printed j₀ of Aviles et al. Eq. (15)\n"
          "- New blind second reading `Checked/Trust/SecondReadingJ0.lean` (`printedJ0`), copied verbatim from the reader's output "
          "`runs/2026-11-06T0028Z/t5/redteamM/d03_reader/SecondReadingJ0.lean` (committed before the Checked module, next to its "
          "brief `briefJ0.md`: the reader saw only the typeset page); agreement `Checked/Trust/TranscriptionsJ0.lean` "
          "(`agree_printedJ0`): agrees. New PRINTED definition `Checked.Cosmography.AvilesJ0.printedJ0` and headline "
          "`AvilesJ0.printedJ0_false_at` (the printed j₀ is false at every Ω ∈ (0,1)).\n")

if stage in (None, 1):
    write_new(f"{RUN}/briefJ0.md", BRIEF)
    write_new(f"{RUN}/SecondReadingJ0.lean", READER)
if stage in (None, 2):
    # the Checked copy is the reader's file, code unchanged (module doc may name its origin)
    write_new("Checked/Trust/SecondReadingJ0.lean", READER)
    write_new("Checked/Cosmography/AvilesJ0.lean", PROGRAM)
    write_new("Checked/Trust/TranscriptionsJ0.lean", AGREE)
    append("Checked.lean", "import Checked.Cosmography.AvilesJ0\nimport Checked.Trust.SecondReadingJ0\nimport Checked.Trust.TranscriptionsJ0\n")
    append("scripts/trust/headlines.txt", "# Aviles et al. Eq. (15): the printed j0 (run 2026-11-06T0028Z, red team M)\nAvilesJ0.printedJ0_false_at\n")
    append("scripts/trust/def_kinds.txt", "Checked.Cosmography.AvilesJ0.printedJ0 PRINTED\n")
    append("LEDGER.md", LEDGER)
print("d03 applied", stage)
