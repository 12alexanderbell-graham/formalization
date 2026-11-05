#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])

def write(rel, text):
    p = root / rel
    assert not p.exists(), rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)

def append(rel, text):
    p = root / rel
    s = p.read_text()
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text)

write('Checked/Cosmography/CVdQJournal.lean', 'import Checked.Cosmography.CVdQ\n\n/-!\n# Cattoën & Visser, Eq. (59): the journal version (run 2026-11-05T2228Z)\n\nThe deceleration distance d_Q(y) to third order in y, with the y-squared coefficient as printed in\nthe journal version of Eq. (59). The expansion is proved for every flat model that is three times\ncontinuously differentiable at the observation time.\n-/\n\nnamespace Checked.Cosmography.CVdQJournal\n\nopen Filter Asymptotics Topology Checked.Cosmography Checked.Cosmography.Aviles\n  Checked.Cosmography.BambaY Checked.Cosmography.CVdQ\n\n/-- The y² coefficient of d_Q as printed in Eq. (59) of the journal version of Cattoën & Visser 2007\n(Class. Quantum Grav. 24, 5985). -/\nnoncomputable def printedQ2Journal (q j Ω : ℝ) : ℝ := 1 / 24 * (3 - 2 * q + 12 * q ^ 2 - 4 * (j + Ω))\n\n/-- **Deceleration distance to third order in `y` with the coefficient of the journal version of\nCattoën & Visser 2007.** The remainder is smaller than the cube of `y`. -/\ntheorem printedQ2Journal_holds (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 3 a t₀)\n    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :\n    (fun t => remainderQ printedQ2Journal a t₀ t) =o[𝓝 t₀] (fun t => yred a t₀ t ^ 3) :=\n  dQ_y_third_order a t₀ ha ha0 hH\n\nend Checked.Cosmography.CVdQJournal\n')

write('Checked/Trust/SecondReadingCVdQJournal.lean', 'import Mathlib.Data.Real.Basic\nimport Checked.Cosmography.CVdQ\n\nnamespace Checked.Trust.SecondReading\n\n/-- Cattoën & Visser, Class. Quantum Grav. 24, 5985 (2007), journal version, Eq. (59): the y² coefficient\nof d_Q(y) is the bracket `[3 − 2q₀ + 12q₀² − 4(j₀ + Ω₀)]` over 24 (the arXiv v1 prints it over 12). Written\nfrom the typeset journal page. -/\nnoncomputable def printedQ2Journal (q j Ω : ℝ) : ℝ := Checked.Cosmography.CVdQ.correctQ2 q j Ω\n\nend Checked.Trust.SecondReading\n')

write('Checked/Trust/TranscriptionsCVdQJournal.lean', 'import Checked.Trust.SecondReadingCVdQJournal\nimport Checked.Cosmography.CVdQJournal\n\nnamespace Checked.Trust.Transcriptions\n\n/-- `Checked.Cosmography.CVdQJournal.printedQ2Journal` agrees with the blind second reading. -/\ntheorem agree_printedQ2Journal : Checked.Cosmography.CVdQJournal.printedQ2Journal = Checked.Trust.SecondReading.printedQ2Journal := by\n  funext q j Ω\n  rfl\n\nend Checked.Trust.Transcriptions\n')

write('Checked/Trust/NVCVdQJournal.lean', 'import Checked.Trust.Witnesses\nimport Checked.Cosmography.CVdQJournal\n\nnamespace Checked.Trust.NV\n\ntheorem printedQ2Journal_holds : nonvacuity% Checked.Cosmography.CVdQJournal.printedQ2Journal_holds :=\n  ⟨Real.exp, 0, dS_smooth _, dS_a0, dS_hubble_ne, trivial⟩\n\nend Checked.Trust.NV\n')

append('Checked.lean', 'import Checked.Cosmography.CVdQJournal\nimport Checked.Trust.SecondReadingCVdQJournal\nimport Checked.Trust.TranscriptionsCVdQJournal\nimport Checked.Trust.NVCVdQJournal\n')
append('scripts/trust/headlines.txt', 'CVdQJournal.printedQ2Journal_holds\n')
append('scripts/trust/def_kinds.txt', 'Checked.Cosmography.CVdQJournal.printedQ2Journal PRINTED\n')
append('LEDGER.md', '## 2026-11-05 · run 2026-11-05T2228Z · journal version of Cattoën & Visser Eq. (59), read a second time (part 1)\n- **Blind second reading** (Sonnet, typeset journal page only; brief `runs/2026-11-05T2228Z/second_reading_claims/BRIEF_E.md`), copied verbatim to `SecondReadingCVdQJournal.lean` (`printedQ2Journal`). Agreement `TranscriptionsCVdQJournal.lean` (`agree_printedQ2Journal`): agrees. New headline `printedQ2Journal_holds`; witness `NVCVdQJournal.lean`.\n')
