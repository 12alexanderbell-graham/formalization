import Mathlib.Data.Real.Basic
/-! Blind literal reading of the printed F(R) cosmography polynomials and ΛCDM parameters of Bamba, Capozziello, Nojiri and Odintsov (Section XI of their review, third arXiv version), copied from `runs/2026-11-14T1628Z/reader_bamba11/SecondReadingFreshBambaFR.lean` (code verbatim; module doc and definition docs rewritten without numbers: the reader's own description of the source is in that file, and `scripts/trust/check_findings.py` prints it in the findings' generated Printed lines). Reader: an independent Sonnet subagent that downloaded and rendered the arXiv PDF itself, from the brief committed alone before it in that folder. -/
namespace Checked.Trust.SecondReading
/-- Blind reading by an independent reader; source described in `runs/2026-11-14T1628Z/reader_bamba11/SecondReadingFreshBambaFR.lean`. -/
noncomputable def bamba12PrintedP0 (q j s l : ℝ) : ℝ :=
  (j - q - 2) * l - (3 * s + 7 * j + 6 * q ^ 2 + 41 * q + 22) * s
    - ((3 * q + 16) * j + 20 * q ^ 2 + 64 * q + 12) * j
    - (3 * q ^ 4 + 25 * q ^ 3 + 96 * q ^ 2 + 72 * q + 20)
/-- Blind reading by an independent reader; source described in `runs/2026-11-14T1628Z/reader_bamba11/SecondReadingFreshBambaFR.lean`. -/
noncomputable def bamba12PrintedQ0 (q j s l : ℝ) : ℝ :=
  (q ^ 2 - j * q + 2 * q) * l
    + (3 * q * s + (4 * q + 6) * j + 6 * q ^ 3 + 44 * q ^ 2 + 22 * q - 12) * s
    + (2 * j ^ 2 + (3 * q ^ 2 + 10 * q - 6) * j + 17 * q ^ 3 + 52 * q ^ 2 + 54 * q + 36) * j
    + 3 * q ^ 5 + 28 * q ^ 4 + 118 * q ^ 3 + 72 * q ^ 2 - 76 * q - 64
/-- Blind reading by an independent reader; source described in `runs/2026-11-14T1628Z/reader_bamba11/SecondReadingFreshBambaFR.lean`. -/
noncomputable def bamba12PrintedR (q j s l : ℝ) : ℝ :=
  (j - q - 2) * l - (3 * s - 2 * j + 6 * q ^ 2 + 50 * q + 40) * s
    + ((3 * q + 10) * j + 11 * q ^ 2 + 4 * q + 18) * j
    - (3 * q ^ 4 + 34 * q ^ 3 + 246 * q + 104)
/-- Blind reading by an independent reader; source described in `runs/2026-11-14T1628Z/reader_bamba11/SecondReadingFreshBambaFR.lean`. -/
noncomputable def bamba12LCDMq0 (Ω : ℝ) : ℝ :=
  1 / 2 - (3 / 2) * (1 - Ω)
/-- Blind reading by an independent reader; source described in `runs/2026-11-14T1628Z/reader_bamba11/SecondReadingFreshBambaFR.lean`. -/
noncomputable def bamba12LCDMl0 (Ω : ℝ) : ℝ :=
  1 + 3 * Ω + (27 / 2) * Ω ^ 2
/-- Blind reading by an independent reader; source described in `runs/2026-11-14T1628Z/reader_bamba11/SecondReadingFreshBambaFR.lean`. -/
noncomputable def bamba12PrintedEtaDen (Ω : ℝ) : ℝ :=
  (3 * (9 * Ω + 74) * Ω - 556) * Ω ^ 2 + 16
end Checked.Trust.SecondReading
