import Mathlib.Data.Real.Basic
/-! Blind literal reading of the printed y-redshift luminosity and angular diameter distance coefficients of Bamba, Capozziello, Nojiri and Odintsov (Section X of their review, third arXiv version), copied from `runs/2026-11-14T1628Z/reader_bamba10/SecondReadingFreshBambaY.lean` (code verbatim; module doc and definition docs rewritten without numbers: the reader's own description of the source is in that file, and `scripts/trust/check_findings.py` prints it in the findings' generated Printed lines). Reader: an independent Sonnet subagent that downloaded and rendered the arXiv PDF itself, from the brief committed alone before it in that folder. -/
namespace Checked.Trust.SecondReading
/-- Blind reading by an independent reader; source described in `runs/2026-11-14T1628Z/reader_bamba10/SecondReadingFreshBambaY.lean`. -/
noncomputable def bamba12PrintedDL2y (q j Ω : ℝ) : ℝ :=
  -(1 / 6) * (12 - 5 * q + 3 * q ^ 2 - j - Ω)
/-- Blind reading by an independent reader; source described in `runs/2026-11-14T1628Z/reader_bamba10/SecondReadingFreshBambaY.lean`. -/
noncomputable def bamba12PrintedDL3y (q j s Ω : ℝ) : ℝ :=
  (1 / 24) * (52 - 20 * q + 21 * q ^ 2 - 15 * q ^ 3 - 7 * j + 10 * q * j + s - 2 * Ω * (1 + 3 * q))
/-- Blind reading by an independent reader; source described in `runs/2026-11-14T1628Z/reader_bamba10/SecondReadingFreshBambaY.lean`. -/
noncomputable def bamba12PrintedDL4y (q j s l Ω : ℝ) : ℝ :=
  (1 / 120) * (359 - 184 * q + 186 * q ^ 2 - 135 * q ^ 3 + 105 * q ^ 4 + 90 * q * j - 105 * q ^ 2 * j - 15 * q * s + -(57 * j) + 10 * j ^ 2 + 9 * s - l - 5 * Ω * (17 - 6 * q + 9 * q ^ 2 - 2 * j))
/-- Blind reading by an independent reader; source described in `runs/2026-11-14T1628Z/reader_bamba10/SecondReadingFreshBambaY.lean`. -/
noncomputable def bamba12PrintedDA3y (q j s Ω : ℝ) : ℝ :=
  -(1 / 24) * (-2 * q + 3 * q ^ 2 + 15 * q ^ 3 - j - 10 * q * j - s + 2 * Ω)
/-- Blind reading by an independent reader; source described in `runs/2026-11-14T1628Z/reader_bamba10/SecondReadingFreshBambaY.lean`. -/
noncomputable def bamba12PrintedDA4y (q j s l Ω : ℝ) : ℝ :=
  -(1 / 120) * (1 - 6 * q + 9 * q ^ 2 - 15 * q ^ 3 - 105 * q ^ 4 + 10 * q * j + 105 * q ^ 2 * j + 15 * q * s + -(3 * j) - 10 * j ^ 2 + s + l + 5 * Ω)
end Checked.Trust.SecondReading
