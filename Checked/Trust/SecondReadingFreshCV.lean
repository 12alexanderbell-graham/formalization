import Mathlib.Data.Real.Basic
/-! Blind literal reading of the printed y-squared coefficient of the deceleration-distance series of Cattoën and Visser (their cosmographic Hubble fits paper, only arXiv version), copied from `runs/2026-11-14T1628Z/reader_cv/SecondReadingFreshCV.lean` (code verbatim; module doc and definition docs rewritten without numbers: the reader's own description of the source is in that file, and `scripts/trust/check_findings.py` prints it in the findings' generated Printed lines). Reader: an independent Sonnet subagent that downloaded and rendered the arXiv PDF itself, from the brief committed alone before it in that folder. -/
namespace Checked.Trust.SecondReading
/-- Blind reading by an independent reader; source described in `runs/2026-11-14T1628Z/reader_cv/SecondReadingFreshCV.lean`. -/
noncomputable def cv07PrintedQ2 (q j Ω : ℝ) : ℝ :=
  (1 / 12) * (3 - 2 * q + 12 * q ^ 2 - 4 * (j + Ω))
end Checked.Trust.SecondReading
