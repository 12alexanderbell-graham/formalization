# Brief: blind literal reading of the ROBER end time and printed reference value (run 2026-11-06T1028Z)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `runs/` (other than this folder), `scripts/`, `validation/`, or any `*.md` there, and do not use git to look at history. Find the published values yourself: the problem "ROBER" (Robertson's chemical kinetics problem) in the Bari IVP test set (F. Mazzia, C. Magherini et al., "Test Set for IVP Solvers", University of Bari, release 2.4, 2008; the PDF of the report or of the ROBER problem section, from the test-set web pages at Bari / archimede.uniba.it or a mirror of the report). Record which document and which page/table you used and whether you saw the typeset text (render PDF pages to PNG with `pdftoppm -r 200` and read the image) or only a text extraction. For arXiv use only arxiv.org/abs or arxiv.org/pdf pages (never ar5iv, never e-print). Downloaded PDFs, renders and text dumps go to a temporary directory outside the repository (e.g. /tmp/robL_reader); only your Lean file goes into this folder.

Write ONE Lean 4 file `runs/2026-11-06T1028Z/rob_reader_long/SecondReadingRobLong.lean`:

```lean
import Mathlib.Data.Real.Basic
/-! Blind literal reading of the ROBER test problem's integration end time and printed reference value (reader: <you>, sources: <document, section, table>). -/
namespace Checked.Trust.SecondReading
/-- Bari IVP test set, problem ROBER: the end time T of the integration interval [0, T] specified by the test set. -/
noncomputable def robTEnd : ℝ := ...
/-- Bari IVP test set, problem ROBER: the printed reference value of the third component y₃ at the end time T, all printed digits. -/
noncomputable def robY3Ref : ℝ := ...
end Checked.Trust.SecondReading
```

Form of the bodies: `robTEnd` as an exact value written with integer literals and `*`, `^` only (a printed 3·10^5 becomes `3 * 10 ^ 5`); `robY3Ref` as an integer numeral divided by a power of ten, written out as one integer numeral over one integer numeral with no `^` (a printed 0.1250 becomes `1250 / 10000`, keeping every printed digit, including trailing zeros, in the numerator, so that the denominator is ten to the number of printed decimals). Exactly the values printed in the source. No other definitions, no comments other than the module doc and docstrings above. Use only what you read; if the report and the problem's own description disagree, say so in the module doc.

Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; lake env lean runs/2026-11-06T1028Z/rob_reader_long/SecondReadingRobLong.lean` (timeout 300000 ms). Another Lean build may be running on the machine; if the compile fails only for lack of memory, retry once after a minute.

Finally report: the two bodies, the sources (document, page, table), whether you saw the typeset page, and anything uncertain (also the other two printed components at T, as plain text in your report only).
