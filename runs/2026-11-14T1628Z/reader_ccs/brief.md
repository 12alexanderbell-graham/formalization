# Brief: blind literal reading of a printed cosmographic coefficient (run 2026-11-14T1628Z)

## Rules (read first)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path named below; in particular never open `Checked/`, `Work/`, `scripts/`, `validation/`, any other file or folder under `runs/`, or any `*.md` file other than this brief, and do not use git. Do not search the web and do not open any site except the one download below.

Download the paper yourself into a NEW temporary directory outside the repository (for example `mkdir -p /tmp/rdr_$RANDOM` and work there): `curl -sSfL -o p.pdf https://arxiv.org/pdf/<id>v<N>` with the id and version given below. Do not use `arxiv.org/e-print/`, ar5iv, export.arxiv.org or any mirror. Find the page with `pdftotext -f P -l P p.pdf -` (pdftotext garbles mathematics: use it only to find the page), render it with `pdftoppm -r 200 -f P -l P -png p.pdf page`, crop the equations with Python PIL at a size you can read, and READ THE IMAGE with your Read tool. Transcribe from the typeset image only. Nothing you download or render goes into the repository; the only file you write is the output file.

## Output

Write ONE Lean 4 file at the output path below, with exactly this shape:

```lean
import Mathlib.Data.Real.Basic
/-! <module doc, your own words> -/
namespace Checked.Trust.SecondReading
/-- <definition doc, your own words> -/
noncomputable def <name> (<arguments> : ℝ) : ℝ :=
  <the printed expression>
<... one definition per item below, in the order listed ...>
end Checked.Trust.SecondReading
```

- Module doc: who read it ("an independent reader"), the paper (authors, year, arXiv id and version you downloaded), and which equations you read. Definition doc: the paper, the equation number(s), the page of the PDF where you read it, the symbol the paper uses, what the quantity is in one sentence, and any reading choice you had to make (a symbol you could not read with certainty, a line break between two signs, a missing subscript). Docs are PLAIN TEXT: no backticks, no Markdown (no asterisks, underscores for emphasis, links, headings), no HTML, no URLs. Unicode mathematical symbols are fine.
- The expression: the printed expression, faithfully, as a Lean real expression in the named arguments: keep the printed grouping and prefactors (e.g. a printed −(2/7)(…) becomes `-(2 / 7) * (…)`), write fractions as `a / b`, powers as `x ^ n`, products with `*`; every printed coefficient exactly as printed, even if you think it is wrong (do not correct anything; report suspected misprints in the doc and in your report). No other definitions, no `def` without `noncomputable`, no comments other than the docs. Lean is not installed for you: do not install or compile; write the file carefully and re-read each formula against the image term by term at the end.

## Report (your final message)

For each definition: the line(s) you wrote, the page, a one-line description of what the typeset formula looks like (layout, line breaks), anything uncertain. Also say whether the other arXiv versions named below print the same formulas (download them the same way and compare), if the brief asks.

## What to read

Paper: S. Capozziello, V. F. Cardone, V. Salzano, "Cosmography of f(R) gravity", arXiv:0802.1583, **version 2** (v1 has no appendix). In its Appendix A, Eq. (A2) prints a series for a distance D(z) in powers of the redshift z with coefficients D⁰_z, D¹_z, D²_z, D³_z, D⁴_z, written in terms of the cosmographic parameters q₀, j₀, s₀, l₀ (deceleration, jerk, snap, lerk).

Read the coefficient **D⁴_z** exactly as printed (it runs over several printed lines).

Arguments: q = q₀, j = j₀, s = s₀, l = l₀.

1. `noncomputable def ccs08PrintedD4z (q j s l : ℝ) : ℝ` := the printed D⁴_z.

Output path: `runs/2026-11-14T1628Z/reader_ccs/SecondReadingFreshCCS.lean`.
