# Brief: blind literal reading of printed F(R) cosmography formulas (run 2026-11-14T1628Z)

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

Paper: K. Bamba, S. Capozziello, S. Nojiri, S. D. Odintsov, "Dark energy cosmology: the equivalent description via different theoretical models and cosmography tests", arXiv:1205.3421, **version 3**, Section XI (testing F(R) gravity by cosmography). It expresses F(R₀) and its derivatives through polynomials of the cosmographic parameters q₀, j₀, s₀, l₀, then evaluates them in the ΛCDM model as functions of the matter density parameter (written Ω_M or Ω_m in that section).

Read, exactly as printed:
1. `noncomputable def bamba12PrintedP0 (q j s l : ℝ) : ℝ` := the polynomial 𝒫₀ of Eq. (11.25).
2. `noncomputable def bamba12PrintedQ0 (q j s l : ℝ) : ℝ` := the polynomial 𝒬₀ of Eq. (11.26).
3. `noncomputable def bamba12PrintedR (q j s l : ℝ) : ℝ` := the polynomial ℛ of Eq. (11.31).
4. `noncomputable def bamba12LCDMq0 (Ω : ℝ) : ℝ` := q₀ in the ΛCDM model as printed in Eq. (11.39), as a function of the matter density parameter.
5. `noncomputable def bamba12LCDMl0 (Ω : ℝ) : ℝ` := l₀ in the ΛCDM model as printed in Eq. (11.39).
6. `noncomputable def bamba12PrintedEtaDen (Ω : ℝ) : ℝ` := the polynomial in the matter density parameter that stands as the denominator of the fraction in both Eq. (11.42) and Eq. (11.43) (only that polynomial, without the separate factors that multiply ε). As a check of your reading, evaluate the two printed fractions with your transcription at the values of the matter density parameter that the paper uses in Eqs. (11.44)–(11.45) and compare with the numbers printed there; say in your report whether they agree.

Arguments: q = q₀, j = j₀, s = s₀, l = l₀; Ω = the matter density parameter.

Also compare items 1–6 with versions 1 and 2 of the same arXiv id in your report.

Output path: `runs/2026-11-14T1628Z/reader_bamba11/SecondReadingFreshBambaFR.lean`.
