# Brief: blind literal reading of a printed Falkner–Skan parameter value (run 2026-11-11T0828Z)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `runs/` (other than this folder), `scripts/`, `validation/`, or any `*.md` there, and do not use git to look at history.

Find the published value yourself in two papers by R. Fazio on the Falkner–Skan model f''' + f f'' + β(1 − f'²) = 0, f(0) = f'(0) = 0, f' → 1:
- arXiv:1212.5057 ("Blasius problem and Falkner–Skan model: Töpfer's algorithm and its extension", 2012), and
- arXiv:2011.07725 ("Existence and uniqueness of BVPs defined on semi-infinite intervals: insight from the iterative transformation method", 2020).
In each, locate the figure whose caption gives the value of β for which the plotted solution has d²f/dη²(0) = 0 (the limiting value β_min), and read the printed β in that caption. Use only arxiv.org/abs or arxiv.org/pdf (never ar5iv, never e-print, never a mirror); if a fetch fails or is refused, record "not read" and do not retry by another route. Render the page with `pdftoppm -r 200 -png -f P -l P` and read the image (the typeset text), not only a text extraction. Downloads, renders and text dumps go to a temporary directory outside the repository (e.g. /tmp/fazio_reader); only your Lean file goes into this folder. Also check the governing equation's form in each paper (the coefficient in front of f f'' and of the bracket), and say in your report whether it matches the form above.

Write ONE Lean 4 file `runs/2026-11-11T0828Z/sep_printed_reader/SecondReadingFSSepPrinted.lean`:

```lean
import Mathlib.Data.Real.Basic
/-! Blind literal reading of the printed Falkner–Skan limiting parameter value (reader: <you>, sources: <papers, pages, figures>). -/
namespace Checked.Trust.SecondReading
/-- Fazio (arXiv:1212.5057, 2012; arXiv:2011.07725, 2020): the value of β printed in the figure caption of the solution with zero wall shear d²f/dη²(0) = 0, all printed digits, with its sign. -/
noncomputable def fsSepPrintedFazio : ℝ := ...
end Checked.Trust.SecondReading
```

Form of the body: the printed value as `-(N / D)` (or `N / D` if printed positive), N one integer numeral holding every printed digit after the decimal point (trailing zeros kept), D one integer numeral equal to ten to the number of printed decimals, no `^`. Exactly the value printed. If the two papers print different values, use the 2020 paper's and give the 2012 value in the module doc. No other definitions, no comments other than the module doc and docstring. Lean is not installed on this machine: do not try to install or compile; just write the file carefully.

Finally report: the body, for each paper the page and figure number and the caption text you saw, whether you saw the typeset page, the equation form check, and anything uncertain.
