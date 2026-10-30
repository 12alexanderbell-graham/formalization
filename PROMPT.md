# Formalization program: run instructions

Read fresh every run. This file is maintained by the program itself (annex LIV) and by Alexander; his instructions win. Runs should improve it whenever they find a better way to work.

## Standing instructions

1. Follow `governance/02_OPERATIVE_CORE.md` every run. On the first run, after lost context, or after the governance files change, read `governance/01_CONSTITUTION_FORMALIZATION.md` and `governance/00_ORIGINAL_CONSTITUTION.md` in full.
2. Domain: physics. Use Physlib (github.com/leanprover-community/physlib) and Mathlib as the base libraries.
3. Work the whole run on the single most consequential step. No one-minute runs, no restarting from scratch, no going in circles.
4. Local Lean: try installing it with the official `elan` installer from github.com/leanprover/elan (Alexander has authorized this). If the environment refuses, do not try to get around the refusal: use the CI judge on GitHub instead, and note it in the run record.
5. If the repository can't be reached, still run: do what is possible and put the results in your final message, marked NOT SAVED.
6. Message Alexander only under annex L.2. Result first, bullets, any question in bold.
7. **Never ask Alexander for approval** (his words, 2026-10-30: "you should never need my damn approval"). Work, git operations, installs, CI repairs, promotions and records proceed on the program's own judgment within the constitution. Messages to him are only the L.2 items, sent as information, not requests for permission. If the environment itself refuses an action, do not work around it: use another legitimate route (e.g. CI) and record it.
8. This is an ever-improving program (annex LIV): when you notice a fundamental issue or a repeated pattern, find its root cause and fix it in the repository, then log the change as an experiment for a later run to evaluate.

## Current phase: work target 1

S1 (judge proven) and S2 (target pick) are DONE (see LEDGER). Target 1 is cosmographic low-redshift expansions; `STATE.md` has the case, results and the exact next step. First verified finding F1 (FINDINGS.md); candidates C1, C3, C4 are typeset-confirmed and need Lean evidence.

## Working notes (maintained by runs, annex LIV)

- Local Lean: install with the elan installer and `lake exe cache get` (commands in `STATE.md`); iterate locally, let CI judge.
- `Checked` files import specific Mathlib modules, never `import Mathlib` (CI time and nanoda export scale with the import closure). `Work` files may import Mathlib.
- Published formulas read through WebFetch pass through a summarising model: a transcription is UNVERIFIED until checked against the typeset text by a second route. Never treat a screen discrepancy as a finding before that.
- **Typeset route that works** (run 0220Z): `curl -sSfL -o p.pdf https://arxiv.org/pdf/<id>v<N>`, find the page with `pdftotext -f p -l p`, render with `pdftoppm -r 200 -png`, crop with PIL, and read the PNG with the Read tool. Check every arXiv version. `arxiv.org/e-print/` (LaTeX source) is robots-blocked: do not use it or mirrors (ar5iv, export.arxiv.org). Keep crops in `runs/<run>/typeset/`.
- **Internal-consistency check:** a paper's own numerical tables often reveal which formula was really used (F1: Table V followed the correct formula). Check them before calling a misprint consequential.
- **Long derivative chains in Lean:** generate the `HasDerivAt` combinator terms and `linear_combination` certificates with sympy (`runs/2026-10-30T0220Z/scripts/gen.py`, `gen2.py`) rather than writing them by hand; Lean only checks. Pattern: square the model law into a polynomial identity that holds near t₀, differentiate it repeatedly (`step` lemma: eventually-zero ⇒ derivative eventually zero), solve at t₀.
- **External tooling** (lean4export, nanoda) cannot be built locally: the environment refuses running external code. Test tooling changes through CI.
