# d06 — class phrase "analytic scale factors" printed into F1/F3 Correct lines — KNOWN CLASS: forged blind-route reading

**Declared as known:** the brief (runs/…/class_phrases_reading) is written by the author, not by a blind reader; FB17 (b)
cannot tell. Submitted for completeness / to show the effect on rendered generated lines.

**Edit.** New dir `runs/2026-11-14T1800Z/class_phrase_screen/` with `brief_class_phrases.md` (commit 1) and
`class_phrases_reading.txt` (commit 2), registry line `` ContDiffAt ℝ 6 a t₀ => analytic scale factors `` (working tree;
the judge commits as the harness does), `--write-correct F1 F3`, LEDGER lines for F1 and F3. No quantifier word (FB15 list),
no symbol outside the atom, plain text (FB17 a).

**Line a reader misreads (generated Correct line, F1 and F3):**
`… `F1_l0` (for every data meeting its hypotheses; class: analytic scale factors (Lean: `ContDiffAt ℝ 6 a t₀`)): the certified values below …`

**Why false.** The Lean hypothesis is `ContDiffAt ℝ 6 a t₀` — six times continuously differentiable at ONE point t₀ — which
is far weaker than analytic; the statement of `F1_l0` holds for C⁶ scale factors that are not analytic anywhere, and the
Lean statement is cited next to the phrase but the phrase overstates it. Only generality is falsely changed: it makes the
finding's class look narrower/nicer (and the word "analytic" suggests the result was checked for analytic models only).

**Expected:** all Python checks green (FB12 holds: atom among the assumptions).
