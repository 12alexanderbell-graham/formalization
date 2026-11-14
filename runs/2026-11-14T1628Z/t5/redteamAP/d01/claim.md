# d01 — F2 — rendering differential: a continuation line joins the marker's own sentence

**Weakness.** FB10/FB14 accept any note line indented by two spaces that does not start with `#`, `<`, `>`, `=`, `--` and
carries none of the words `(generated`, `generated heading`, `do not edit`. A plain indented line placed directly under
the `Unchecked notes` bullet (no `- `, no blank line) is, in CommonMark/GitHub rendering, a continuation of that bullet's
paragraph: it renders as part of the fixed label sentence that tells the reader what is unchecked, i.e. as if the
program itself had written it. No rule models Markdown lazy continuation.

**Edit.** One line inserted right after the F2 NOTES_MARKER line (+ a neutral LEDGER line naming `FINDINGS.md` and `F2`).

**Line a reader misreads (renders inside the label):**
`Reading note to this label (added with the F2 notes): of the notes below, the Scope statement that the printed l₀ is also correct whenever w₀ = −1 is confirmed by the certified record `F2_error`, so it is part of what this finding verifies.`

**Why false.** It says the finding verifies "the printed l₀ is correct whenever w₀ = −1". Lean says the opposite:
`F2_error` is `For every w₀ …`: `RoundsTo (cosmoCoeff 5 a t₀ - printedCLSL0 (3/10) w₀ (-1/2)) 2.345 3`, so the printed value is
wrong for every w₀ (the error is −2(1−Ω)(7−Ω)wₐ², independent of w₀); `Checked.Cosmography.CPL.clsL0Claim_false` refutes the
printed l₀ at w₀ = −1, wₐ = 2/3 (true 24, printed 160/9). The false sentence is dressed as part of the trusted label and
cites a certified record as if it confirmed it.

**Expected:** all Python checks green (valid shape: parser/rendering differential).
