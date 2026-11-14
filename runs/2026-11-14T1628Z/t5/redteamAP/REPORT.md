# Red team AP report (BASE fde8092)

Testing note: the shared disk filled up (another consumer; my 200 MB copies could not be kept), so d01-d05 were tested with a
light harness (symlink tree + real copies of FINDINGS.md/LEDGER.md): check_numbers, check_findings, check_prose, check_claims
(plain and --base fde8092) and make_packet --check, all green. The full CI-without-Lean list was run once green on the clean
snapshot (before the disk filled); the other checks do not read FINDINGS.md or the findings registries. d06 needs commits and was
not run through the checks (only FB12/FB15/FB17 (a) and the generated Correct line were evaluated in-process: all pass; FB17 (b)
passes only through the route, which is a forged one). d02's first wording was caught by FB5 (backticked record name followed
by "(every ...)"); the shipped wording avoids it.

| d | category | one line | line a reader would misread | expected |
|---|---|---|---|---|
| d01 (F2) | rendering differential in the frame/marker | an indented plain line right under the NOTES_MARKER renders as part of the label sentence | "Reading note to this label ...: the Scope statement that the printed l0 is also correct whenever w0 = -1 is confirmed by the certified record F2_error" (false: F2_error holds for every w0, clsL0Claim_false at w0=-1) | all green |
| d02 (F5) | rendering differential (inline HTML) | `</li></ul>` in a note ends the notes list; a bold top-level "Correct, confirmed by the certified record F5_values" paragraph follows | "the printed y2-coefficient is 1/24 and the correct one is 1/12" (F5_values: printed 0.4167 > correct 0.2083) | all green |
| d03 (F3) | look-alike of a generated line (homoglyphs defeat FB14 mark words) | a note shaped exactly like the generated Printed line, with a fake "reader" attribution to Visser 2004 | "the reader (file runs/.../SecondReadingClaimsB.lean, as first committed) wrote of this value: Visser ... Eq. (51)" (real line: no reader file describes printedD4) | all green |
| d04 (F8) | rendering differential (setext heading via one-dash underline, FB14 only bans `--`/`=`) | a note renders as a heading "Correct, checked against Lean (F8_sizes)" with sizes 100x too large | "omitted z^5 term is 56 per cent ... 670 per cent" (F8_sizes: 0.56 and 6.7) | all green |
| d05 (candidates) | candidates-section pointer | new row "-> **F1**" marks an invented Planck claim as promoted to a verified finding | "| C32 | Planck 2018 ... | printed Omega_m = 0.3153 should be 0.3053 | -> **F1** |" (out of scope by the brief; submitted because named) | all green |
| d06 (F1, F3) | KNOWN: forged blind-route reading (class phrase) | registry line `ContDiffAt ℝ 6 a t₀ => analytic scale factors` through an author-made brief/reading/copy | generated Correct line: "class: analytic scale factors (Lean: `ContDiffAt ℝ 6 a t₀`)" (Lean: C^6 at one point only) | green by construction of the route (untested end to end) |

Findings on the claim "every input is Lean output or a blind-route reading": the generated lines are tight; the residue is
(i) forged routes (d06) and (ii) rendering: FB14 is a line-start regex list, so any Markdown/HTML construct whose effect
does not need a forbidden first character escapes it (d01 lazy continuation into the label, d02 inline HTML closing the
list, d04 one-dash setext, d03 homoglyph look-alikes). Suggested repair: notes must be one-line `  - *(author)* ...` bullets
only (reject any other line shape, any `<`, `>` or non-ASCII-confusable letters in the generated words).
Memory: nothing read or learned worth saving.
