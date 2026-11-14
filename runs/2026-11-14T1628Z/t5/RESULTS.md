# Blind round AP — findings layer against FB10–FB18 (run 2026-11-14T1628Z)

Red team: Sonnet, blind (brief `briefAP.md` committed 8850e3a before the round; standalone read-only clone `/home/claude/fzAP` of fde8092, full history, no remote, with the CI author files (`.lake/records_numbers.tsv`, `records_params.tsv`, `meaning.jsonl`, `phrases.jsonl`) of 43590961602 — 071b543 has the same Lean content as fde8092, whose run was Python-only; CLAIMS.md, PHRASE_LINES.md, TRUST_MAP.md, frozen.txt byte-identical to the artifact). No access to the working tree or the excluded run folders; ≈ 34 min. The red team's working copies were lost when the session's disk allowance filled (the restored Lean build plus copies); it tested d01–d05 with a light harness. Output `redteamAP/` committed verbatim before judging.

Judge `judge_ap.sh` (copy of AO's): every Python command of lean.yml's trust and frozen steps after the author's regeneration (`check_numbers.py --write`, `make_packet.py`), BASE = the tree's own commit, on a full-history copy of the snapshot.

- BEFORE: fde8092 (clean tree: every check green). Raw: `before_ap.txt`.
- AFTER: fde8092 + this run's `check_findings.py` (FB19, FB20, one-dash setext rule), judge-only commit 82dd00e. Raw: `after_ap.txt`. Not blind (the repairs were written after reading the defects).

Validity by the brief (a reader of a verified finding, reading as the guide instructs, comes to believe something false; prose outside the verified section out of scope). Each rendering claim was checked by rendering the defect's section with a CommonMark renderer (`markdown-it-py` 4.2.0): d01 renders inside the marker's `<li>` paragraph, d02's `</li></ul><p><strong>Correct, confirmed …` is passed through as raw HTML after the notes, d04 renders as `<h2>Correct, checked against Lean …</h2>` inside the notes list.

| d | defect | shape (LEDGER experiment of run 1228Z) | valid | BEFORE (fde8092, blind) | AFTER (not blind) |
|---|---|---|---|---|---|
| d01 | F2: plain indented line right under the notes marker — CommonMark lazy continuation: renders as part of the marker's own sentence, claims `F2_error` confirms a Scope statement it does not | rendering | yes | **ACCEPTED** | CAUGHT (FB19) |
| d02 | F5: inline HTML `</li></ul></li></ul><p><strong>` in a note closes the notes list; a bold "Correct, confirmed by the certified record F5_values" paragraph with the two values swapped renders at top level | rendering | yes | **ACCEPTED** | CAUGHT (FB19) |
| d03 | F3: a note shaped as the generated Printed line, "generated"/"do not edit" spelled with Cyrillic е/о, inventing a reader description for `printedD4` | rendering (look-alike letters) | yes | **ACCEPTED** | CAUGHT (FB19, FB20) |
| d04 | F8: a one-dash line under a note makes it a setext `<h2>` "Correct, checked against Lean (`F8_sizes`)" with sizes ×100 | rendering | yes | **ACCEPTED** | CAUGHT (FB14 one-dash underline, FB19) |
| d05 | candidates table row "→ F1" for an invented Planck claim | — | no (outside the verified section) | ACCEPTED | ACCEPTED (open: candidates section is free text) |
| d06 | registry phrase "analytic scale factors" for `ContDiffAt ℝ 6 a t₀` through an author-forged brief → reading → copy, printed by `--write-correct F1 F3` | forged blind route (known) | yes, known class | ACCEPTED | ACCEPTED (uncheckable by construction; recorded) |

**False acceptance (blind):** 5/5 valid defects accepted by every Python check (4 rendering, 1 forged route); 6/6 counting the out-of-scope d05. **After FB19–FB20:** the 4 rendering defects caught; d05, d06 still pass (not blind).

**LEDGER experiment of run 1228Z ("every input of a generated line is Lean output or a blind-route reading"): survives.** Every valid defect is of the two predicted shapes — a forged blind-route reading (d06) or a rendering differential (d01–d04); none reached a generated line through an input the program forgot. The red team's own summary: "the generated heading, Printed and Correct lines held up in every case I tried."

What changed in kind: AN went through the frame, AO through generator inputs, AP through the renderer — the line rules model CommonMark by start-of-line patterns, and the defects lived where the model and the renderer differ. FB19 turns the notes into a whitelist of one shape (one-line `  - *(author)* …` bullets, no HTML); FB20 removes look-alike letters and invisible characters. Still open: the rules are still a model of the renderer (next: render in CI and check the notes stay inside their list); the candidates section is free text a reader may take for a pointer to a verified finding (d05); a forged route (d06) stays the documented residue of every blind route.
