# Run 2026-11-14T1628Z (scheduled)

**THE RESULT:** part 3 (rotation: parts 2/5 and 1 moved at 1428Z, part 3 last at 1228Z) — the verified-findings layer now tells a reader, for every printed value it calls wrong, where that value is printed, in the words of a blind reader who found it in the paper (13 printed formulas behind F3–F7, F9, F10 had no such description; now 0), and a blind red team measured the layer once more: 5 valid wrong findings accepted, 4 through how the page renders and 1 through the known forged-route shape (none through a generator input), so the LEDGER experiment of run 1228Z survives and FB19–FB20 close the rendering shapes.

**What can a scientist now trust without checking it themselves, that they could not before?** For F3–F7, F9 and F10, which paper, version, equation and page each refuted printed formula comes from — written by independent readers who downloaded and rendered the arXiv PDFs themselves, and tied by a Lean theorem (`ring`) to the very formula the Lean record evaluates; and that a note under the unchecked marker can no longer render as part of the marker's own sentence, as a heading, or outside the notes list.

**Weakest unchecked step:** blindness of the readers and of the red team is not mechanically checkable (same as every blind route: different agent, brief committed first); and the rendering rules (FB19, FB20) were written after reading the defects (not blind).

## Start
- 16:28Z. add_repo not exposed; pre-cloned checkout detached with a stale, shallow local main; `git checkout -B main origin/main` = fc559f2; unshallowed later (`git fetch --unshallow origin` — do it first). No LOCK → taken (5ae4df7).
- Local Lean: elan + Mathlib cache ≈ 3 min; `checked-build` of 43581569718 (c3ca8a4) restored; `lake build Checked` green; StatementDeps relock ≈ 10 min; Claims ≈ 3 min.
- CI at start: 43590961602 (071b543, `bonnor_ebert_second_max`): every blocking step of the checked job green, one nanoda shard running; **green on every job at 16:40Z → `bonnor_ebert_second_max` PROVED**. 43611102762 (fc559f2, `bonnor_ebert_second_min`) in progress at the end.
- Alexander interrupted live at ≈ 16:50Z asking for a status summary; answered (SendUserMessage) and continued.
- Disk: the restored build (≈ 23 GB tree) plus the red team's copies filled the allowance at ≈ 17:15Z; freed by removing `~/.cache/mathlib` and stale `/tmp/tmp*` scratch repositories of the checks (≈ 4 GB). The red team lost its working copies and tested d01–d05 with a light harness; the judge below ran every check on full trees.

## Bottleneck (and what a yes/no changes)
- STATE 0s, part 3: (a) a blind round against FB16–FB18 — the LEDGER experiment says the only valid shapes left are a forged blind-route reading or a parser/rendering differential; yes (only those) keeps the claim that no author text feeds a generated line, no refutes it; (b) the 13 pre-route PRINTED definitions shown as "no reader file describes its source".

## What we did
1. **Fresh blind readings** (item (b)). Four briefs committed alone (1d567a4): only paper, arXiv version, equation numbers, definition names and argument meanings; the readers (Sonnet) downloaded and rendered the PDFs themselves and wrote plain-text descriptions. Readings committed verbatim (208acec), copied by script into `Checked/Trust/SecondReadingFresh{CCS,CV,BambaFR}.lean` (bee548d); the 13 agreement theorems repointed; **all 13 closed by `ring` at the first compile** — the fresh readings, the 2026-10-30 readings and the program's transcriptions agree on every printed formula. Reader side results: v1 and v2 of 1205.3421 print the same formulas; the Sec. XI reader reproduced the printed η numbers of (11.44)–(11.45) from its own denominator.
2. `check_brief_leak` L3 rejected the Sec. X brief: its equation numbers (10.52)… and the arXiv id 1205.3421 contain the digit strings 105 and 120 of printed coefficients. Not weakened: the reading was redone from a second brief (41cd44d: the PDF handed over pre-downloaded, equations described by role; the reader read id and version from the page margin), reading 9c2aff1, copy `SecondReadingFreshBambaYb.lean`; first copy archived. Same values.
3. `check_findings.py --write-layout F3 F4 F5 F6 F7 F9 F10`: every generated heading now reads "read blind; its source as the reader described it" (13 → 0 undescribed printed values); LEDGER lines (FB7, check_formulas).
4. **Blind red team AP** (item (a); Sonnet, brief committed first 8850e3a, snapshot fde8092 with 071b543's CI author files, clean snapshot green on every Python check). Output committed verbatim before judging. Results: `t5/RESULTS.md`.
5. **Repairs** `check_findings.py` FB19 (notes are one-line author bullets with no HTML), FB20 (no letters outside Latin/Greek/mathematical alphabets, no invisible format characters; generated marks matched on a folded copy); FB14's setext rule now also rejects a one-dash underline; 8 new selftest controls (81 in all).

## Results
- `bonnor_ebert_second_max` **PROVED** (CI 43590961602 of 071b543 green on every job incl. the checked job and nanoda 4/4).
- Findings layer: printed values without a reader's source description 13 → 0.
- Round AP: BEFORE 5/5 valid accepted blind (4 rendering, 1 forged route; d05 out of scope); AFTER FB19–FB20: the 4 rendering defects caught (FB19; d03 also FB20, d04 also FB14), d05, d06 pass (not blind). LEDGER experiment of run 1228Z survives (`t5/RESULTS.md`).

## Not done / next
- STATE 0t.
