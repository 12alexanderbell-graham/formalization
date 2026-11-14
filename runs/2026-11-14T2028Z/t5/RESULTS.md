# Blind round AQ — findings layer after the page is rendered in CI (FB19–FB22) — run 2026-11-14T2028Z

Red team: Sonnet, blind (brief `briefAQ.md` committed b6676eb before the round; standalone clone `/home/claude/fzAQ` of a219d2b, full history, no remote, with the `.lake` outputs (`records_numbers.tsv`, `records_params.tsv`, `meaning.jsonl`, `phrases.jsonl`, `necessity.tsv`) of this run's local StatementDeps/Claims run on that tree — trust step exit 0, frozen step 21/21 against fc559f2). No access to the working tree or the excluded run folders; ≈ 13 min. Output `redteamAQ/` committed verbatim (commit after b6676eb) before judging.

Judge `judge_aq.sh` (copy of AP's): every Python command of the goal guard, the packet check, and lean.yml's trust and frozen steps after the author's regeneration (`check_numbers.py --write`, `make_packet.py`), BASE = the tree's own commit, on full-history copies of the snapshot.

- BEFORE: a219d2b (FB21, FB22 as first written). Raw: `before_aq.txt`. Clean tree: every check green.
- AFTER: a219d2b + this run's repairs (judge-only commit ba0bc53 in the judge tree; the same `check_findings.py` and `candidates_mention_baseline.txt` as committed on main). Raw: `after_aq.txt`. Not blind.

Validity by the brief (a reader of a verified finding — or of a candidates line telling what a verified finding verified — comes to believe something false).

| d | defect | shape | valid | BEFORE (blind) | AFTER (not blind) |
|---|---|---|---|---|---|
| d01 | candidates row C2 (→ F1) given free cells saying the paper's Table V numbers were computed from the misprint, with `[✓F1_…]` tags check_numbers does not read there; F1's records say nothing about Table V | candidates free cells | yes | **ACCEPTED** | CAUGHT (FB22: certified tag in the candidates; mention of F1 not a bare pointer) |
| d02 | new row C32 "=> **F10**" attaching an invented claim about Eq. (11.46) to F10 (FB22 read only the arrows →, -> and ⇒) | candidates pointer by another arrow | yes | **ACCEPTED** | CAUGHT (FB22: any mention of F<k>) |
| d03 | a note in F4 shaped as the generated Correct line, marks spelled with Latin look-alikes U+0261 ɡ, U+1D0F ᴏ (FB20 allowed every Latin letter; the fold mapped only Greek/Cyrillic) | look-alike letters | yes | **ACCEPTED** | CAUGHT (FB20 Latin rule) |
| d04 | link reference definitions at the end of the candidates section turned the certified tags `[✓F4_values(…)]` inside generated blocks into links with hover titles "Proved in Lean for every scale factor and every curvature constant K" | rendering outside FB21's region | yes | **ACCEPTED** | CAUGHT (FB21: no reference definition; no link in the generated part) |
| d05 | a setext h2 "Verified findings (continued)" and a 3-space-indented ATX h3 "F15 — …" in the candidates section rendered a second verified section claiming C30 is Checked | rendering outside FB21's region | yes | **ACCEPTED** | CAUGHT (FB21: every rendered heading in the whole file) |
| d06 | registry phrase "flat LCDM models with the matter density not fixed" through an author-forged brief → reading → copy, printed into F1/F3 Correct lines | forged blind route (known) | yes, known class | ACCEPTED | ACCEPTED (documented residue) |

**False acceptance (blind):** 6/6 valid defects accepted by every check (5 of new shapes, 1 known forged route). **After the repairs:** the 5 new shapes caught (each by the rule aimed at it, checked by applying the defect and running FB14/FB20–FB22 directly); d06 passes.

**LEDGER experiment of run 1628Z ("line rules are a model of the renderer; the next blind round finds a valid defect only through rendering if CI does not render"): partly confirmed, partly refuted.** Rendering in CI closed every shape of round AP and the red team found no differential between the line model and the rendered structure of the verified section; but two of its five new defects were still rendering defects — constructs elsewhere in the file (reference definitions, headings) that change what the verified section or the page shows. A render check must whitelist the whole rendered document, not one region's structure. The other three went through text a reader may take as checked that no rule bound (candidates cells, Latin look-alikes).

What changed in kind: AN through the frame, AO through generator inputs, AP through the renderer's view of the notes, AQ through the rest of the rendered page and the candidates section. Still open: GitHub's renderer (cmark-gfm with footnotes, alerts, autolinks, math, emoji) is not markdown-it-py; grandfathered candidates lines are free text; the forged route (d06).
