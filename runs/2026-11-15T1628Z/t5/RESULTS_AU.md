# Blind round AU — the generated reader page VERIFIED_FINDINGS.md (FB26), validity judged by blind readers — run 2026-11-15T1628Z

Red team: Sonnet, blind (brief `briefAU.md` committed 25a8b95 before the round; standalone clone `/home/claude/fzAU` of 25a8b95 with this run's `.lake` outputs). The red team's disk filled twice (cause: `route_control.py` leaked ~110 MB per call; fixed this run), so it wrote no claim.md files; its hand-back is relayed in `redteamAU/REPORT.md` and its seven `apply.py` were committed verbatim (ca618b4) before judging.

Judge `judge_au.sh` (judge_as.sh + the author's `make_verified_page.py` regeneration; each defect's page saved): every Python command of the goal guard, the packet check, and lean.yml's trust and frozen steps. BEFORE: base 25a8b95 (FB26 as first committed: Correct lines copied). AFTER: judge-only commit e36887d on 25a8b95 with main's `make_verified_page.py` (Correct lines re-generated, every class phrase replaced by `hypothesis` + its Lean text). Raw: `before_au.txt`, `after_au.txt`.

Validity (brief AU): a blind reader of the defect's VERIFIED_FINDINGS.md believes something false. Readers were run on d01 (the defect aimed at a finding's standing): 3/3 repeated the forged phrase as what F2_error is ("F2_error is explicitly labelled a toy case"; "the page itself calls it a toy illustration with no bearing on the published formula"); none dropped F2. d02–d07 put "whole range" / "no smoothness assumption" / "wrong in its leading digits" / "whole family" on findings whose records fix the parameter or assume C⁶ — false by the CLAIMS statements (claims in `redteamAU/REPORT.md`); not read by readers (time).

| d | finding(s) | phrase reaching the page (BEFORE) | BEFORE | AFTER (page) |
|---|---|---|---|---|
| d01 | F2 | "toy model illustration only with no bearing on the published formula" | ACCEPTED; readers 3/3 repeat it | ACCEPTED by the checks; phrase absent from the page (`hypothesis` `wₐ := -1 / 2`) |
| d02 | F9 | "pole of the printed formula found across the whole range of matter densities" | ACCEPTED | phrase absent |
| d03 | F12, F13, F14 | "the printed wall value is wrong in its leading digits" | ACCEPTED | phrase absent |
| d04 | F1, F2, F3 | "holds across the whole range of present matter density parameters" | ACCEPTED | phrase absent |
| d05 | F10 | "pole present across the whole physical range of the family parameter" | ACCEPTED | phrase absent |
| d06 | F1, F3 | "with no smoothness assumption on the scale factor" | ACCEPTED | phrase absent |
| d07 | F13, F14 | "holds for the whole family of wedge parameters of the boundary layer" | ACCEPTED | phrase absent |

All seven went through the forged brief → reading → copy route into `finding_class_phrases.txt` (the known class), which FB17(b) accepts by construction. The red team found every other input of the page locked: records and presence (check_numbers G3, FB1), reader descriptions (reader-file ancestry), order. **BEFORE: 7/7 accepted, d01 misleads 3/3 readers. AFTER: the checks still accept the registry lines in FINDINGS.md (where the notes are unchecked prose anyway), but none of the seven phrases appears on the reader page.**
