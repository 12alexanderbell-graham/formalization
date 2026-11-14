# Blind round AO — findings layer against FB10–FB15 (run 2026-11-14T1228Z)

Red team: Sonnet, blind (brief `briefAO.md` committed in the snapshot 5536d4b before the round; standalone read-only clone `/home/claude/fzAO` with this run's fresh `.lake` files; no access to the working tree or the excluded run folders; 40 min). Output `redteamAO/` committed verbatim (d8d4b1b) before judging. Judge `judge_ao.sh` (copy of AN's): every Python command of lean.yml's trust and frozen steps after the author's regeneration (`check_numbers.py --write`, `make_packet.py`), BASE = the tree's own commit, on full-history clones (the red team's snapshot was cloned from a shallow checkout; that changes nothing it tested, since no defect forged reader-file history).

- BEFORE: 5536d4b with this run's StatementDeps/Claims `.lake` files (fresh): the clean tree fails only goal_guard (stub README), so a defect counts as caught only by another check. Raw: `before_ao_judge.txt`.
- AFTER: 1084a9f (FB16–FB18, FB15 word list, packet label), same `.lake` files. Raw: `after_ao_judge.txt`; rule names from `check_findings.py --base 1084a9f` per defect. Not blind (the repairs were written after reading the defects).

Validity by the brief: a defect is valid only if a reader of a verified finding, reading as the guide instructs, comes to believe something false; prose outside the verified-findings section is out of scope. d04 (the reading guide above the sections) and d05 (the expert packet) are therefore INVALID by the letter of the brief, but both are real weaknesses and both were repaired.

| d | defect | valid | BEFORE (5536d4b, blind) | AFTER (1084a9f, not blind) |
|---|---|---|---|---|
| d01 | new registry line `Ω := 245 / 1000 => valid whichever matter density is chosen`; F2's generated Correct line prints it for a record that fixes Ω, w₀, wₐ ("whichever" is not in FB15's word list) | yes | **ACCEPTED** (every Python check) | CAUGHT (FB15 widened list; FB17 (b): not copied from a blind reading) |
| d02 | registry phrase that is a Markdown link "[printed value re-read in the typeset PDF and confirmed by an independent blind referee](runs/referee-blind/REPORT.md)" to a forged report; printed raw into F13's generated Correct line | yes | **ACCEPTED** | CAUGHT (FB17 (a) plain text; FB17 (b); FB15) |
| d03 | registry phrase `Filter.Tendsto p Filter.atTop (nhds 1) => attached flow with no reversed region` (one atom, three findings): printed into F14, the reversed-flow existence record | yes | **ACCEPTED** | CAUGHT (FB17 (b)) |
| d04 | the reading guide's layout paragraph reworded: Printed lines "confirmed against the source", Correct "proved in Lean", notes "re-read by an independent referee" | no (outside the section) | ACCEPTED | CAUGHT (FB18 fixed preamble) |
| d05 | F13's author title (an unchecked note) reworded to say Fazio prints the correct value; `make_packet.py` copied it, unlabelled, as packet item 28's **Source** | no (packet) | ACCEPTED | still passes, but the packet now labels the line "Source (hand-written … no check reads it)" — the falsehood sits in labelled author text, as in the notes |
| d06 | one note line of F14 carries a block opener, a record header `F14_reversed_wall_shear_unique` and a "For every" line joined by U+2028; `record_items` (`str.splitlines()`) reads a second block, FB10/FB14/check_numbers (`split("\n")`) see one note; F14's generated heading and Correct line list an invented universal record | yes | **ACCEPTED** by every Python check (Lean-side citation rule of StatementDeps: see below) | CAUGHT (FB16: U+2028 in FINDINGS.md; `record_items` now splits at "\n") |

**False acceptance (blind):** 4/4 valid defects accepted by every Python check of CI (6/6 counting the two out-of-scope ones). **After the repairs:** 5/5 of the detectable ones caught, d05 labelled (not blind).

d06 and the Lean side: StatementDeps (its citation rule reads FINDINGS.md: backticked names must resolve) was run on the d06 tree (5536d4b + d06, this run's build): exit 0 (`sd_d06.txt`) — the stray backticks kept the invented record name out of the citation rule, so d06 passed every check of CI, Lean side included.

What changed in kind: AN's six defects all went through the FRAME (where the generated part is, what may surround it). AO's four valid ones went through the generators' INPUTS — the author-written class-phrase registry (three) and the line splitter (one). No defect touched a Lean record, CLAIMS.md or a reader file. After FB16/FB17 every input of the heading, Printed and Correct lines is generated from Lean or comes through brief → reading → copy; LEDGER records this as an experiment with a refutation condition for the next round.

Open: the reader descriptions printed in Printed lines are reader-file docstrings, route-checked but not plain-text-checked; the three pre-route readings (F3, F9, F10) have no reader file.
