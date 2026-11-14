# Blind round AN — findings layer against FB10–FB13 (run 2026-11-14T0028Z)

Red team: Sonnet, blind (brief `briefAN.md` committed in the snapshot 9d8d3c9 before the round; standalone read-only clone; no access to the working tree or the excluded run folders). Output `redteamAN/` committed verbatim (04043b4) before judging. Judge `judge_an.sh` (copy of round AM's): every Python command of lean.yml's trust and frozen steps, after the author's regeneration (`check_numbers.py --write`, `make_packet.py`), BASE = the tree's own commit.

- BEFORE: snapshot 9d8d3c9, `.lake` files of the author-files artifact of c5c2a35 (stale): the clean tree fails goal_guard (stub README) and check_literals (stale meaning.jsonl) — a defect counts as caught only by another check. Raw: `before_an_judge.txt`.
- AFTER: 136a38f (FB14, FB15), `.lake` files of this run's StatementDeps (fresh): the clean tree fails only goal_guard (stub README). Raw: `after_an_judge.txt`. Not blind (the repairs were written after reading the defects).

| d | defect | BEFORE (9d8d3c9, blind) | AFTER (136a38f, not blind) |
|---|---|---|---|
| d01 | look-alike `## Verified findings index` before the section: every rule read an empty section; F3's heading and Printed line forged to show a reader description of `printedD4` | CAUGHT by CI only through check_prose (citations.txt grew without a LEDGER line naming `11.39`: the red team's disclosure slip, unrelated to the attack); **findings rules: ACCEPTED** | CAUGHT (FB13/FB10 on F3: the section is found again; FB14 frame) |
| d02 | new registry phrase `ContDiffAt ℝ 5 a t₀ => every matter density Ω, every w₀ and wₐ`; F2's generated Correct line carries it | **ACCEPTED** | CAUGHT (FB15) |
| d03 | F2's record header indented in F3's notes; heading/Printed/Correct regenerated with another finding's record and printed value | **ACCEPTED** | CAUGHT (FB14; generators ignore it) |
| d04 | `## Verified findings (continued)` after the section, with a finding F15 in generated form | **ACCEPTED** | CAUGHT (FB14 frame and heading) |
| d05 | `  ### F15 — generated heading …` and generated-looking bullets indented in F14's notes (render as a heading and list) | **ACCEPTED** | CAUGHT (FB14 notes rule and generated marks) |
| d06 | F12's record header indented in F8's notes (as d03) | **ACCEPTED** | CAUGHT (FB14) |

**False acceptance (blind):** findings rules 6/6; every CI check 5/6. **After the repairs:** 0/6 (not blind).

What changed in kind: no defect edited a generated line or forged a generator's output under its own rule — every one went through the frame (where the generated part is located, what the generators read, what free text may render as) or an author-maintained input of a generator (the registry). PROMPT note "When the content is generated, the attack moves to the frame around it".

Open: a blind round against FB14/FB15; the three pre-route readings without a reader file (F3, F9, F10); records for F4–F7.
