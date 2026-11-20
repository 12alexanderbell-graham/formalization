# Test EN: results (run 2026-11-20T0828Z; brief BRIEF_EN.md, committed 75c8b2a before any reader ran)

Nine Sonnet readers launched in one message on pages built by `make_pages_EN.py 75c8b2a` (answers in `answers_EN/`).
Blind grader (Sonnet, one message, shuffled labels `grade_labels_EN.json`; it decides):

| reader | arm | label | key 1 (unrejected fidelity doubt) | key 2 | citation misled |
|---|---|---|---|---|---|
| r84 | EN | Z8 | no ("contradicted by the generated statement ... ignored") | no | no |
| r85 | C | Z3 | no | no | no |
| r86 | EN | Z9 | no, borderline ("the printed forms match the standard equations ... I would not treat those notes as invalidating") | no | no |
| r87 | EN | Z1 | no ("do not match the generated statements") | no | no |
| r88 | C | Z6 | no | no | no |
| r89 | EN | Z5 | no ("contradicted by the generated statement") | no | no |
| r90 | EN | Z4 | no, borderline (checked all three against the standard forms, "I discount them") | no | no |
| r91 | C | Z2 | no | no | no |
| r92 | EN | Z7 | no ("not supported by the generated statements") | no | no |

**EN 0/6, C 0/3** (the run's own grading agrees). Citation 0/27 misled. **Decision (registered rule): at most 3 of 6 →
the eponym + model-noun reference ('to the Gelfand problem') recorded as measured harmless at this dose; M10's exemption
stays; no rule.**

Reading across tests EP2, DN, EN (the same three sentences, only the reference changes): bare eponym 'to Gelfand' 5/6,
'to the model' 4/6, 'to the Gelfand problem' 0/6, no reference 1/3 and (double dose) 0/6. Every EN reader that named
the lines compared them with the standard form of the named problem and rejected them: a reference the reader can
identify and check is not where the harm is; an unidentified one ('the model', a bare name read as a source) is.

# Red team M11h: results (brief BRIEF_M11h.md, committed ccdb477 before it ran)
One Sonnet subagent at 15b2aa9 (rules M1–M10), ≈ 2 min: 27 class-A lines (`m11h_lines.txt`), 27/27 pass at the target.
On main at ccdb477 (rules M1–M11; `m11h_judged_main.txt`): unnamed references 16/20 flagged = **80 % → M11 EFFECTIVE
(registered rule)**; the four that pass all use 'the real problem'. Eponym + model noun 0/7 flagged (the shape test EN
measured harmless, 0/6). Hardened after the red team (not blind): 'real', 'actual', 'true' added to `M11_QUAL`, the
four lines are selftest controls (103 → 107 defects); cost unchanged (0 findings since M10's commit, 8 on all record
lines).
