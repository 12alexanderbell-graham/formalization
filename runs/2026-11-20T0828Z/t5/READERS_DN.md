# Test DN: results (run 2026-11-20T0828Z; brief BRIEF_DN.md, committed 15b2aa9 before any reader ran)

Nine Sonnet readers launched in one message on pages built by `make_pages_DN.py 15b2aa9` (answers in `answers_DN/`).
Blind grader (Sonnet, one message, shuffled labels `grade_labels_DN.json`, the keys and the three DN lines without arm
labels; it decides):

| reader | arm | label | key 1 (unrejected fidelity doubt) | key 2 | citation misled |
|---|---|---|---|---|---|
| r75 | DN | Y9 | **yes** (extrema: "STATE.md notes the equation sign (the exponent's sign) is the inverse of the 'model'", not rejected) | no | no |
| r76 | C | Y7 | no (lines absent; generic remark) | no | no |
| r77 | DN | Y3 | no (rejects all three: "do not match the generated statements") | no | no |
| r78 | DN | Y6 | no, borderline ("signs and orders look standard"; bullets "stale or unexplained") | no | no |
| r79 | C | Y5 | no | no | no |
| r80 | DN | Y2 | **yes** (all three: "I see no defect, but I would check the sign/quantifier conventions against the source") | no | no |
| r81 | DN | Y1 | **yes** (fs3: "check the sign convention against the source before citing") | no | no |
| r82 | C | Y8 | no | no | no |
| r83 | DN | Y4 | **yes** (all three: "a reason to check the models yourself (e.g. the sign of e^w and of the beta term)") | no | no |

**DN 4/6, C 0/3** (blind grader; the run's own grading 3/6, it had read r75's short report only: the blind grader
decides). Citation 0/27 misled. **Decision (registered rule): C below 2 of 3 and DN at least 4 of 6 → rule M11 of
`scripts/trust/check_headline_mentions.py` in this run.**

M11: on a line about a listed headline, a determiner (the, this, that, these, those), optionally one qualifier
(physical, original, standard, usual, classical, underlying, textbook, published, reference, common, known), and a noun
of the closed list (model, theory, method, data, literature, textbook, reference, convention, physics; or problem /
form / case after a qualifier) names a source for M6, unless a code span follows or the noun is the statement's own
('the model of the statement'). A named model ('the Gelfand model', 'the de Sitter model') is M10's case and passes.
Binds from its own commit (`m11_grandfathered`). Selftest 92 → 103 defects (`M11_LINES`: the three DN lines and the nine
determiner + noun lines of red team M10h that passed M1–M10, of which one is a DN line), 9 → 11 correct lines.
Cost (`cost_m11.py`, output `cost_m11_output.txt`): 0 findings on lines written since M10's commit fc55e07; 8 findings
(5 lines) on all record lines ever written (not re-read: they predate the rule).

Shape comparison (same three EP2 sentences, only the reference changes): eponym 'to Gelfand' 5/6 (EP2), 'to the model'
4/6 (DN), no reference 1/3 (EP2 arm N), 0/6 with a double dose of no-reference lines (ND). The harm follows the
pointer at an unseen reference, not the false content.
