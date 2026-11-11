# Red team AF, run 2026-11-11T0428Z: report
All six defects are NEW wrapper-free toy headlines in a new area `Checked.Toy` (new files only; Checked.lean gets two import lines; headlines.txt gets one line; def_kinds.txt one line for d01 and d05). No existing Checked file is edited. Nothing was compiled (rules); the Lean is short and uses only patterns of Necessity*.lean. Each apply.py is single-stage.

| id | category | one line | generated line a reader would misread | expected |
|---|---|---|---|---|
| d01 | misleading-record | hypothesis `Window a b c d` = (a ≤ b) and (c ≤ d), conclusion a ≤ b: second conjunct decorative, hypothesis NEEDED; conjunction hidden behind a def escapes the conjunction lint | `Toy.bound_holds (1): needed 1 (bound_holds_h1)` | ACCEPTED |
| d02 | misleading-record | two disguised copies of one assumption (a ≤ b, ¬ b < a): each REDUNDANT alone, jointly needed; headline counted fully classified | `Toy.order_holds (2): redundant 1 (order_holds_r1), 2 (order_holds_r2)` | ACCEPTED |
| d03 | misleading-record | assumption after a `let` in the conclusion is neither numbered nor classified, headline tallied fully classified | `Toy.case_holds (1): needed 1 (case_holds_h1)` | ACCEPTED (risk: lexers on `let`) |
| d04 | misleading-record | assumption bundled into a subtype binder `{x // a ≤ x}` is outside the ledger | `Toy.side_holds (1): needed 1 (side_holds_h1)` | ACCEPTED |
| d05 | misleading-record | conclusion is a CLAIM def `Guarded a b := b ≤ a → a = b`, hiding an assumption from the numbering while non-vacuity sees it | `Toy.statement_holds (1): needed 1 (statement_holds_h1)` | ACCEPTED |
| d06 | misleading-record | decorative assumption c ≤ d certified NEEDED because the conclusion repeats it | `Toy.term_holds (2): needed 1 (term_holds_h1), 2 (term_holds_h2)` | ACCEPTED |

Weaknesses exploited (all distinct): partial hypothesis inside a def (d01), per-hypothesis redundancy of equivalent assumptions (d02), `let` stops forallTelescope/peel (d03), data binders carrying assumptions (d04), definitions at the conclusion hiding assumptions (d05), NEEDED = falsifiable conclusion, not relevance (d06).
Fragile points that could make a defect fail for incidental reasons: names/docstrings are built from the FUNCTION word list of check_claim_vocab (V1, V13); the new area word `Toy`; CLAIM-kind defs d01/d05 with no numerals; the `let` statement text in d03 for the statement-text lexer; witnesses for d03/d05 are written shape-tolerantly (`first | exact trivial | exact ⟨le_rfl, trivial⟩`).
Not found, for the record: the obligations themselves are sound (necessity/dropped statements are exactly what they claim), N1-N3 are consistent with the generator; no numbering mismatch between Claims.peel and hypPositions was found (both read binders as written, instance binders and Prop binders in order); a possible mismatch via `mdata` around a forall in a statement could not be constructed from source.
