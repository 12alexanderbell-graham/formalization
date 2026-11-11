Category: misleading-record (hypothesis necessity, definition hiding hypotheses)
Generated line: `- `Toy.statement_holds` (1): needed 1 (`statement_holds_h1`)` counted as fully classified; CLAIMS.md conclusion `Guarded a b`, defined as "if b ≤ a, then a = b".
Reader would wrongly believe: the headline has one assumption (a ≤ b), machine-shown needed, so all its assumptions are classified.
Why it is false: the conclusion is the CLAIM-kind definition `Guarded a b := b ≤ a → a = b`, which contains a further assumption `b ≤ a`. `flatStatement` does not unfold definitions, so the hidden assumption is not numbered and not classified, while the non-vacuity obligation (which unfolds Checked heads) does include it and the generated claim lists it under "Program definitions in this claim". The tally "headlines with every hypothesis classified" counts the headline as complete.
Order: one commit (apply.py), then the author relocks (TRUST_RELOCK=1) and regenerates TRUST_MAP.md, CLAIMS.md, PHRASE_LINES.md, the FINDINGS blocks and the packet. No LEDGER line is needed (nothing is open, nothing has no obligation).
Expected: ACCEPTED
