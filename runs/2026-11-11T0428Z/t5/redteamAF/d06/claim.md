Category: misleading-record (hypothesis necessity, NEEDED but decorative)
Generated line: `- `Toy.term_holds` (2): needed 1 (`term_holds_h1`), 2 (`term_holds_h2`)`; CLAIMS.md: assuming 1. a ≤ b, 2. c ≤ d; then 1. (a ≤ b) or (c ≤ a), 2. c ≤ d.
Reader would wrongly believe: both assumptions carry weight for the headline's result, i.e. assumption 2 (c ≤ d) cannot be dropped from the main claim.
Why it is false: the main claim `(a ≤ b) or (c ≤ a)` follows from assumption 1 alone. Assumption 2 is NEEDED in the machine's sense only because the conclusion repeats it verbatim as a second conjunct (`... ∧ c ≤ d`), so removing it falsifies that echo. Any decorative assumption can be certified NEEDED by appending it to the conclusion; no check compares the conclusion with the hypotheses (T2 level 1 "does not check that the conclusion is not trivially true").
Order: one commit (apply.py), then the author relocks (TRUST_RELOCK=1) and regenerates TRUST_MAP.md, CLAIMS.md, PHRASE_LINES.md, the FINDINGS blocks and the packet. No LEDGER line is needed (nothing is open, nothing has no obligation).
Expected: ACCEPTED
