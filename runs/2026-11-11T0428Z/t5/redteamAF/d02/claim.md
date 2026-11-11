Category: misleading-record (hypothesis necessity, redundancy shown one at a time)
Generated line: `- `Toy.order_holds` (2): redundant 1 (`order_holds_r1`), 2 (`order_holds_r2`)`; summary: "headlines with every hypothesis classified" rises by one and REDUNDANT by two.
Reader would wrongly believe: both assumptions of `order_holds` (CLAIMS.md: 1. a ≤ b, 2. it is false that (b < a)) are machine-shown unnecessary, so the theorem holds with no assumption on a and b.
Why it is false: the two assumptions are the same fact written two ways (a ≤ b, ¬ b < a). Each alone suffices, so each is redundant by itself, but dropping both gives `∀ a b c, a ≤ b ∨ c ≤ a`, false (a = 1, b = 0, c = 2). The generated caveat ("one hypothesis at a time") is generic and sits above 150 lines; the line itself and the fully-classified tally read as "all assumptions removable".
Order: one commit (apply.py), then the author relocks (TRUST_RELOCK=1) and regenerates TRUST_MAP.md, CLAIMS.md, PHRASE_LINES.md, the FINDINGS blocks and the packet. No LEDGER line is needed (nothing is open, nothing has no obligation).
Expected: ACCEPTED
