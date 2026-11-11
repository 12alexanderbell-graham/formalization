Category: misleading-record (hypothesis necessity, assumption carried by a data binder)
Generated line: `- `Toy.side_holds` (1): needed 1 (`side_holds_h1`)` counted as fully classified; CLAIMS.md: "For every `a : ℝ`, `c : ℝ`, `b : {x // a ≤ x}` assuming 1. c ≤ a then c ≤ ↑b".
Reader would wrongly believe: the only assumption is `c ≤ a` and the machine has shown it needed; nothing else is assumed.
Why it is false: the binder `b : {x : ℝ // a ≤ x}` is a subtype: the assumption `a ≤ b` is bundled into the data type, so it is not a Prop binder, is not numbered and is never classified (the conclusion `c ≤ b` needs it as much as hypothesis 1). Any assumption can be moved into a subtype binder to remove it from the necessity ledger while the headline still counts as fully classified. unusedHyps accepts it because `b.2` uses the binder.
Order: one commit (apply.py), then the author relocks (TRUST_RELOCK=1) and regenerates TRUST_MAP.md, CLAIMS.md, PHRASE_LINES.md, the FINDINGS blocks and the packet. No LEDGER line is needed (nothing is open, nothing has no obligation).
Expected: ACCEPTED
