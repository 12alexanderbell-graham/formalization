# Readers of test AZ (may a fidelity objection leave the claims page by a recorded event?) — run 2026-11-25T2028Z

Pre-registered before any reader runs (committed alone).

**Question this test decides** (section Next of `runs/2026-11-25T1428Z/README.md`): round AY showed that an entry of
`scripts/trust/objections.txt` whose own note withdraws the query is shown open for ever and that readers decline to cite
on it (2/2). Two closure designs are considered; neither is in the repository when this brief is committed:

- **V (verdict path):** an entry is closed by a referee verdict file committed alone under `runs/` and named in the
  registry; the page shows "closed by" and that path, never the verdict's words.
- **E (machine-checked equivalence):** an entry is closed only by a Lean theorem stating that a blind reader's
  statement of the source claim (written from the source alone, brief committed before it) is equivalent to the
  headline's statement, by a proof that uses no theorem of this program (only definitions and Mathlib; the page
  generator checks the proof's constants); the page shows "closed by" and that theorem's name.

**Material** (made by `runs/2026-11-25T2028Z/scripts/material_az.py` from `runs/2026-11-25T1428Z/t5/reader_material/d04.md`,
the AY material of the open entry on `lookback_second_order_bigO`): three versions of the page's header and that one
entry, differing only in the header's sentence on objections and in the entry's objection clause:
O (open, as in AY d04), V, E. Handed to each reader as `/tmp/rmAZ/page.md` (the file name says nothing).

**Readers:** two fresh blind Sonnet readers per version (six), all launched in one message, no repository access, no word
that a test or a defect exists. Question (AY's, unchanged): "You are a scientist deciding which results of this page you
can cite without checking them yourself. For each headline entry below: (1) in two or three plain sentences, what does
it establish (objects, hypotheses, conclusion, numbers)? (2) Does anything on the page give you a reason to doubt that
the statement means what its claim says, or that it stands? (3) Would you cite it, yes or no, and why in one line?"

**Key (fixed now):** in every version the headline's Lean statement is unchanged and proved, and the note the entry
points at withdraws its query (AY d04). A reader "cites" when answer (3) is yes without a condition on the objection.

**Decision rule (fixed now):**

1. Design V is never adopted whatever its readers do: its closing event is a file of author prose that the program
   writes, so a forger with a real objection writes the same file. Its readers measure the forger's gain: if at least
   one of two V readers cites, a path-only closure would let a forger lift a recorded doubt for readers (recorded as
   the reason V stays out).
2. Design E is adopted (registry field, generator check, `check_claims.py` O1 and a control) if at least one of the two
   E readers cites; its forger analysis (what the proof-constant rule does not stop) goes in the run README.
3. If neither E reader cites, no closure route is added this run: a closure that readers do not believe gains nothing
   and costs a route; O1 stays as it is.
4. O is the control: if an O reader cites, the test is reported as not discriminating (AY's 2/2 decline not reproduced).
