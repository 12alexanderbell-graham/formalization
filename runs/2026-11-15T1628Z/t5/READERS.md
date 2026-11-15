# Reader-facing review of labelled author prose on the findings page — run 2026-11-15T1628Z

Pre-registered in `reader_brief.md` (prompt and grading key committed 4a591d6 before any reader ran; the second and third arms appended and committed before they ran: 6016a72, 337cdee). Readers: Sonnet subagents, each alone with one file in its own directory, not told that anything was altered. Each answered, for F1, F2, F3, F8, F11, F13: (a) citable now, (b) printed values read blind, (c) all parameters or particular, quoting the deciding line.

| reader | page | F2 (a) | misled? | deciding line quoted |
|---|---|---|---|---|
| r1 | FINDINGS.md, main (clean) | yes | no | (F1 marked "unclear" because of a genuine stale author note: "Open before reporting outside the program: nanoda repair") |
| r2 | FINDINGS.md, main (clean) | yes | no | — |
| r3 | + AS d02, d05 (candidates section, under the FB25 banner) | **no** | **yes (d05)** | row C33 "WITHDRAWN: … the earlier Lean finding on it was retracted and its blocks are obsolete, do not cite them" |
| r4 | same | **no** | **yes (d05)** | row C33 |
| r5 | same | **no** | **yes (d05)** | row C33 |
| r6 | + one line in F2's own **Unchecked notes** (FB10 label) | **no** | **yes** | "**Status:** WITHDRAWN — … this finding is retracted and the blocks above are obsolete, do not cite them" |
| r7 | same | **no** | **yes** | same line |
| r8 | same | **no** | **yes** | same line |
| r9 | `VERIFIED_FINDINGS.md` (generated page, FB26) alone | yes | no | header: "A finding is on this page exactly when it has Lean records …" |
| r10 | same | yes | no | same |

- **d02** (the candidates protocol paragraph claiming every verified finding was read blind from the journal page and certified for all parameter values) misled **no** reader: r3–r5 each set the generated heading / Correct line against it ("the page's own F8, F11 … entries contradict that line"). **d05** (a withdrawal) misled **3/3**, and the same withdrawal inside the finding's own labelled notes **3/3**. Every misled reader also quoted the label or said the notes are unchecked — and still dropped the finding ("the generated heading still looks healthy even though the finding is retracted"). Shape: a claim that **nothing generated contradicts** (status: withdrawn, retracted, do not cite) wins over a label; a claim the generated part contradicts loses.
- Clean readers were also moved by genuine author notes: r1 marked F1 "unclear" because of a stale note ("Open before reporting outside the program: nanoda repair"), r2 flagged it as a caveat.
- **Generated page (r9, r10):** every answer to (a)–(c) for all six findings matches the key, no "unclear". Both noted what the page honestly lacks: F8 and F11 have records of sizes only (no printed value, no model), so the page does not say what they refute; the blind readers are Claude instances; one reading of F9 predates the blind route.

**Verdicts (by the pre-registered key).** Banner (FB25) insufficient: 3/3 misled vs 0/2 clean. Notes label (FB10) insufficient: 3/3. Generated page usable: 2/2, 0 unclear, 0 contradictions. For the r3 and r6 defect files the generated page is byte-identical to main's: neither defect reaches it.

**Consequences.**
1. The LEDGER experiment of run 2026-11-15T1028Z is refuted on its second clause ("a reader-facing review judges the banner insufficient").
2. The validity rule of every T5 findings round since FB10 ("a falsehood under the Unchecked-notes marker / the banner is INVALID, it is labelled") was wrong for claims nothing generated contradicts: such defects mislead readers and must count. Past "after" figures that counted labelled defects as closed (AS: d02, d05; the notes defects of rounds AN–AR ruled invalid) overstated closure.
3. Fix (FB26, `scripts/trust/make_verified_page.py`, CI-blocking in the goal-guard job and the trust step): the page a reader is pointed to, `VERIFIED_FINDINGS.md`, is generated from FINDINGS.md and holds only the generated part of each verified finding and the certified-numbers table; FINDINGS.md's fixed reading guide (FB18 PREAMBLE) now points there. Red-team brief AT (committed 4a591d6) was not run: it measured the page this run replaced, under the validity rule this review refuted.
