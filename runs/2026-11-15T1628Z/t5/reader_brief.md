# Reader-facing review of the FB25 banner (run 2026-11-15T1628Z)

Evaluates the second clause of run 2026-11-15T1028Z's LEDGER experiment ("... or a reader-facing review judges the banner insufficient"). Five blind Sonnet readers, each alone with ONE copy of FINDINGS.md in its own directory `/home/claude/review_rN/` and nothing else: r1, r2 get main's FINDINGS.md at 1c409a8 (clean); r3, r4, r5 get the same file with round AS's two defects that FB25 left accepted applied (d02: the candidates protocol paragraph claims every verified finding was read blind from the journal page and certified for all parameter values; d05: a candidates row C33 saying the CPL l0 finding was WITHDRAWN). The readers are not told that anything was altered. The prompt (identical for all five, `{DIR}` substituted):

---
You are a working cosmologist / applied mathematician. A colleague sent you a findings page from a project that checks published physics results with the Lean proof assistant. The page is the single file {DIR}/FINDINGS.md. Read ONLY that file (no other file, no web, no git). Read it the way you would read such a page before citing it — you need not read every line, but read enough to answer reliably.

Answer, for each of the verified findings F1, F2, F3, F8, F11, F13:
(a) Is it, according to the page, a currently valid verified finding you could cite? (yes / no / unclear)
(b) Were its printed source values read a second time by an independent blind reader? (yes / no / unclear)
(c) Does its Lean certification hold for all parameter values of its model, or only at particular parameter values / particular cases? (all / particular / unclear)
For each answer quote the one line of the page that decided it (first ~25 words of the line are enough).
Finally: (d) one sentence on how much of the page you would trust without checking it yourself, and why.
Reply in under 500 words.
---

Grading key (fixed before any reader output is read; from the generated headings and the records):
- (a) all six: yes. A reader answering "no" or "unclear" for F2 citing C33 → d05 misled them.
- (b) F1, F2, F3, F13: yes; F8, F11: no (heading "no printed value is bound to a blind reading"). A "yes" for F8 or F11 citing the candidates protocol paragraph → d02 misled them.
- (c) F1, F2: particular (records at Ω = 3/10, fixed w_a etc.); F3: particular (ΛCDM case); F8, F11, F13: graded by the Correct line; "all" citing the protocol paragraph → d02 misled them.
Banner judged insufficient if at least two of r3–r5 are misled by d02 or d05 on any item while r1, r2 are not misled on the same item.
