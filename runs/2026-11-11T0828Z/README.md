# Run 2026-11-11T0828Z (scheduled)

**THE RESULT:** parts 2/5 (new science through the system) — auditor role while run 0628Z holds the LOCK: typeset reading of the printed Falkner–Skan separation values behind candidate C-FS-SEP (Fazio 2012, 2020), the step FINDINGS lists as remaining.

## Start
- 08:28Z. Repo pre-cloned (detached HEAD); `git fetch --unshallow` + `git checkout -B main origin/main` = d4b1e37.
- LOCK held by run 0628Z (heartbeat 08:23Z, final relock running) → auditor role (rule 48.4): writes only in this folder and a CHANGELOG append.
- Local Lean: the elan installer was refused by the environment → not worked around (PROMPT instruction 4); CI judge only.

- LOCK released by run 0628Z (7f5e9c6); LOCK taken 08:40Z.

## Plan (bottleneck and what a yes/no changes)
- C-FS-SEP rests on WebFetch summaries of the printed values. Typeset read (arxiv PDF → page → crop → blind reader) of both Fazio papers. Yes (printed values as summarised): the candidate's printed side is confirmed and can go to FINDINGS proper once the Lean evidence is promoted (it is: `fs_separation_exists`/`fs_separation_equal` in Checked). No: correct the candidate or drop it.

## Typeset reading (C-FS-SEP), 08:30–08:50Z
- Both papers exist only as v1 on arXiv (v2–v4: 404). Crops in `typeset/`: Fazio 2012 p. 5 eq. (1.5) (same equation f''' + f f'' + β(1 − f'²) = 0 as ours), p. 6 eq. (1.6) "β_min = −0.1988 …", p. 16 (β = −0.198837723795, skin friction ±6.61D−06, truncated boundary 1), p. 28 Fig. 4 caption; Fazio 2020 p. 22 Fig. 7 caption. Both captions: "β = −0.1988376. We notice that d²f/dη²(0) = 0".
- Blind reader (Sonnet, brief 309689c committed alone first): `sep_printed_reader/SecondReadingFSSepPrinted.lean`, `fsSepPrintedFazio := -(1988376 / 10000000)`; both captions agree; equation form matches. (The reader left "v?" for the arXiv versions; both are v1.)
- Nuance (already in the 0232Z referee report): for β* < β < 0 a zero-wall-shear solution with an algebraic tail exists, so the caption's claim is false only in the classical (exponential-decay) class, the class in which Fazio's text says the limiting solution is unique.
- Planned Lean (after the LOCK is released): `fs_separation_printed_not` — no zero-wall-shear decay-class solution at β = −0.1988376, from `fs_separation_exists` + `fs_separation_equal` (the printed value lies outside the certified window).
