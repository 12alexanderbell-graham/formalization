# Prior-art screen: the β = −0.1 attached-branch wall shear (run 2026-11-09T1228Z)

Sonnet subagent, brief `brief_screen.md`; its Write tool refused the file, so this is its returned report, transcribed by the main session (summary, its words condensed). Shallow: 3 searches, 6 arXiv PDFs via arxiv.org/pdf (fetch-tool summaries; none blocked).

Read:
- arXiv 1212.5057 (Toepfer's algorithm), Table 4: β = −0.1 **reverse-flow** f''(0): Stewartson −0.141; Asaithambi, Auteri et al., ITM −0.140546 (same normalisation). Two physical solutions for β_min < β < 0. No attached-branch value at β = −0.1.
- arXiv 2003.07971 (iterative transformation method), Table 7: the same reverse-flow −0.140546 only.
- arXiv 1907.09912 (asymptotic approximants): attached branch 0.28176052424 at β = −0.12, 0.469599988361 at β = 0 (its κ at β = 0 is √2 × 0.33206: a different normalisation of η); no β = −0.1 value in the text (a supplementary table, not read). No rigorous bounds.
- arXiv 2508.02677 (h-adaptive FEM): m ≥ 0 only; "rigorous" without enclosures.
- arXiv 0807.0912: no β = −0.1 table, no uniqueness class.
Seen in search results only (not read): 10.1134/S0015462820040072; Quart. Appl. Math. 1979; Mathematika "further solutions … −1 and 0"; arXiv 2303.17781, 2011.07725, math/0601332, math/0603194, math/0601385, 2609.23493. Not accessed: Hartree 1937, Smith 1954, Cebeci–Keller, Rosenhead, Iglisch–Kemnitz, Hartman 1964.

Answers:
1. No printed attached-branch value at β = −0.1 was found in what was read (the classical 5-digit 0.31927 is cited in the run-0428Z research note from memory, not verified here). Novelty of the ten digits: unconfirmed, not refuted.
2. No interval/computer-assisted enclosure of any Falkner–Skan wall shear with β < 0 found; no Lean/Coq/Isabelle formalisation found.
3. Class of the classical β < 0 uniqueness statement: unresolved (primary sources not read).
