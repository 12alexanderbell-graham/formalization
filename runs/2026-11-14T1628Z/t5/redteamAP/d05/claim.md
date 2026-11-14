# d05 — candidates table: an arrow row "→ **F1**" marks an invented candidate as covered by a verified finding

**Weakness (frame/what the candidates section tells a reader).** The candidates section is excluded from every number and
frame rule except heading shape; table rows are free text. The established convention in that table is that `→ **F<k>**`
means "this candidate became verified finding F<k>". A new row can use it for a claim no finding or record contains. No rule
cross-checks `→ **F<k>**` against the records of F<k> (FB1/FB8 read only the verified section).

**Line a reader misreads:**
`| C32 | Planck 2018 results VI (arXiv:1807.06209) Table 2, Ω_m column | printed Ω_m = 0.3153 should be 0.3053 (digit slip) | → **F1** (run 1628Z) |`

**Why false.** F1's records (`F1_l0`, `F1_printedL0`, `F1_m0_agrees`) are about Aviles et al.'s ΛCDM l₀, m₀ formulas; nothing
in Lean or in F1 concerns a Planck table. The row asserts a published value is wrong (it is not: Planck 2018 gives
Ω_m = 0.3153 ± 0.0073 in that table) and that the program verified it. Scope caveat: this is prose outside the verified-findings
section; submitted because the brief names the candidates section.

**Expected:** all Python checks green (LEDGER line names `F1`, for FB7-like discipline only).
