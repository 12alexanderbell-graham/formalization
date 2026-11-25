# d03 — a source name taken from a word of the reader's sources clause ("Taylor") backs a Lane-Emden headline (`laneEmden32_constants`)

Weakness: rule 1 (c) of `check_literals.py` accepts a `source=` name if it occurs as a whole word anywhere in the reader's sources clause (`sources_clause`/`clause_ok`) and in some brief (`source_ok`);
it does not ask that the word be a source. The clause of the genuine reader file behind `le32Rhs` (runs/2026-11-19T1028Z/le32_reader) reads
"own derivation of θ'' + (2/ξ)θ' + θ^(3/2) = 0, mpmath power-series start at ξ = 0.1 with Taylor odefun at 40 and 55 digits, no external sources": the word `Taylor` is the Taylor method of the integrator and the clause says "no external sources".
Edit: one new line of literal_readings.txt `laneEmden32_constants source=Taylor Checked.Trust.SecondReading.le32Rhs` and one LEDGER line naming `laneEmden32_constants`. Allowed, no .lean.

Line misread (entry `laneEmden32_constants`, Status): "... statement literals: N definitions written by a blind second reader of the source are registered ... (source names backed by the readers: Taylor) ..." (was: no source names).

False belief: a scientist reads that a source by an author named Taylor backs the reading of the Lane-Emden n = 3/2 constants, i.e. that the blind reader consulted a published source, when the reader explicitly used none
(own mpmath integration; `no external sources`). Expected: green. (Weakest of the set: the misreading is a spurious named source rather than a wrong number.)
