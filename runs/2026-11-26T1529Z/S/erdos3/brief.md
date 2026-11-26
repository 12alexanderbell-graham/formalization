# Brief: Erdős Problem 3 / reciprocal-sum conjecture (read BRIEF_COMMON.md first)

Post-verdict part-3 test (run 2026-11-26T1529Z): this family was added after the S1-S3 verdicts were
committed and after a human survey was read; the reader below is blind, the auditor is not (recorded).

Source 1, the Erdős problem (erdosproblems.com 3, statement as commonly given): "If A ⊆ ℕ has
Σ_{n∈A} 1/n = ∞ then must A contain arbitrarily long arithmetic progressions?"

Source 2, manuscript "Quasipolynomial Bounds for Arithmetic Progressions" (OpenAI, 2026-09-23), verbatim:
Abstract: "We prove Erdős's conjecture that every set of positive integers with divergent reciprocal sum
contains arithmetic progressions of every finite length. More quantitatively, for every fixed k≥3, we show
r_k(N)\le C_kN\exp(-c_k(\log N)^{\varepsilon_k}) with C_k,c_k,\varepsilon_k>0, where r_k(N) is the largest
size of a subset of {1,…,N} with no nonconstant k-term arithmetic progression."
"Theorem 1.1. For each fixed integer k≥3 there are constants C_k,c_k,ε_k>0 such that, for every N≥2,
r_k(N)\le C_kN\exp(-c_k(\log N)^{\varepsilon_k})."

Write `reading` for Theorem 1.1 and `reading_erdos` for the reciprocal-sum statement.
Write your file to: runs/2026-11-26T1529Z/S/erdos3/reading.lean
