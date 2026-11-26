# Brief: target 0, Chandrasekaran, "An algebraic quantization of gravity from the null cone" (arXiv 2611.34924)

You are a blind reader for a formal-verification audit. You have not seen any formalization of this
paper. Read ONLY the typeset PDF at /tmp/claude-0/-home-claude-formalization/32a3656a-fe82-5bab-a882-acf48c963df6/scratchpad/ext/t0/paper.pdf (arXiv 2611.34924v1 as served 2026-11-26, sha256 d17caccbee57cfbee6fc2eeed2e5a53467c9401be979fd2952aa2bf92d5443af; not committed: arXiv licence), pages 27
(Section 4.2, the Gaussian wavefunction (4.7) and the ladder operators) and 33–35 (Section 4.4,
"Finiteness of transition amplitudes", Eqs. (4.32)–(4.34), the text and footnote around them).
Do not open any other file, do not search the web, do not run git.

Task. Write ONE Lean 4 file (Mathlib only) at runs/2026-11-26T1529Z/T0/reading.lean containing:
1. Definitions you need, each with a doc comment quoting the sentence of the paper it encodes:
   the variance (Δq_k)^2 as a function of s and k, the phase per mode, the dilogarithm Li_2 (Mathlib
   has none: define Li_2(z) for |z| ≤ 1 as the series Σ_{k≥1} z^k/k^2), and the relation between s, the
   corner area 𝒜, G_N and ħ.
2. `theorem single_mode`: the per-mode connected correlator that the paper's first equality in (4.33)
   asserts (the value of the connected expectation for j = k and its vanishing for j ≠ k), stated on a
   concrete model of one harmonic-oscillator mode that you define from (4.7) and the ladder operators
   (e.g. operators on the span of the first few occupation-number states, or on coefficient vectors).
   Say exactly which Gaussian centres and widths you use, as the paper does.
3. `theorem eq_4_33`: the series identity of (4.33), including that the series converges absolutely,
   for every s > 0.
4. `theorem eq_4_34`: the G_N^3 coefficient of (4.34) at finite N (with s written through G_N), as an
   exact identity, and `theorem harmonic_log`: the log N + O(1) statement.
5. `theorem finite_term`: the paper's sentence that summing before expanding "converts the log N
   divergence ... into the finite term −i log s/s^3 in (4.33)", stated as precisely as the text allows
   (e.g. an asymptotic statement as s → ∞ about the imaginary part of the right side of (4.33)).
All theorems `:= by sorry`. The file must typecheck (check with the command given to you).

Then, in a comment block at the end: (i) every place the text was ambiguous and your choice; (ii) a
list of every assumption on which the word "finite" in this section depends (fixed area, one
polarization, one angular harmonic, the Gaussian state and its centres, the chosen phase, any cutoff
N, the order of limits, ...), each with the sentence of the paper that introduces it.
