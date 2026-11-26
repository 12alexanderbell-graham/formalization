# Brief: target 3, AlphaEvolve's rank-48 algorithm for 4×4 complex matrix multiplication (blind reading)

You are a blind reader for a formal-verification audit. Read only this brief. No web, no other files, no git.

Source claim (Google DeepMind, AlphaEvolve, 2025; their results notebook titles the item "Rank-48
decomposition of <4,4,4> over 0.5*C"): AlphaEvolve found an algorithm that multiplies two 4×4
complex-valued matrices using 48 scalar multiplications, improving on the 49 obtained by applying
Strassen's algorithm recursively. In the notebook's terms: a decomposition of rank 48 of the matrix
multiplication tensor <4,4,4>, i.e. three factor matrices with 48 columns each, whose entries lie in
0.5·ℤ[i] (complex numbers whose real and imaginary parts are multiples of 1/2), such that the sum over the
48 columns of the outer products of corresponding columns equals the matrix multiplication tensor.

Task: one Lean 4 file (Mathlib only) at runs/2026-11-26T1529Z/T3/reading.lean stating, with `:= by sorry`:
  theorem reading_algorithm : the claim as an ALGORITHM statement: there exist 48 pairs of complex linear
    forms on 4×4 complex matrices and 48 complex 4×4 coefficient matrices such that for ALL complex 4×4
    matrices A, B the product A * B equals the sum over r of (form_r(A) · form'_r(B)) times the r-th
    coefficient matrix (so exactly 48 multiplications of a quantity depending on A by one depending on B);
  theorem reading_entries : the same, adding that every coefficient used lies in 0.5·ℤ[i].
State each with Mathlib's `Matrix (Fin 4) (Fin 4) ℂ`. Comment on any ambiguity (bilinear vs general
algorithms, commutativity, the field) in a block at the end.
