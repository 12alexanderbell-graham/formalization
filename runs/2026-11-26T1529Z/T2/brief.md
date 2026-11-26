# Brief: target 2, "More than two thirds of the zeros of the Riemann zeta function are simple and on the
# critical line" (L. Alpöge, R. Furman; argument discovered and written by Claude; arXiv 2608.13637)

You are a blind reader for a formal-verification audit. You have not seen, and must not look for, any Lean
formalization of this paper. Read only this brief. No web, no other files, no git.

Source (the paper's TeX, verbatim):

Abstract: "We prove unconditionally that at least two thirds of the nontrivial zeros of the Riemann zeta
function, counted with multiplicity, are simple and lie on the critical line, and that at least five sixths
are distinct; the previous unconditional records are 5/12 and 0.6603. With the Montgomery--Taylor window the
constants become 0.6725 and 0.8362. ... The results extend to primitive Dirichlet L-functions ..."

§1.1: "Write ρ=β+iγ for a nontrivial zero of ζ(s) and m_ρ≥1 for its multiplicity. For 0≤T_1<T_2 let
N(T_1,T_2):=Σ_{T_1<γ≤T_2} m_ρ (zeros, counted with multiplicity),
N_d(T_1,T_2):=#{ρ:T_1<γ≤T_2} (distinct zeros),
N_0^*(T_1,T_2):=#{ρ:T_1<γ≤T_2, β=1/2} (distinct zeros on the critical line),
N_0^s(T_1,T_2):=#{ρ:T_1<γ≤T_2, β=1/2, m_ρ=1} (simple zeros on the critical line);
write also N_0 for the zeros on the line counted with multiplicity and N^s for the simple zeros ...
Write N(T):=N(0,T)."

"Theorem 1. As T→∞, (i) N_0^s(T,2T) ≥ (2/3−o(1)) N(T,2T), (ii) N_d(T,2T) ≥ (5/6−o(1)) N(T,2T).
With the Montgomery--Taylor window ψ_MT in place of the indicator window ψ_0, the constants improve to
2−c_MT^{−1}=0.67250... and (1/2)(3−c_MT^{−1})=0.83625... respectively, where
c_MT^{−1}:=1/2+(1/√2)cot(1/√2) ... A fortiori N_0^*(T,2T), N_0(T,2T), N^s(T,2T) ≥ (2/3−o(1))N(T,2T)."
"The same holds for (0,T) in place of (T,2T), with rate O(log log T/log T)."
"Theorem 2. Theorem 1 holds verbatim for L(s,χ) in place of ζ(s), for any fixed primitive Dirichlet
character χ."

Announced headline (as stated in the test instruction): "the proportion of non-trivial zeros proved on the
critical line raised from 41.6% to 67.2%".

Task: one Lean 4 file (Mathlib only; Mathlib has `riemannZeta`, `DirichletCharacter.LFunction`,
`analyticOrderAt`) at runs/2026-11-26T1529Z/T2/reading.lean with your definitions (doc comment quoting the
source for each), and these theorems, each `:= by sorry`:
  reading_1i, reading_1ii (Theorem 1 (i), (ii) with constants 2/3 and 5/6),
  reading_1_MT (both Montgomery–Taylor constants, with c_MT defined exactly as in the source),
  reading_1_afortiori (the N_0^* case of the "a fortiori" sentence, constant 2/3),
  reading_cumulative (the (0,T) sentence, for N_0^s and N_d with the constants 2/3 and 5/6),
  reading_2 (Theorem 2 for (i) and (ii)),
  reading_headline (the announced 67.2% sentence, read literally).
Encode "≥ (c−o(1)) X as T→∞" faithfully and say how. Avoid junk values (an infinite set's cardinality or
sum, values at the pole): say in a comment how each is excluded or why it cannot arise. Then list every
ambiguity and your choice in a comment block at the end.
