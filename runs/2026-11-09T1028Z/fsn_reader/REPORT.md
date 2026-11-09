# fsn_reader report (Sonnet subagent, from brief 600017e alone; verbatim summary by the main session)

- ODE: sympy residual of the boundary-layer momentum equation ∝ −(m+1)(f''' + f f'') + 2m(f'² − 1), so f''' + f f'' + β(1 − f'²) = 0 with β = 2m/(m+1); at m = −1/21, β = −1/10. BETA = -1/10, A = 1, C = 2, D = 1 (u = U f').
- Edge: with g = 1 − p, q = −g', linearisation g'' + (η + c) g' − 2β g = 0. Two kinds: algebraic g ~ C η^{2β} = C η^{−1/5}, q/g ~ 1/(5η) → 0; Gaussian g ~ C η^{−1−2β} e^{−η²/2}, q/g ~ η → ∞. The condition "for every M, eventually M(D − p) ≤ q" holds for the Gaussian kind and fails for the algebraic kind.
- Checks: sympy (both ansätze leave relative residual O(1/η²)); scipy shooting: s = 0.2 algebraic (η·q/g → ≈ 0.2), s* ≈ 0.31927 Gaussian-fast (q/g grows like η); shots below ≈ 0.317 stay below 1 with algebraic decay (a continuum, matching non-uniqueness).
- Consulted: brief, own derivation, sympy, scipy. No web, no repository files. Compiles (`lake env lean`, rc 0; deprecation warning for the import path).
