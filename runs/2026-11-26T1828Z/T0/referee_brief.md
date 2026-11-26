# Referee brief (run 2026-11-26T1828Z, target 0, angular sum)

You are a referee for a formal-verification audit of arXiv 2611.34924v1 (Chandrasekaran, "An algebraic
quantization of gravity from the null cone"). Read ONLY the LaTeX source at
/tmp/claude-0/-home-claude-formalization/67e9266c-878f-55df-ab45-aec72f7e14c8/scratchpad/t0/src/main.tex
(the PDF of the same version is paper.pdf in the directory above, if you prefer typeset equations).
Do not open any other file of the repository, do not search the web, do not run git.

Sections 4.4 ("Finiteness of transition amplitudes", main.tex lines ~1250-1440) compute a graviton pair
creation-and-annihilation amplitude, Eqs. (4.32)-(4.34), "for one polarization and one real valued angular
harmonic". Answer, with line numbers and equation labels for every claim:

1. Does the paper, anywhere (main text, footnotes, appendices), give a dependence of the Gaussian widths
   (Δq)^2 of the mode variables on the angular harmonic (angular momentum j, m) or on the polarization?
   Search the whole file. Quote every sentence relevant to how the width or the one-graviton normalization
   depends on the harmonic (Sec. 4.2 around (4.7)-(4.9); Sec. 4.4; Appendix D.3 "Focusing and the number of
   graviton states"; the symplectic form (3.42)).
2. Does the paper anywhere treat the sum of this pair amplitude over angular harmonics or polarizations,
   or state that the finiteness claim is restricted to one harmonic? Quote.
3. If the same quadratic insertion and the same boundary phase were used in every radiative harmonic, with
   the widths the paper's definitions give in each harmonic, would the sum over harmonics of the pair
   amplitude converge or diverge? Give your reasoning in a few lines, and say which of these holds:
   (i) the paper makes the sum over harmonics converge; (ii) the claim is meant for one harmonic and only
   some wording is broader; (iii) the sum over harmonics diverges under the paper's own definitions.
   More than one may hold; say which and why.
4. Quote every sentence of the abstract, introduction or conclusions that states the finiteness of this
   amplitude without the one-harmonic restriction.

Report in under 600 words. Be adversarial: if the reading "the width does not depend on the harmonic" is
not supported by the text, say so.
