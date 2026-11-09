# Prior-art screen: Falkner–Skan β < 0 (uniqueness class, continuum, reversed-flow branch at β = −0.1)

Screener: subagent (general-purpose; WebSearch/WebFetch; arxiv.org/abs|pdf only, failed fetch = not read). Its Write call was blocked by the harness; the main session saved its returned text here. **Caveat: the decisive primary texts were NOT read** (Coppel 1960, Hartman Ch. XIV, Hastings 1972, Libby & Liu 1967, Brown & Stewartson 1965: paywalled/blocked). Statements about them come from secondary sources read, or from memory where marked.

## 1. (A) uniqueness for β < 0 in the class f'' > 0 + super-exponential approach — partly in print; confidence medium-low
- Craven & Peletier 1972 (Mathematika 19:129–133): β ≥ 0 (as summarised by Fazio, arXiv:2011.07725, read: 0 ≤ β ≤ 1, restriction 0 < f' < 1 dropped). Asaithambi (Fluids 6:153, 2021, read): 0 ≤ β < 1.
- Coppel 1960: abstract only. Asaithambi says Veldman & van de Vooren extended Coppel's work to β < 0.
- Hartman: Gao–Zhang–Zhao (arXiv:2303.17781, read) restate his theorem only for β > 0 (class f'' > 0, Gaussian asymptotics).
- Caltech annotated bibliography (authors.library.caltech.edu, read): Hartree 1937 selects the unique β < 0 solution by "most rapid approach"; Hartman 1964: for β < 0 only one integral is exponential, the rest algebraic.
- No readable statement of the exact theorem "f'' > 0 + super-exponential approach ⇒ unique, every β < 0" found. From memory only: Hartman Ch. XIV has a β < 0 uniqueness result under an exponential-decay condition (β₀ ≈ −0.1988). To check by hand.
- "Every β < 0" is vacuous below β₀ (no attached solution).

## 2. (B) continuum with algebraic decay in 0 ≤ f' < 1 — yes in substance, mostly non-rigorous; confidence medium
- Brown & Stewartson, JFM 23 (1965), "…with algebraic decay": not read; Hewitt–Duck–Stow (JFM 468, 2002, read) credit them with algebraically decaying solutions existing only for β < 0, and call exponential decay a "somewhat arbitrary" selection (otherwise continua).
- Caltech bibliography (read): Brauner et al. 1982: algebraic decay for −0.1988 < β < 0 except two extremal solutions.
- No rigorous continuum theorem with 0 ≤ f' ≤ 1 and 1 − f' ~ Cη^{2β} found.

## 3. (C) reversed-flow branch — analytically proved; nothing computer-assisted or formal found
- Yang & Lan, CPAA 12 (2013) 2465–2495 (abstract read): reversed-flow solutions for every parameter in (−1/6, 0) (check the parameter convention against β).
- Hastings 1972 (SIAM J. Appl. Math. 22, not read): per Asaithambi, existence and uniqueness of Stewartson's reversed flows; Hastings & Siegel 1972 (Mathematika 19:76) small −β. Iyer–Masmoudi (arXiv:2203.02845, read) cite reversed-flow existence on (β*, 0) as classical.
- Lan & Yang 2011 (Nonlinear Anal., summary read): nonexistence below some λ*.
- No computer-assisted / interval / validated-numerics proof for Falkner–Skan (either sign of β), none for Blasius, no proof-assistant treatment found (targeted searches; MathSciNet unavailable).

## 4. Tabulated f''(0) at β = −0.1
- Ganapol, arXiv:1006.3888 (read; non-rigorous): attached 3.19269759843E-01 (12 digits, Table 6; agrees with Katagiri 1986, not read); reversed −1.40546212979E-01 (Table 7, "correct to several units in the last place").
- Fazio Table 4 (read): reversed branch, Stewartson 1954 −0.141; Asaithambi, Auteri et al. −0.140546. Zhu–Cheng–Wu Table 5 (read): attached 0.319270. Cebeci–Keller: 3 digits for the reversed branch (per Ganapol).
- Both planned enclosures contain Ganapol's values.

## 5. Already in print?
- (A): partly — selecting the exponentially decaying solution is classical (Hartree, Stewartson); the exact rigorous theorem not verified (Coppel 1960, Hartman Ch. XIV to check).
- (B): qualitatively yes (Brown–Stewartson 1965; Brauner et al. 1982; Hewitt–Duck–Stow 2002), not as a rigorous theorem at β = −0.1.
- (C): existence of both branches analytically known; digits printed to 12 places; no rigorous enclosure or formal proof found — the certified part appears new.

## Not read (failed or blocked)
SIAM 10.1137/0122031 (Hastings 1972); Cambridge Core (Mathematika reversed-flow article, Lan–Yang CMB PDF); ScienceDirect (Lan–Yang 2011, CNSNS algebraic-decay paper); AIAA 10.2514/3.4130 (Libby & Liu); Bohrium (Brown–Stewartson 1965); rjp.nipne.ro (robots.txt); ResearchGate; arxiv.org/abs/math/0603194 (permission timeout); Hartman's book, Stewartson 1954, Cebeci–Keller (no full text).
