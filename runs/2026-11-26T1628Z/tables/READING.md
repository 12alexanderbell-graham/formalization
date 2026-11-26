# Reading of printed H2+ tables (fresh Sonnet reader, brief BRIEF_TABLES.md committed first in faf5466)

Saved verbatim from the reader's final message (run 2026-11-26T1628Z). The reader read through WebFetch
(a model extraction of the PDF, not the glyphs); its own caveat is kept.

  Caveat: both pages were read through WebFetch, which returns a model-generated extraction of the PDF, not raw text. Digits and quotes below are as that extraction gave them. They have not been checked against the PDF glyphs. Please spot-check them.

  SOURCE 1: https://arxiv.org/pdf/physics/0607081 (opened)
  - Tables 2, 6 and 7 are the only ones that give R = 2. They print p and A, not E.
  - Table 2, "Convergence of "Taylor series" of A(p^2) Ground State: 1s sigma_g (n=1,ell=0,m=0)". Row printed as `2.0 | 1.48501462 | .811729585 | .8118596153`. Columns: R | p | A (ODKIL accurate) | A (series, 20 terms).
  - Table 6, "Convergence of Series A(x,y) Ground State Revisited: ...". Row printed as `2 | 0.81172958404 | 0.8117295840 | 0.8117295850`. Columns: series (12 terms) | ODKIL (accurate) | Sidi-d.
  - Table 7, "Convergence of A(R, p) Ground State: ...". Row printed as `2.0 | 1.48501462 | 0.811729585 | 0.8117297560`.
  - Energy in the text: the electronic energy "evaluated at R=2.0 a.u. for comparison" is printed as -0.6026342144949. Eq. (11) is printed as E_elec = -2p²/R², and Eq. (21) as E_T = E_elec + 1/R. With p = 1.48501462, E_elec would be about -1.1026, so the printed -0.60263... looks like the total energy. The text label and the number disagree. I did not reconcile them.
  - Unit: a.u. (atomic units).
  - Separation constant A at R = 2: 0.811729585 (ODKIL), 0.8117295840 in Table 6. Eq. (10) defines A as the separation constant of the prolate-spheroidal ODEs. Eq. (12) gives A → -ℓ(ℓ+1) as R → 0.

  SOURCE 2: https://arxiv.org/pdf/1401.8009 (opened)
  - Table I: "The total energy E(R) for 1sσg state of the H+2-ion compared to [5] (rounded) and Lagrange mesh method (cf. [2]); Req = 1.997193 a.u., p is taken as variational parameter".
  - Columns: R[a.u.] | E[Ry] (Present/[5]/Mesh) | p.
  - R = 2.0 row: -1.20526842899 (three stacked lines, all the same value), p = 1.485015.
  - Type and unit: the caption says "total energy". The text defines E' = E − 2Z1Z2/R, with E the total energy, in Rydberg. So this is the total energy including the nuclear repulsion, in Ry, not hartree.
  - Separation constant, Table VI, column 1sσg (000+), at R = 2.0: A1,ξ = 0.8117295877, A1,η = 0.8117295852, Madsen and Peek 0.8117295846248. Convention: Lξ X = −A X (Eq. 6) and Lη Y = −A Y (Eq. 7).

  Third source: not needed, because two sources print R = 2.

## Program's note (not the reader's)
- Both sources print the TOTAL energy at R = 2: -0.6026342144949 hartree (Scott et al., labelled "electronic"
  in the text: a Source-class labelling error, the number and its Eqs. (11), (21) say total) and
  -1.20526842899 Ry = -0.602634214495 hartree (Olivares-Pilon/Turbiner, Table I). Electronic eigenvalue of the
  separated equations: total - 1/R = -1.1026342144949.
- Separation constant printed +0.8117295846248 (Madsen-Peek via Table VI of 1401.8009); the screen script's
  convention has the opposite sign (A = -0.8117295846). p = sqrt(-E R^2/2) = 1.48501462 printed.
- Not yet: the glyphs themselves (the extraction is a model's); the freeze needs a literal reading of the
  digits it uses, by the program's literal-reading route.
