# Blind reader: ROBER reference solution (run 2026-11-06T0828Z)

Subagent (general-purpose), brief: transcribe the published ROBER reference values from primary
sources only (test-set PDF rendered to PNG, Fortran `solut` raw text); not allowed to read the
repository. Report (verbatim values):

- Source A: Bari IVP test set, problem description II-10 "Problem ROBER" (PDF created 2008-02-28,
  release 2.4, Mazzia & Magherini), page II-10-3, Table II.10.3 "Reference solution at the end of
  the integration interval" (crop `typeset/rober_pdf_p3_table_II.10.3.png`):
  y1 = 0.2083340149701255·10⁻⁷, y2 = 0.8333360770334713·10⁻¹³, y3 = 0.9999999791665050.
  Integration interval [0, 10¹¹] (Section 10.4, crop `typeset/rober_pdf_p2_section10.4.png`).
  Computed "by RADAU on an Alphaserver DS20E ... using double precision work(1) = uround =
  1.01·10⁻¹⁹, rtol = atol = h0 = 1.1·10⁻¹⁸". No stated accuracy.
  URL http://www.dm.uniba.it/~testset/report/rober.pdf (Wayback 20131012011104; the 2021 capture at
  archimede.dm.uniba.it has the same digest; live hosts reset TLS through the proxy).
- Source B: `rober.f` rev 1.2 (2006-10-02), subroutine `solut`: same three values
  (`0.2083340149701255D-07`, `0.8333360770334713D-13`, `0.9999999791665050D+00`).
- Source C: `rober.f` rev 1.1 (2003-09-04): same values.

Prior-art subagent (same message): no published rigorous enclosure of standard ROBER at any
t ≥ 10³ (ARCH-COMP ROBE21 uses other constants and t = 40; Zhang & Yap 2026 t ≤ 1); no
publication found documenting that the printed reference violates y1 + y2 + y3 = 1
(1 − (y1 + y2 + y3) = 1.0169·10⁻¹⁴ in exact decimal arithmetic on the printed values).
