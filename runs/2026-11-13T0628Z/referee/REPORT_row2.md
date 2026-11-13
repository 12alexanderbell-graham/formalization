# Referee report, row β = −0.02 (`fs_rev_two_exists`), run 2026-11-13T0628Z

Referee: Sonnet subagent, read only `Work/FalknerSkan/ReversedRowTwo.lean`; report returned as text and saved here by the main session (summary, verbatim numbers). Scripts in /tmp (not kept).

- Statement attack: one-sided derivatives on Ici 0 are the right reading; polynomial right-hand sides, so the initial data and q(0) fix the solution; no division or other junk value; the decay clause excludes the algebraic branch (q/(1 − p) ~ −2β/η → 0 there) and selects the super-exponential class; p ≡ 1 fails p(0) = 0. No defect.
- Own Taylor integrator (mpmath, 60 digits, order 45, step 1/8), secant shooting with p(L) = 1: L = 15 → −0.0651685855873840347629046929567; L = 20 → −0.0651685855429030724826350944226; L = 25 and 30 → −0.0651685855429030724826350943999. Step 1/16 at L = 25: p(25) − 1 = −3e-61. q(0) = −0.06516858554290307248263509. Margins 5.71e-11 above the lower end, 4.29e-11 below the upper end: strictly inside.
- Along the solution: min p = −0.115111057133432 at η ≈ 3.625; q < 0 from 0, one sign change in (3.5625, 3.625); p changes sign once near η ≈ 6.31; p ∈ [−0.1151, 1); min q = q(0), max q = 0.312015007263604 at η ≈ 8.81 (unscaled; scaled by 1/√(2/100)^? not computed: the main session's scaled clamp check is the generator's, max scaled q ≈ 2.21 in run 0428Z's feasibility log).
- Decay class: q/(1 − p) = 0.380, 1.391, 3.10, 4.999, 6.949, 8.920, 10.901 at η = 8, 10, …, 20 (≈ f(η)), so it grows without bound.
- Prior art: arXiv:1006.3888v1 (pdf, pdftotext) Table 7 prints β = −2.00E-02 → −6.51685855429E-02: agrees to all 12 printed digits; inside the window. Run 2026-11-12T2228Z's referee had −0.0651685855429030725 (same).
- VERDICT: STANDS.
