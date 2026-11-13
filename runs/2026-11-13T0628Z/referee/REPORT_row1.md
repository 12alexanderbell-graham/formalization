# Referee report, row β = −0.01 (`fs_rev_one_exists`), run 2026-11-13T0628Z

Referee: Sonnet subagent, read only `Work/FalknerSkan/ReversedRowOne.lean`; report returned as text and saved here by the main session (summary, verbatim numbers). Scripts in /tmp (not kept).

- Statement attack: one ∃ f p q, derivative clauses on Ici 0 (one-sided at 0), ∀ M ∀ᶠ is the faster-than-every-exponential class; p ≡ 1 excluded by p(0) = 0, the attached branch by the negative window; no junk value. No defect.
- Own Taylor integrator (mpmath 45 digits, order 34, step 1/8 or 1/16), secant on p(η∞) = 1: η∞ = 15 → −0.0423217953845 (not converged); 20 → −0.04232092603915720673; 25, 30, 35 → −0.04232092603915720670990199. q(0) = −0.0423209260391572067099; margins 6.08e-11 above −0.0423209261, 3.92e-11 below −0.0423209260.
- min f' = −0.101394724762 at η ≈ 4.94; q < 0 on [0, 5), one sign change; max q = 0.303772 at η ≈ 11.0; f' ∈ [−0.1014, 1); q/(1 − p) = 2.93, 4.82, 6.76, 8.73 at η = 14, 16, 18, 20 (≈ η − 11).
- Prior art: arXiv:1006.3888v1 Table 7 (pdftotext) prints β = −1.00E-02 → −4.23209260392E-02: all 12 digits agree; inside the window.
- VERDICT: STANDS.
