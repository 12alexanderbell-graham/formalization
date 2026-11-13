# Referee report, row β = −0.03 (`fs_rev_three_exists`), run 2026-11-13T0228Z

Referee: Sonnet subagent, read only `Work/FalknerSkan/ReversedRowThree.lean`; report returned as text and saved here by the main session (summary, verbatim numbers).

- Own Taylor integrator (mpmath, 40 digits, order 44, step 1/8), bisection on q(0): η∞ = 12 → −0.0825638868 (not converged); 15 → −0.08256296511880281; 20 and 25 → −0.08256296511875790932 (identical). Converged q(0) = −0.082562965118757909. Margins: 8.12e-11 above the lower end, 1.876e-11 below the upper end: strictly inside.
- Along the solution: min f' = −0.12067 at η ≈ 3.0, f' < 1 throughout, f' → 1 from below (1 − f' ≈ 1.3e-12 at η = 15); f'' changes sign once at η ≈ 2.9–3.0, max 0.3182 at η ≈ 7.6. −1 ≤ f' ≤ 1 holds.
- Decay class: f''/(1 − f') = 0.84, 2.32, 4.17, 6.11 at η = 8, 10, 12, 14 (≈ η − 8.04): the faster-than-every-exponential condition holds and is not vacuous. No second solution in the window (single crossing in the shooting scan). No quantifier or junk-value issue found.
- Prior art: arXiv:1006.3888v1 (pdf, pdftotext) Table 7 prints β = −3.00E-02 → −8.25629651188E-02, 4.2e-14 from the referee's value (Ganapol's 12-digit rounding); inside the window.
- VERDICT: STANDS.
