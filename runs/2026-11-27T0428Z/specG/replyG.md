# Reader G's reply (Sonnet subagent, verbatim as returned to the orchestrator; formatting only)

File: runs/2026-11-27T0428Z/specG/SecondReadingSpecG.lean. Compiled with no output (no errors, warnings, sorry or axiom). Read only the brief and bamba2012_1205.3421v3.md, aviles2012_1204.2007.md, capozziello2011_1104.3096.md. One helper def, `hubble a t = deriv a t / a t`.

1. CurvParamSpecG: `k K a t0 = K / ((a'(t0)/a(t0))^2 * a(t0)^2)`; determined where `a t0 ≠ 0` and `deriv a t0 ≠ 0`. Sign from bamba lines 59 and 9825-9851 (series contain `-K c²/(H0² a0²)`, `Ω0 = 1 + K c²/(H0² a0²)`), so k = +K/(H0² a0²) = Ω0 − 1. Source sets a0 = 1; a(t0) kept.
2. RicciFlatSpecG: `R a t = -6 (Ḣ + 2H²)`; determined where `a t ≠ 0`, `a` differentiable near `t`, `deriv a` differentiable at `t`. Inconsistency in the source: §XI (eq. 11.6) has −6, §VIII.C (source lines 7317, 7515) has +6. Followed §XI. The §XI sign is the opposite of the usual one for the stated metric signature.
3. FlatLCDMSpecG: iff `a t0 > 0`, `H(t0) > 0`, and near `t0`: `a s > 0`, `a` differentiable, `H(s) = H(t0) √(Ω (a(t0)/a(s))³ + 1 − Ω)`. Choices where the source is silent: near t0 only (judgement), positive root and H0 > 0, Ω unrestricted. Determined for every (Ω, a, t0).
4. FlatCPLSpecG: same shape with the printed E²; 1+z = a(t0)/a(s), z/(1+z) = 1 − a(s)/a(t0); real power of a positive base. Same choices.
Other: aviles m0 formula has Ωm² twice (typo, unused); the bamba excerpt does not show how D_A is defined.
