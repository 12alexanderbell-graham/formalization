# Reader H's reply (Opus subagent, verbatim content as returned to the orchestrator; condensed formatting)

File compiles (no errors, warnings, sorry, axiom); six Mathlib imports; four structures, one field each; docstrings cite transcription line numbers. Read only the brief and the three source files.

1. CurvParamSpecH: for 0 < a t0, deriv a t0 ≠ 0: `k K a t0 = -K / (a t0^2 (deriv a t0 / a t0)^2)`, i.e. Ω_K^(0) = −K/(a0²H0²) (§X lines: Ω0 = 1 + K/(H0²a0²) = 1 − Ω_K^(0)). **Ambiguous:** "the parameter that appears in the expansions" could mean the bare ratio +K/(H0²a0²), the combination printed in the coefficients; opposite sign. Chose Ω_K as the only curvature parameter §X names. Aviles uses the opposite sign, Ω_k ≡ Ω0 − 1. Own addition: a(t0) > 0.
2. RicciFlatSpecH: `R a t = -6 (deriv (a'/a) t + 2 (a'/a)^2)` for 0 < a t, a differentiable near t, a' differentiable at t. **Inconsistent in the source:** §VIII.C writes +6, §XI eq. (11.6) −6; followed §XI; either an opposite curvature convention or a typo, the excerpt does not say which.
3. FlatLCDMSpecH: for 0 < a t0, deriv a t0 ≠ 0: P ↔ near t0, a has derivative a t · H0 · √(Ω (a t0/a t)³ + 1 − Ω). Near t0 because of "for our purposes and the redshifts involved sufficiently described", radiation neglected "at late times", formula used only for the cosmographic series at t0; all-times would fail at the big bang. H0 > 0 not required (source silent). Questionable in source: m0 formula's two Ω_m² terms; series sign −H0Δt vs (expa); "t − t0 > 0" though light is received from t ≤ t0.
4. FlatCPLSpecH: same shape with ecpl; positive root since E(0) = 1; near t0.
Caveat: side conditions a(t0) > 0 and H0 ≠ 0 outside the equivalence; a program putting H0 > 0 inside its condition disagrees on contracting cases.
