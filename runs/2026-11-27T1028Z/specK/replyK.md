# Reader K (Haiku) reply, verbatim as returned to the orchestrator

File: /home/claude/formalization/runs/2026-11-27T1028Z/specK/SecondReadingSpecK.lean

Compiled: yes. `lake env lean` exited 0 with no output (no errors, no warnings). The file contains no sorry, no axiom, no notation or macros. Namespace `Checked.Trust.SecondReadingSpecK`. Imports: Mathlib.Analysis.Calculus.Deriv.Basic, Mathlib.Analysis.Calculus.ContDiff.Defs, Mathlib.Analysis.Calculus.IteratedDeriv.Defs.

Source read: /home/claude/formalization/runs/2026-11-27T1028Z/sources/bamba2012_1205.3421v3.md (the brief and this file only). Nothing else was read.

Helper defs (mine): hubbleRateK a t = deriv a t / a t; ricciScalarK a t = -6 * (deriv (hubbleRateK a) t + 2 * hubbleRateK a t ^ 2); matterDensityK Ω a t₀ t = 3 * H(t₀)^2 * Ω * (a t₀ / a t)^3; rhoCurvK F a t as eq. rhocurv (source lines 97–98).

1. DustDensitySpecK (ρ Ω a t₀ t).
- Determines ρ Ω a t₀ t for 0 < a t₀, 0 < a t, and a differentiable at t₀ (the value is 3 H(t₀)^2 Ω (a t₀/a t)^3).
- Field `scaling` (source lines 104–105, ρ_M = ρ_M(t₀) a^{-3}): ρ(t) = ρ(t₀)(a(t₀)/a(t))^3.
- Field `present` (line 105 with κ²=1, line 91): ρ(t₀) = 3 H(t₀)^2 Ω.
- Choices: the source writes a^{-3} with a(t₀)=1; I generalised it to the ratio a(t₀)/a(t). H = ȧ/a is not printed in the excerpt; the standard definition is used.

2. FRFriedmannSpecK (P Ω a F t₀ t).
- Equation: H² = (1/3)(ρ_M/F'(R) + ρ_curv) (source lines 83–84, 97), with κ²=1.
- Determines P at all arguments satisfying the side conditions: 0 < a t₀; a differentiable at t₀; eventually near t, 0 < a s and a is C^3 at s; F is C^2 at R(t); F'(R(t)) ≠ 0.
- Choices: the side conditions are my addition; they are needed for H, Ṙ, F'' to be defined and because the equation divides by F'. ρ_M is the explicit section XI matter term from item 1, since the structure's P does not take ρ.

3. FRMasterSpecK (P Ω a F t₀ t).
- Equation: Ḣ = -(1/(2F'(R)))[3H₀²Ω a^{-3} + R̈F'' + Ṙ(ṘF''' - HF'')] (source lines 148–157). The a^{-3} term is written with the matterDensityK generalisation.
- Determines P under: 0 < a t₀; a differentiable at t₀; eventually near t, 0 < a s and a is C^4 at s; F is eventually C^3 near R(t); F'(R(t)) ≠ 0.
- Choices: the C^4 and C^3 side conditions are my addition, needed for R̈ and F''' to exist.

Source points to flag:
- Sign inconsistency for R. Section XI, line 163, gives R = -6(Ḣ + 2H²). Section VIII, lines 7316 and 7515, gives R = +6(Ḣ + 2H²), which is the usual flat-FLRW form. I followed section XI as printed, per the brief. The master equation's curvature terms depend on this sign, so the other program should check that it uses the same convention.
- Section XI does not state the derivation. The master equation is said to follow from combining eq. curvcons (line 111) with eq. hfr (line 83). I did not check that derivation or the w_curv expression (lines 119–121), and they are not part of the three specs.
- The a^{-3} scaling in the source is valid only for a(t₀)=1, despite the text saying the metric is general. I used the ratio form.
- Section XI prints no equation number for the Friedmann equation; the excerpt refers to it as eq:Add-2-01 (line 77), which is not in the transcription, so I could not check it against the source.

Memory: I did not read or use any memory for this task.
