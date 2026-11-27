# Reader I (Sonnet) reply, verbatim as returned to the orchestrator

File: /home/claude/formalization/runs/2026-11-27T1028Z/specI/SecondReadingSpecI.lean. Compiled with no errors, warnings, sorry or axiom (imports only Mathlib.Analysis.Calculus.Deriv.Basic). I read only briefI.md and sources/bamba2012_1205.3421v3.md.

Item 1, DustDensitySpecI. Determines ρ Ω a t₀ t for all Ω, t₀, t with a t₀ > 0 and a t > 0. The two fields are present value ρ(t₀) = 3 (a'(t₀)/a(t₀))² Ω and scaling ρ(t)·a(t)³ = ρ(t₀)·a(t₀)³.
- Choice: the source takes a₀ = 1 and prints ρ_M = 3H₀²Ω a⁻³ (lines 104-105). For an un-normalised scale factor I read this as 3H₀²Ω (a(t₀)/a(t))³, with H₀ = a'(t₀)/a(t₀). The source does not print H = a'/a, so that is my choice. κ² = 1 is from line 91.

Item 2, FRFriedmannSpecI. One field: P ↔ H² = (1/3)(ρ_M/F'(R) + ρ_curv). This follows lines 83 and 97-98, with R = -6(Ḣ + 2H²) from line 163. It is determined when a t₀ > 0, a t > 0 and F'(R(t)) ≠ 0.
- Choices: Ṙ, Ḣ and the F derivatives are Mathlib `deriv` of explicit functions. I add no differentiability hypotheses, so a failed derivative reads as Mathlib's junk value 0. Nothing is asserted when F'(R) = 0.

Item 3, FRMasterSpecI. One field: P ↔ Ḣ = -(1/(2F'))[ρ_M + R̈F'' + Ṙ(ṘF''' - HF'')], from lines 149-155. Determined under the same conditions as item 2. The same choices apply, and R̈ is `deriv (deriv (ricci a))`.

Source problems:
- Sign of R: section XI line 163 prints R = -6(Ḣ + 2H²), but §VIII.C (lines 7317 and 7515) prints R = +6(Ḣ + 2H²). The metric at lines 14-16 has signature (-+++), where the standard value is +6. I used the section XI sign as the brief instructs.
- ρ_curv consistency: I did not verify that the ρ_curv of line 97 matches standard F(R) cosmology under the -6 sign.
- Matter term in the master equation: line 150 writes 3H₀²Ω a⁻³ where line 105 writes Ω_M^{(0)}, so Ω_M and Ω_M^{(0)} are the same quantity.
- w_curv: eq. (wcurv), lines 119-121, is not used by any item.
- Source gap: the source never states a₀ ≠ 1 handling.
