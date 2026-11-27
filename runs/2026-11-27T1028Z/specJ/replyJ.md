# Reader J (Opus) reply, verbatim as returned to the orchestrator

**File:** /home/claude/formalization/runs/2026-11-27T1028Z/specJ/SecondReadingSpecJ.lean

**Compiled:** yes. `lake env lean` on it gave no errors and no warnings, and a test `#check` of the fields worked. The file has no `sorry`, no `axiom`, no new notation and no helper defs (every formula is written out inside its field). Its only import is `Mathlib.Analysis.Calculus.Deriv.Basic`, and it sits in namespace `Checked.Trust.SecondReadingSpecJ`.

**Source read:** only the brief and /home/claude/formalization/runs/2026-11-27T1028Z/sources/bamba2012_1205.3421v3.md. Nothing else in the repository was read or listed. One `ls` of the specJ folder was refused by the permission system, and I did not retry it.

**Conventions used in all three items (source lines are lines of that file):**
- κ² = 1 (line 91).
- H = ȧ/a, and H₀ = ȧ(t₀)/a(t₀), using Mathlib `deriv`. The source never spells out H = ȧ/a; I used the standard definition.
- R = −6(Ḣ + 2H²), the §XI sign from lines 162–165, with Ḣ = `deriv (fun s => deriv a s / a s) t`.
- Ṙ is `deriv` of the explicit R function and R̈ is `deriv (deriv …)`. F′, F″, F‴ are `deriv F`, `deriv (deriv F)` and `deriv (deriv (deriv F))`, evaluated at R(t).
- The source's a⁻³ (lines 105, 112, 150) assumes a(t₀) = 1 (compare line 25, a₀ = 1). Because the scale factor here is not normalised, I read a⁻³ as (a(t₀)/a(t))³.
- The source is silent on smoothness, so I added no differentiability hypotheses. Every derivative is Mathlib's total `deriv`, and this choice is stated in the docstrings.

**1. DustDensitySpecJ** — two fields, both taken from lines 102–106:
- `present_value`: if a t₀ ≠ 0, then ρ Ω a t₀ t₀ = 3 (ȧ(t₀)/a(t₀))² Ω.
- `dust_scaling`: if a t ≠ 0 and a t₀ ≠ 0, then ρ(t)·a(t)³ = ρ(t₀)·a(t₀)³.
- **Determines:** ρ Ω a t₀ t = 3 H₀² Ω (a(t₀)/a(t))³ for all Ω, a, t₀, t with a t ≠ 0 and a t₀ ≠ 0. Values where a vanishes are left unconstrained.

**2. FRFriedmannSpecJ** — one field, `iff_friedmann`:
- Under a t ≠ 0, a t₀ ≠ 0 and F′(R(t)) ≠ 0, P holds iff H² = (1/3)(ρ_M/F′ + (1/F′)[(F − R F′)/2 − 3 H Ṙ F″]).
- This is the equation exactly as printed: lines 82–86 with ρ_curv from lines 96–100 written in, and ρ_M as in item 1.
- **Determines:** the truth of P for all arguments with a t ≠ 0, a t₀ ≠ 0 and F′(R(t)) ≠ 0.

**3. FRMasterSpecJ** — one field, `iff_master`, under the same side conditions:
- P holds iff Ḣ = −(1/(2F′))[3H₀²Ω(a₀/a)³ + R̈F″ + Ṙ(ṘF‴ − HF″)], from lines 148–157.
- **Determines:** the same set of arguments as item 2.

**Ambiguous, inconsistent or questionable points in the source:**
- **Sign of R:** §XI (line 163) has R = −6(Ḣ + 2H²), but §VIII (lines 32, 35) has R = +6(Ḣ + 2H²). The +6 version is the standard one for the (−,+,+,+) metric of line 14. I used −6, as the brief instructs.
- **Sign of the F − RF′ term:** the Friedmann form gives 3F′H² = ρ_M + (F − RF′)/2 − 3HṘF″. The usual (−,+,+,+) result has (RF′ − F)/2 together with R = +6(…). §XI looks like a mix of conventions, and I did not check whether the Friedmann and master equations are consistent with each other under R = −6(…). I encoded both as printed.
- **Typo in the master equation:** lines 151–154 contain a doubled "+ +" left behind by a commented-out line break. I read it as a single "+".
- **Two names for Ω:** line 105 writes Ω_M, while lines 106, 111 and 150 write Ω_M^{(0)}. I took them as the same present matter density parameter Ω.
- **Normalisation:** line 105 relies on a(t₀) = 1, so I generalised it as described above.
