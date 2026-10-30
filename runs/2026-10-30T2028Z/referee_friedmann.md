# Referee report: `Work.Fidelity.FriedmannBlind.FriedmannLCDM`

File: `Work/Fidelity/FriedmannBlind.lean` (only file read). It type-checks
(`lake env lean Work/Fidelity/FriedmannBlind.lean`, exit 0, no output). Nothing in the repo was changed.

**Verdict: STANDS** (the only notes are cosmetic and about scope; none needs a fix)

## 1. Field-by-field fidelity

Predicate: `∃ ρ Λ, (∀ᶠ t in 𝓝 t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧ ρ t·a t³ = ρ t₀·a t₀³ ∧ (a'/a)² = ρ t + Λ/3) ∧ 0 < a'(t₀) ∧ Ω = ρ t₀ / (a'(t₀)/a(t₀))²`.

| Item | Check |
|---|---|
| Units | With c = 1, H² = (8πG/3)ρ − K/a² + Λ/3. Setting 8πG/3 = 1 and K = 0 gives H² = ρ + Λ/3. Λ has units of 1/time² (c = 1), so the 8πG/3 = 1 choice leaves the Λ/3 term as it is. Correct. |
| Λ/3 term | Correct. It implies Ω_Λ = Λ/(3H₀²) = 1 − Ω (flatness closure). |
| Critical density | ρ_c = 3H²/(8πG) = H² in these units. Correct. |
| Dust continuity | The integrated form ρa³ = ρ₀a₀³ holds on the neighbourhood. On a connected interval with a > 0 this is equivalent to ρ̇ + 3Hρ = 0, and it does not need ρ to be differentiable, which is better than the differential form. Correct. |
| Expansion | `0 < deriv a t₀`. Because the derivative is nonzero, a is differentiable at t₀, so this is not the junk value 0. Section 2 shows that ȧ > 0 on a whole neighbourhood follows from it. |
| Ω | Divides by H₀² with H₀ = ȧ₀/a₀ > 0, so the division is genuine. |
| Quantifiers | `∃ ρ Λ` sits outside `∀ᶠ`, so Λ is one constant and ρ is one function. With the quantifiers inside, Λ could depend on t and the predicate would be far too weak. The `ρ t₀` inside the filter refers to the same ρ. Correct. |
| Junk guards | `a t > 0` makes the quotient a genuine ratio. `DifferentiableAt` at every point of the neighbourhood (including t₀) makes `deriv` genuine. The powers `^2` and `^3` are natural-number powers. There are no square roots and no other partial operations. |
| Local vs global | The statement is local (any neighbourhood of t₀). This is the right choice for "the model near today": a global version would wrongly reject sin^{2/3}, cosh^{2/3}-with-Ω<0, and so on, because a ≤ 0 or ȧ ≤ 0 somewhere. Scope note: any downstream global quantity (the age ∫dt, a horizon) needs more hypotheses than this predicate supplies. |

## 2. Strength: the predicate is equivalent to the H(z) form, and Ω is determined by a

**Claim.** `FriedmannLCDM Ω a t₀` ⇔ there is H₀ > 0 such that, on a neighbourhood of t₀, a > 0, a is differentiable, and H(t) = H₀·√(Ω(1+z)³ + 1 − Ω) with 1+z = a(t₀)/a(t).

(⇒) Set H₀ = ȧ₀/a₀ > 0. On the neighbourhood, ρ(t) = ρ₀x³ with x = a₀/a, and ρ₀ = ΩH₀². Evaluating the Friedmann equation at t₀ gives Λ/3 = H₀² − ρ₀ = H₀²(1 − Ω). So H² = f(t) := H₀²(Ωx³ + 1 − Ω).
- f is continuous, because a is differentiable and therefore continuous on the neighbourhood, and f(t₀) = H₀² > 0. So f > 0 on a smaller open interval I around t₀.
- On I, ȧ² = a²f > 0, so ȧ never vanishes on I. ȧ is a derivative on the open interval I, so by Darboux it has the intermediate value property and cannot change sign. Since ȧ(t₀) > 0, ȧ > 0 on I.
- Hence H = +√f = H₀√(Ω(1+z)³ + 1 − Ω) on I. So the sign of H near t₀ is forced, not only its sign at t₀.

(⇐) Take ρ(t) := ΩH₀²(a₀/a(t))³ and Λ := 3H₀²(1 − Ω). Lean's `√` returns junk on negative input, but the radicand equals 1 at t₀ and is continuous, so it is positive on some neighbourhood and the filter absorbs this. The H(z) form at t₀ gives ȧ₀/a₀ = H₀ > 0, and then Ω = ρ₀/H₀² holds by construction.

**Ω is determined by (a, t₀).** Suppose two pairs (ρ₀, Λ) and (ρ₀', Λ') both work. Then (ρ₀ − ρ₀')x(t)³ = const near t₀. Since ȧ₀ > 0, a is not constant on any neighbourhood of t₀, so x³ is not constant either, and therefore ρ₀ = ρ₀'. Near t₀, ρ is pinned to ρ₀a₀³/a³, so the free choice of ρ cannot launder a junk density. Values of ρ off the neighbourhood are unconstrained, which is harmless.

**Regularity.** "Differentiable" is enough. On I, ȧ = a√f with f continuous, so a is C¹. Bootstrapping makes a C^∞, in fact analytic. The second Friedmann (acceleration) equation then follows by differentiation, because H ≠ 0.

**Attack cases:**
- Contracting somewhere near t₀: impossible, by the Darboux argument above.
- a not differentiable: rejected by the `DifferentiableAt` field.
- ρ junk: pinned near t₀, as above.
- Radiation or curvature admixtures: rejected, because ρ₀x³ + Λ/3 cannot reproduce an x⁴ or x² term on an interval where x varies.
- a(t₀) ≠ 1: accepted (correct, a is not normalised).
- Λ < 0 and ρ < 0: accepted, as the docstring says.
- Bounce cosh^{2/3} at t₀ > 0 with Ω < 0: accepted. At t₀ = 0 (the bounce itself): rejected because ȧ₀ = 0. This is correct, since Ω = ρ₀/0 is undefined there.
- sin^{2/3} with Λ < 0, 0 < t₀ < π/2: accepted. At the turnaround t₀ = π/2: rejected, for the same reason.
- Contracting branches (ȧ₀ < 0): rejected. This matches "expanding at t₀".

## 3. Closed forms (sympy symbolic plus numerical checks)

| a(t) | domain of t₀ | ρ(t) | Λ | Ω at t₀ |
|---|---|---|---|---|
| t^{2/3} (EdS) | t₀ > 0 | 4/(9t²) | 0 | 1 |
| sinh^{2/3} t | t₀ > 0 | 4/(9 sinh² t) | 4/3 | 1/cosh² t₀ ∈ (0,1) |
| sin^{2/3} t | 0 < t₀ < π/2 | 4/(9 sin² t) | −4/3 | 1/cos² t₀ > 1 |
| cosh^{2/3} t | t₀ > 0 | −4/(9 cosh² t) | 4/3 | −1/sinh² t₀ < 0 |
| e^{ht}, h > 0 | any t₀ | 0 | 3h² | 0 |

For all five rows, sympy gives exactly zero for each of these three residuals:
- H² − ρ − Λ/3
- d(ρa³)/dt
- ρ(t₀)/H(t₀)² − Ω

Numerical spot checks of the same three quantities are ≤ 1e-15. A separate numerical check of H(t) − H₀√(Ω(1+z)³ + 1 − Ω) on t₀ ± 0.05 gives ≤ 3e-10 (finite-difference error). The in-file proof `einsteinDeSitter` uses ρ = 4/9/t², Λ = 0, and t₀ = 1, which matches the table.

## 4. Minor notes (no correction required)
1. The citation "Ryden eq. 4.17/5.x" is vague. This is cosmetic.
2. The predicate is local, so downstream global claims (age of the universe, behaviour as t → ∞) need extra hypotheses. That is a scope limitation, not a defect.
3. ρ is left arbitrary outside the neighbourhood. This is harmless, since only ρ t₀ enters Ω.
