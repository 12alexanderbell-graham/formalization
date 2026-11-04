# Blind restatement notes: RK acentric factor

File: Work/Chemistry/RKAcentricBlind.lean (namespace Blind.RKAcentric). Elaborates; only `sorry` warnings.

Reading choices:
1. Pressure `rkP R A b v T = R*T/(v-b) - A/(sqrt T * v * (v+b))`, a total function on ℝ. Every
   statement only evaluates it at `T > 0`, `v > b > 0`, so no junk from division or sqrt is reached.
2. Critical point is a hypothesis predicate `IsCriticalPoint`, defined by derivatives (not by closed
   forms): `0 < Tc`, `b < vc`, `deriv (v ↦ P v Tc) vc = 0`, `deriv (deriv ...) vc = 0`, `Pc = P vc Tc`.
   Because `v ↦ P v Tc` is smooth on the open set `v > b`, `deriv` and `deriv ∘ deriv` at `vc` are the
   true derivatives. Closed forms (`vc = b/(2^{1/3}-1)`, `Z_c = 1/3`, Ω_a, Ω_b) are only in a comment.
3. I added two supporting theorems (critical point exists; it is unique) so the main theorems are not
   vacuous because of the hypothesis-style critical point, and so "its critical point" is well defined.
4. Coexistence `IsCoexistence T vl vg ps`: `b < vl < vg`, `P vl T = ps = P vg T`, and
   `∫_{vl}^{vg} P v T dv = ps*(vg - vl)` (interval integral, continuous integrand, no junk).
   No extra stability or ordering-of-roots condition: the claim says "every coexistence state", so the
   predicate is exactly the stated Maxwell construction. `ps > 0` is not assumed; it is a conclusion.
5. Temperature `0.7 T_c` is written `7/10 * Tc`.
6. ω = `-Real.logb 10 (ps/Pc) - 1`. To keep the log off junk inputs, the conclusion also states
   `0 < ps/Pc` (it is implied by the rounding conclusion anyway).
7. "To 3 decimals" = `Checked.Records.RoundsTo x d 3`, i.e. `|x - d| ≤ 1/2000`, with d = 87/1000 and 58/1000.
8. Universality: all theorems quantify over arbitrary `R, A, b > 0` (as hypotheses `hR hA hb`) and over
   any triple satisfying `IsCriticalPoint`.
9. Two separate theorems (`coexistence_exists`, `coexistence_numbers`) plus a combined `rk_acentric`.

Numerical sanity check (mpmath, reduced units R = Tc = Pc = 1, b = Ω_b, A = Ω_a):
v_l ≈ 0.12085, v_g ≈ 7.3115, p_s/P_c ≈ 0.087442, ω ≈ 0.058280. Both lie inside the ±0.0005 window
(0.087442 is 0.00044 from 0.087, so the first rounding claim holds with little margin).
Note that the two rounding conditions together force p_s/P_c ∈ [0.08738, 0.0875].
Uniqueness of the coexistence state (needed for "every state") was not checked numerically beyond
the one root found.
