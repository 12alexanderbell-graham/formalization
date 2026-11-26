import Mathlib

open scoped BigOperators

namespace Reading

/-- Source §1.1: "Write ρ=β+iγ for a nontrivial zero of ζ(s)".
Nontrivial zeros of a function `F` (ζ or L(s,χ)) with ordinate in `(T1, T2]`:
zeros in the open critical strip `0 < Re < 1`, `T1 < γ ≤ T2`.
All zeros in this strip are nontrivial (trivial ones have Re ≤ 0). The pole at `s = 1` is
outside the strip (Re < 1), so no junk value at the pole is ever used. -/
def zerosIn (F : ℂ → ℂ) (T1 T2 : ℝ) : Set ℂ :=
  {ρ | F ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T1 < ρ.im ∧ ρ.im ≤ T2}

/-- Source: "m_ρ ≥ 1 for its multiplicity". The analytic order at ρ, as a natural number.
`analyticOrderAt` is `⊤` only if `F` vanishes near ρ, and `0` (junk) only if `F` is not
analytic at ρ; neither occurs for ζ, L(s,χ) at a zero in the strip (analytic away from 1,
not identically zero), so `toNat` is faithful and m_ρ ≥ 1. -/
noncomputable def mult (F : ℂ → ℂ) (ρ : ℂ) : ℕ := (analyticOrderAt F ρ).toNat

/-- Source: "N(T_1,T_2):=Σ_{T_1<γ≤T_2} m_ρ (zeros, counted with multiplicity)".
The set is finite (zeros are isolated, strip region bounded in Re and ordinate), so the
`finsum` is the true sum (a `finsum` over an infinite support would be junk 0). -/
noncomputable def N (F : ℂ → ℂ) (T1 T2 : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ zerosIn F T1 T2, mult F ρ

/-- Source: "N_d(T_1,T_2):=#{ρ:T_1<γ≤T_2} (distinct zeros)". Finite set, so `ncard` is
the true cardinality. -/
noncomputable def Nd (F : ℂ → ℂ) (T1 T2 : ℝ) : ℕ := (zerosIn F T1 T2).ncard

/-- Source: "N_0^*(T_1,T_2):=#{ρ:T_1<γ≤T_2, β=1/2} (distinct zeros on the critical line)". -/
noncomputable def N0star (F : ℂ → ℂ) (T1 T2 : ℝ) : ℕ :=
  {ρ ∈ zerosIn F T1 T2 | ρ.re = 1 / 2}.ncard

/-- Source: "N_0^s(T_1,T_2):=#{ρ:T_1<γ≤T_2, β=1/2, m_ρ=1} (simple zeros on the critical line)". -/
noncomputable def N0s (F : ℂ → ℂ) (T1 T2 : ℝ) : ℕ :=
  {ρ ∈ zerosIn F T1 T2 | ρ.re = 1 / 2 ∧ mult F ρ = 1}.ncard

/-- Source: "write also N_0 for the zeros on the line counted with multiplicity". -/
noncomputable def N0 (F : ℂ → ℂ) (T1 T2 : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ ∈ zerosIn F T1 T2 | ρ.re = 1 / 2}, mult F ρ

/-- Encoding of "A(T) ≥ (c − o(1)) B(T) as T → ∞": for every ε > 0 there is T₀ such that for
all T ≥ T₀, A(T) ≥ (c − ε) B(T). This is equivalent to the existence of a function
`f = o(1)` with `A T ≥ (c − f T) B T` for all large T. -/
def AtLeast (c : ℝ) (A B : ℝ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → ((c - ε) * (B T : ℝ) ≤ (A T : ℝ))

/-- Rate version for the cumulative range (0,T): the error `o(1)` is replaced by
`C · log log T / log T` for some constant `C`, for all large T. -/
def AtLeastRate (c : ℝ) (A B : ℝ → ℕ) : Prop :=
  ∃ C : ℝ, ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T →
    ((c - C * (Real.log (Real.log T) / Real.log T)) * (B T : ℝ) ≤ (A T : ℝ))

/-- Source: "c_MT^{−1}:=1/2+(1/√2)cot(1/√2)". -/
noncomputable def cMTinv : ℝ := 1 / 2 + (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2)

/-- Source: Theorem 1 (i): N_0^s(T,2T) ≥ (2/3−o(1)) N(T,2T) for ζ. -/
theorem reading_1i :
    AtLeast (2 / 3) (fun T => N0s riemannZeta T (2 * T)) (fun T => N riemannZeta T (2 * T)) := by
  sorry

/-- Source: Theorem 1 (ii): N_d(T,2T) ≥ (5/6−o(1)) N(T,2T) for ζ. -/
theorem reading_1ii :
    AtLeast (5 / 6) (fun T => Nd riemannZeta T (2 * T)) (fun T => N riemannZeta T (2 * T)) := by
  sorry

/-- Source: with the Montgomery–Taylor window the constants are `2 − c_MT^{−1}` (0.6725...)
for (i) and `(1/2)(3 − c_MT^{−1})` (0.83625...) for (ii). -/
theorem reading_1_MT :
    AtLeast (2 - cMTinv) (fun T => N0s riemannZeta T (2 * T))
        (fun T => N riemannZeta T (2 * T)) ∧
    AtLeast ((1 / 2) * (3 - cMTinv)) (fun T => Nd riemannZeta T (2 * T))
        (fun T => N riemannZeta T (2 * T)) := by
  sorry

/-- Source: "A fortiori N_0^*(T,2T) ≥ (2/3−o(1))N(T,2T)". -/
theorem reading_1_afortiori :
    AtLeast (2 / 3) (fun T => N0star riemannZeta T (2 * T))
        (fun T => N riemannZeta T (2 * T)) := by
  sorry

/-- Source: "The same holds for (0,T) in place of (T,2T), with rate O(log log T/log T)." -/
theorem reading_cumulative :
    AtLeastRate (2 / 3) (fun T => N0s riemannZeta 0 T) (fun T => N riemannZeta 0 T) ∧
    AtLeastRate (5 / 6) (fun T => Nd riemannZeta 0 T) (fun T => N riemannZeta 0 T) := by
  sorry

/-- Source: Theorem 2: Theorem 1 verbatim for L(s,χ), any fixed primitive Dirichlet character. -/
theorem reading_2 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    AtLeast (2 / 3) (fun T => N0s (DirichletCharacter.LFunction χ) T (2 * T))
        (fun T => N (DirichletCharacter.LFunction χ) T (2 * T)) ∧
    AtLeast (5 / 6) (fun T => Nd (DirichletCharacter.LFunction χ) T (2 * T))
        (fun T => N (DirichletCharacter.LFunction χ) T (2 * T)) := by
  sorry

/-- Source: "the proportion of non-trivial zeros proved on the critical line raised from
41.6% to 67.2%". Read literally: zeros of ζ on the line (with multiplicity) make up at least
67.2% (asymptotically) of all nontrivial zeros (with multiplicity) in (0,T]. -/
theorem reading_headline :
    AtLeast (672 / 1000) (fun T => N0 riemannZeta 0 T) (fun T => N riemannZeta 0 T) := by
  sorry

/-
AMBIGUITIES AND CHOICES
1. Nontrivial zero = zero with 0 < Re < 1 (open strip); no appeal to the functional equation.
2. Multiplicity = (analyticOrderAt F ρ).toNat; finite and ≥ 1 at all zeros in the strip.
3. Ordinates: only γ > 0 (T1 ≥ 0, T1 < γ ≤ T2), as in the source; for L(s,χ) the zeros with
   negative ordinate are therefore not counted (they are not symmetric to positive ones).
4. "≥ (c − o(1)) X as T→∞": ∀ ε>0 ∃ T0 ∀ T ≥ T0, (c−ε)·X ≤ A. Multiplicative form; no
   division, so no issue if X were 0 (it is positive for large T).
5. "Rate O(log log T / log T)" is applied to the (0,T) statements only, as
   (c − C·loglogT/logT) with some constant C and all T ≥ T0; the rate is taken to be the
   error in the constant (not an extra factor).
6. reading_cumulative: both N_0^s and N_d, with N(0,T) as comparison, constants 2/3, 5/6.
7. c_MT^{-1} taken exactly as displayed: 1/2 + (1/√2)·cot(1/√2) (the source's "..." continuation
   is not used); Real.cot is cos/sin. Numerical values 0.6725/0.83625 not asserted separately.
8. Montgomery–Taylor statement only for the (T,2T) range, for ζ.
9. Theorem 2: χ : DirichletCharacter ℂ q, q ≠ 0, IsPrimitive; includes q = 1 (then L = ζ).
   "fixed" is a ∀ outside the asymptotics. Mathlib's LFunction is the entire/meromorphic
   continuation (pole at 1 only for trivial χ, outside the strip). Only (i), (ii) with
   constants 2/3, 5/6 (not the MT constants).
10. Headline: "proportion of nontrivial zeros" read as zeros counted with multiplicity on the
   line, N_0, over N, on (0,T], with asymptotic lower bound 0.672 (=67.2%); other readings
   (distinct zeros, liminf, lower density over T) are not used. "Proved" is not formalized
   (the statement is just the mathematical claim); the 41.6% prior record is not stated.
11. a fortiori: only the N_0^* case, for ζ on (T,2T).
-/

end Reading
