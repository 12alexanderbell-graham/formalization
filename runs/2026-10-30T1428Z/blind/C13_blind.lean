import Mathlib

/-!
# Blind restatement: Bamba–Capozziello–Nojiri–Odintsov (2012), Sec. XI, Eqs. (11.1)–(11.31)

Source: K. Bamba, S. Capozziello, S. Nojiri, S. D. Odintsov, "Dark energy cosmology: the
equivalent description via different theoretical models and cosmography tests",
Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421v3, pp. 112–121.

Written from the typeset source alone (no repository cosmology definitions used).

## Source conventions
* `κ² = 1`, `R = −6(Ḣ + 2H²)` (11.6) (note the sign: `R < 0` for de Sitter), `' = d/dR`.
* (11.1)+(11.2): `H² = (1/3)[ρ_M/F′(R) + ρ_curv]`,
  `ρ_curv = (1/F′(R))[(F(R) − R F′(R))/2 − 3 H Ṙ F″(R)]`, `ρ_M = 3 H₀² Ω_M a⁻³`.
* (11.5) master equation: `Ḣ = −(1/(2F′(R)))[3H₀²Ω_M a⁻³ + R̈ F″(R) + Ṙ(Ṙ F‴(R) − H F″(R))]`.
  (The print has a doubled `+ +`; read as a single `+`.)
* (11.17)/(11.22) `F′(R₀) = 1`; (11.19) cubic Taylor truncation of `F` about `R₀`, hence
  `F⁽⁴⁾(R₀) = 0`.
* Cosmography (10.1)–(10.5): `q = −ä a/ȧ²`, `j = a⃛ a²/ȧ³`, `s = a⁽⁴⁾a³/ȧ⁴`, `l = a⁽⁵⁾a⁴/ȧ⁵`
  at `t₀`; the source normalises `a(t₀) = 1` (it writes `ρ_M = ρ_M(t₀) a⁻³`).

## Modelling choices
1. **Unknowns.** `a : ℝ → ℝ` (scale factor), `F : ℝ → ℝ` (the gravity Lagrangian `F(R)`),
   real numbers `t₀, H₀, Ω, q, j, s, l`.  Time derivatives are `deriv`/`iteratedDeriv`.
2. **No junk divisions.** The field equations are stated multiplied through by `3F′` resp.
   `2F′` (equivalent to the printed form wherever `F′ ≠ 0`, in particular near `t₀` since
   `F′(R₀) = 1`).  The cosmographic parameters are introduced by the multiplied-out
   relations `a⁽ⁿ⁾(t₀) = (±) x H₀ⁿ` (using `a(t₀) = 1`, `ȧ(t₀) = H₀`), not by quotients.
   `a⁻³` is written `1 / a t ^ 3`; it is only used where `a > 0` (near `t₀`, by continuity).
   The printed (11.21) divides by `𝓡`; we add the hypothesis `𝓡 ≠ 0` (the source tacitly
   needs it) so that `x / 𝓡` is never the Lean junk value `x / 0 = 0`.
3. **Where the equations hold.** The source says (11.1), (11.5) hold "along the full
   evolutionary history".  We only assume them on a neighbourhood of `t₀` (`∀ᶠ t in 𝓝 t₀`).
   This is all the derivation uses (values at `t₀` and one time derivative of (11.5) at
   `t₀`), it makes the claimed implication *stronger*, and it avoids vacuity: a global
   hypothesis `a > 0` on all of `ℝ` would exclude every model with a Big Bang (e.g. ΛCDM).
4. **Regularity.** `a` is `C⁶` on `ℝ` (only `C⁵` is needed for `d³R/dt³`).  `F` is exactly its
   cubic Taylor polynomial about `R₀` (11.19), as the source "sets"; this gives `F⁽⁴⁾ ≡ 0`
   (the source only uses `F⁽⁴⁾(R₀) = 0`).  We do *not* assume the Taylor form only
   approximately: the closure step genuinely needs `F⁽⁴⁾(R₀) = 0`.
5. **(11.13)** is a pure kinematic statement: it needs only the cosmographic set-up, not the
   field equations, so it is stated under `Cosmo` alone.
6. **Typography of (11.31).** `𝓡` is transcribed verbatim, including its last bracket
   `(3q⁴ + 34q³ + 246q + 104)` (no `q²` term).  `Ω_M` in (11.21) is `Ω_M^{(0)}`.
   The `H` without subscript in the second term of (11.20) is read as `H₀`.

## Blind verdict (see `C13_blind_sympy.out`)
* (11.10)–(11.12): correct.  (11.13): **wrong sign** of `2(q₀+4)j₀`:
  correct `d³R₀/dt³ = −6H₀⁵[l₀ − s₀ − 2(q₀+4)j₀ − 6(3q₀+8)q₀ − 24]`
  (correct − printed `= 24 H₀⁵ j₀ (q₀+4)`).
* (11.18)/(11.20): the `Ḣ Ṙ F″` term has the wrong sign (exact d/dt of (11.5) has `−Ḣ Ṙ`).
* With the *exact* derivative, `P₀, Q₀, P₂, Q₂, P₃, Q₃` agree with (11.25)–(11.30) exactly,
  but the common denominator does **not** agree with (11.31):
  `𝓡_derived − 𝓡_printed = −2(3j₀²q₀ + 10j₀² + 11j₀q₀² + 4j₀q₀ + 90q₀²)`.
  With the printed `𝓡`, (11.21) fails the paper's own ΛCDM check (11.40); with `𝓡_derived`
  it passes (`F(R₀) = R₀ + 2Λ`, `F″ = F‴ = 0`).
-/

open Filter Topology

namespace Blind.C13

noncomputable section

/-! ### Kinematics -/

/-- Hubble parameter `H(t) = ȧ/a`. -/
def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- Scalar curvature in the source's sign convention (11.6): `R = −6(Ḣ + 2H²)`. -/
def ricci (a : ℝ → ℝ) (t : ℝ) : ℝ := -6 * (deriv (hubble a) t + 2 * hubble a t ^ 2)

/-- Cosmographic set-up at `t₀` (10.1)–(10.5) with `a(t₀) = 1`; quotients multiplied out. -/
structure Cosmo (a : ℝ → ℝ) (t₀ H₀ q j s l : ℝ) : Prop where
  smooth : ContDiff ℝ 6 a
  a_t₀ : a t₀ = 1
  H₀_def : deriv a t₀ = H₀            -- `H₀ = ȧ(t₀)/a(t₀)` with `a(t₀) = 1`
  H₀_pos : 0 < H₀
  q_def : iteratedDeriv 2 a t₀ = -q * H₀ ^ 2   -- `q₀ = −ä a/ȧ²`
  j_def : iteratedDeriv 3 a t₀ = j * H₀ ^ 3    -- `j₀ = a⃛ a²/ȧ³`
  s_def : iteratedDeriv 4 a t₀ = s * H₀ ^ 4    -- `s₀ = a⁽⁴⁾ a³/ȧ⁴`
  l_def : iteratedDeriv 5 a t₀ = l * H₀ ^ 5    -- `l₀ = a⁽⁵⁾ a⁴/ȧ⁵`

/-! ### (a) The model setting of (11.21)–(11.24) -/

/-- Model setting under which the source derives (11.21)–(11.24):
cosmography at `t₀`, (11.1)+(11.2) and (11.5) near `t₀` (multiplied by `3F′`, `2F′`),
`F′(R₀) = 1` (11.17), and `F` equal to its cubic Taylor polynomial about `R₀` (11.19). -/
structure Setting (a F : ℝ → ℝ) (t₀ H₀ Ω q j s l : ℝ) : Prop extends Cosmo a t₀ H₀ q j s l where
  /-- (11.19): third-order Taylor truncation about `R₀ = R(t₀)`. -/
  F_cubic : ∀ x, F x = F (ricci a t₀) + deriv F (ricci a t₀) * (x - ricci a t₀)
      + iteratedDeriv 2 F (ricci a t₀) / 2 * (x - ricci a t₀) ^ 2
      + iteratedDeriv 3 F (ricci a t₀) / 6 * (x - ricci a t₀) ^ 3
  /-- (11.17)/(11.22): `F′(R₀) = 1`. -/
  F'_one : deriv F (ricci a t₀) = 1
  /-- (11.1)+(11.2), times `3F′(R)`, with `ρ_M = 3H₀²Ω a⁻³`, holding near `t₀`. -/
  friedmann : ∀ᶠ t in 𝓝 t₀,
      3 * deriv F (ricci a t) * hubble a t ^ 2
        = 3 * H₀ ^ 2 * Ω / a t ^ 3
          + (F (ricci a t) - ricci a t * deriv F (ricci a t)) / 2
          - 3 * hubble a t * deriv (ricci a) t * iteratedDeriv 2 F (ricci a t)
  /-- (11.5) master equation, times `2F′(R)`, holding near `t₀`. -/
  master : ∀ᶠ t in 𝓝 t₀,
      2 * deriv F (ricci a t) * deriv (hubble a) t
        = -(3 * H₀ ^ 2 * Ω / a t ^ 3
            + iteratedDeriv 2 (ricci a) t * iteratedDeriv 2 F (ricci a t)
            + deriv (ricci a) t * (deriv (ricci a) t * iteratedDeriv 3 F (ricci a t)
                - hubble a t * iteratedDeriv 2 F (ricci a t)))

/-! ### Printed polynomials (11.25)–(11.31), verbatim -/

/-- (11.25) -/
def P0 (q j s l : ℝ) : ℝ :=
  (j - q - 2) * l - (3 * s + 7 * j + 6 * q ^ 2 + 41 * q + 22) * s
    - ((3 * q + 16) * j + 20 * q ^ 2 + 64 * q + 12) * j
    - (3 * q ^ 4 + 25 * q ^ 3 + 96 * q ^ 2 + 72 * q + 20)

/-- (11.26) -/
def Q0 (q j s l : ℝ) : ℝ :=
  (q ^ 2 - j * q + 2 * q) * l
    + (3 * q * s + (4 * q + 6) * j + 6 * q ^ 3 + 44 * q ^ 2 + 22 * q - 12) * s
    + (2 * j ^ 2 + (3 * q ^ 2 + 10 * q - 6) * j + 17 * q ^ 3 + 52 * q ^ 2 + 54 * q + 36) * j
    + 3 * q ^ 5 + 28 * q ^ 4 + 118 * q ^ 3 + 72 * q ^ 2 - 76 * q - 64

/-- (11.27) -/
def P2 (q j s : ℝ) : ℝ := 9 * s + 6 * j + 9 * q ^ 2 + 66 * q + 42

/-- (11.28) -/
def Q2 (q j s : ℝ) : ℝ :=
  -(6 * (q + 1) * s + (2 * j - 2 * (1 - q)) * j + 6 * q ^ 3 + 50 * q ^ 2 + 74 * q + 32)

/-- (11.29) -/
def P3 (q j s l : ℝ) : ℝ := 3 * l + 3 * s - 9 * (q + 4) * j - (45 * q ^ 2 + 78 * q + 12)

/-- (11.30) -/
def Q3 (q j s l : ℝ) : ℝ :=
  -(2 * (1 + q) * l + 2 * (j + q) * s - (2 * j + 4 * q ^ 2 + 12 * q + 6) * j
    - (30 * q ^ 3 + 84 * q ^ 2 + 78 * q + 24))

/-- (11.31), verbatim (note: no `q₀²` term in the last bracket). -/
def Rcal (q j s l : ℝ) : ℝ :=
  (j - q - 2) * l - (3 * s - 2 * j + 6 * q ^ 2 + 50 * q + 40) * s
    + ((3 * q + 10) * j + 11 * q ^ 2 + 4 * q + 18) * j
    - (3 * q ^ 4 + 34 * q ^ 3 + 246 * q + 104)

/-! ### (b) Printed claim (11.13) -/

/-- **(11.13) as printed**: `d³R₀/dt³ = −6H₀⁵[l₀ − s₀ + 2(q₀+4)j₀ − 6(3q₀+8)q₀ − 24]`.
Blind verdict: FALSE whenever `j₀(q₀+4) ≠ 0` (sign of the `j₀` term). -/
def Claim_11_13 : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ H₀ q j s l : ℝ), Cosmo a t₀ H₀ q j s l →
    iteratedDeriv 3 (ricci a) t₀
      = -6 * H₀ ^ 5 * (l - s + 2 * (q + 4) * j - 6 * (3 * q + 8) * q - 24)

/-- Corrected (11.13) from the blind derivation (believed true; proof not attempted). -/
theorem claim_11_13_corrected (a : ℝ → ℝ) (t₀ H₀ q j s l : ℝ) (h : Cosmo a t₀ H₀ q j s l) :
    iteratedDeriv 3 (ricci a) t₀
      = -6 * H₀ ^ 5 * (l - s - 2 * (q + 4) * j - 6 * (3 * q + 8) * q - 24) := by
  sorry

/-! ### (c) Printed claim (11.21) -/

/-- **(11.21) as printed**, with `P₀, Q₀` of (11.25)–(11.26) and `𝓡` of (11.31):
`F(R₀)/(6H₀²) = −(P₀ Ω_M + Q₀)/𝓡`, under the model setting and `𝓡 ≠ 0`.
Blind verdict: FALSE (ΛCDM with `F(R) = R + 2Λ`, `Ω = 1/4` is a counterexample; see
`lcdm_quarter_printed` below). -/
def Claim_11_21 : Prop :=
  ∀ (a F : ℝ → ℝ) (t₀ H₀ Ω q j s l : ℝ), Setting a F t₀ H₀ Ω q j s l →
    Rcal q j s l ≠ 0 →
    F (ricci a t₀) / (6 * H₀ ^ 2) = -(P0 q j s l * Ω + Q0 q j s l) / Rcal q j s l

/-! ### Blind derivation: corrected denominator and ΛCDM arithmetic -/

/-- Denominator obtained by the blind sympy derivation (exact d/dt of (11.5)). -/
def RcalDerived (q j s l : ℝ) : ℝ :=
  (j - q - 2) * l - (3 * s - 2 * j + 6 * q ^ 2 + 50 * q + 40) * s
    - ((3 * q + 10) * j + 11 * q ^ 2 + 4 * q - 18) * j
    - (3 * q ^ 4 + 34 * q ^ 3 + 180 * q ^ 2 + 246 * q + 104)

theorem RcalDerived_sub_Rcal (q j s l : ℝ) :
    RcalDerived q j s l - Rcal q j s l
      = -2 * (3 * j ^ 2 * q + 10 * j ^ 2 + 11 * j * q ^ 2 + 4 * j * q + 90 * q ^ 2) := by
  unfold RcalDerived Rcal; ring

/-- Corrected (11.21) (believed true for generic data; proof not attempted).  The derivation
solves a 2×2 linear system for `F″(R₀), F‴(R₀)` whose determinant is `∝ (j₀−q₀−2)·𝓡_derived`.
In the degenerate case `j₀ = q₀ + 2` (`Ṙ₀ = 0`) the sympy script checks that the formula still
agrees with the value forced by (11.14)–(11.15) when `R̈₀ ≠ 0`; the sub-case `Ṙ₀ = R̈₀ = 0`
was not analysed, so a proof may need the extra hypothesis `j₀ − q₀ − 2 ≠ 0`. -/
def Claim_11_21_corrected : Prop :=
  ∀ (a F : ℝ → ℝ) (t₀ H₀ Ω q j s l : ℝ), Setting a F t₀ H₀ Ω q j s l →
    RcalDerived q j s l ≠ 0 →
    F (ricci a t₀) / (6 * H₀ ^ 2) = -(P0 q j s l * Ω + Q0 q j s l) / RcalDerived q j s l

/-- ΛCDM values (11.39) at `Ω = 1/4`: `q₀ = −5/8, j₀ = 1, s₀ = −1/8, l₀ = 83/32`.
The target (11.40) is `F(R₀)/(6H₀²) = (R₀ + 2Λ)/(6H₀²) = (Ω − 2)/2 = −7/8`.
The printed formula gives `18531/400856` instead. -/
theorem lcdm_quarter_printed :
    -(P0 (-5/8) 1 (-1/8) (83/32) * (1/4) + Q0 (-5/8) 1 (-1/8) (83/32))
        / Rcal (-5/8) 1 (-1/8) (83/32) = 18531 / 400856 := by
  unfold P0 Q0 Rcal; norm_num

theorem lcdm_quarter_derived :
    -(P0 (-5/8) 1 (-1/8) (83/32) * (1/4) + Q0 (-5/8) 1 (-1/8) (83/32))
        / RcalDerived (-5/8) 1 (-1/8) (83/32) = -7 / 8 := by
  unfold P0 Q0 RcalDerived; norm_num

end

end Blind.C13
