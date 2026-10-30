import Mathlib

/-!
# Blind restatement of Eq. (A2) of Capozziello–Cardone–Salzano, arXiv:0802.1583v2, App. A

Source (verbatim, App. A): with H = ȧ/a, q = -(1/a) ä H⁻², j = (1/a) a⁽³⁾ H⁻³,
s = (1/a) a⁽⁴⁾ H⁻⁴, l = (1/a) a⁽⁵⁾ H⁻⁵ (subscript 0 = value at t₀),
  a(t)/a(t₀) = 1 + H₀(t−t₀) − (q₀/2)H₀²(t−t₀)² + … + (l₀/5!)H₀⁵(t−t₀)⁵ + O[(t−t₀)⁶]   (A1)
  1 + z = a(t₀)/a(t),   D = c (t₀ − t*),
  "Solving with respect to D up to the fifth order in z":
  D(z) = (c z / H₀) [D⁰ + D¹ z + D² z² + D³ z³ + D⁴ z⁴]                           (A2)
with D⁴ = 1 + 2q₀ + 3q₀² + (5/2)q₀³ + (7/2)q₀⁴ − (5/3)q₀j₀ − (7/8)q₀²j₀ − j₀ + j₀²/12
          − (1/8)q₀s₀ − s₀/6 − l₀/120.

All definitions below are my own (no repo imports).
-/

open Filter Topology Asymptotics Polynomial

noncomputable section

namespace Blind

/-! ## Cosmographic definitions (paper's Eq. (1)) -/

/-- Hubble parameter H(t) = ȧ/a.  Choice: `deriv` (Lean's derivative; junk 0 if not
differentiable, but all claims below assume smoothness at t₀). -/
def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- Generic n-th cosmographic ratio (1/a)(dⁿa/dtⁿ) H⁻ⁿ. -/
def cosmo (n : ℕ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  iteratedDeriv n a t / a t / (hubble a t) ^ n

/-- Deceleration q = −(1/a) ä H⁻² (note the minus sign, as in the source). -/
def decel (a : ℝ → ℝ) (t : ℝ) : ℝ := - cosmo 2 a t
/-- Jerk j = (1/a) a⁽³⁾ H⁻³. -/
def jerk (a : ℝ → ℝ) (t : ℝ) : ℝ := cosmo 3 a t
/-- Snap s = (1/a) a⁽⁴⁾ H⁻⁴. -/
def snap (a : ℝ → ℝ) (t : ℝ) : ℝ := cosmo 4 a t
/-- Lerk l = (1/a) a⁽⁵⁾ H⁻⁵. -/
def lerk (a : ℝ → ℝ) (t : ℝ) : ℝ := cosmo 5 a t

/-- Redshift of light emitted at t and received at t₀:  z = a(t₀)/a(t) − 1. -/
def redshift (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := a t₀ / a t - 1

/-- Light-travel ("physical") distance D = c (t₀ − t*) for emission at t*. -/
def dist (c t₀ tStar : ℝ) : ℝ := c * (t₀ - tStar)

/-! ## The printed coefficients D⁰_z … D⁴_z of (A2) -/

def D0 (_q _j _s _l : ℝ) : ℝ := 1
def D1 (q _j _s _l : ℝ) : ℝ := -(1 + q / 2)
def D2 (q j _s _l : ℝ) : ℝ := 1 + q + q ^ 2 / 2 - j / 6
def D3 (q j s _l : ℝ) : ℝ :=
  -(1 + 3 / 2 * q + 3 / 2 * q ^ 2 + 5 / 8 * q ^ 3 - 1 / 2 * j - 5 / 12 * q * j - s / 24)
/-- D⁴_z exactly as printed (q₀⁴ coefficient 7/2). -/
def D4 (q j s l : ℝ) : ℝ :=
  1 + 2 * q + 3 * q ^ 2 + 5 / 2 * q ^ 3 + 7 / 2 * q ^ 4 - 5 / 3 * q * j - 7 / 8 * q ^ 2 * j
    - j + j ^ 2 / 12 - 1 / 8 * q * s - s / 6 - l / 120

/-- The bracket of (A2): D⁰ + D¹ z + D² z² + D³ z³ + D⁴ z⁴. -/
def bracket (q j s l z : ℝ) : ℝ :=
  D0 q j s l + D1 q j s l * z + D2 q j s l * z ^ 2 + D3 q j s l * z ^ 3 + D4 q j s l * z ^ 4

/-- Right-hand side of (A2): (c z / H₀) · bracket. -/
def A2rhs (c H₀ q j s l z : ℝ) : ℝ := c * z / H₀ * bracket q j s l z

/-! ## Reading R1 (primary): analytic, O(z⁶) remainder, two-sided limit t* → t₀

Choices:
* Quantifiers: for every scale factor `a`, every expansion point t₀ ("present"), every c > 0.
  The paper's formula is meant to be universal in the cosmological model (cosmography is
  model-independent), so ∀ a.
* Smoothness: `ContDiffAt ℝ 6 a t₀`. (A1) carries an O[(t−t₀)⁶] remainder, which is what
  Taylor's theorem gives for C⁶; C⁶ at t₀ is the minimal natural hypothesis making the O(z⁶)
  remainder in (A2) true.
* a(t₀) > 0 (scale factor positive) and H₀ > 0 (expanding universe today; the source divides by
  H₀ and treats D, z > 0 for past emission).
* "D(z)" is not given an explicit inverse; I state it parametrically along the emission time
  t*: D(t*) − (c z(t*)/H₀)·bracket(z(t*)) = O(z(t*)⁶) as t* → t₀. Since z(t*) ~ H₀(t₀−t*) with
  H₀ ≠ 0, t* ↦ z is a local C⁶ diffeomorphism, so this is equivalent to the statement about the
  inverse function D(z) as z → 0, and it is exactly the paper's procedure ("inserting
  t* = t₀ − D/c into (A1)").
* "Up to the fifth order in z": the right side contains z¹…z⁵, so the remainder is O(z⁶).
* Limit: t* → t₀ two-sided (𝓝 t₀). The inversion is a formal power-series identity, valid on
  both sides; the physical past-only version is R1' below.
-/
def BlindClaim : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ c : ℝ),
    ContDiffAt ℝ 6 a t₀ → 0 < a t₀ → 0 < hubble a t₀ → 0 < c →
    (fun tStar => dist c t₀ tStar
        - A2rhs c (hubble a t₀) (decel a t₀) (jerk a t₀) (snap a t₀) (lerk a t₀)
            (redshift a t₀ tStar))
      =O[𝓝 t₀] (fun tStar => (redshift a t₀ tStar) ^ 6)

/-- Reading R1' (physical direction of time): emission strictly in the past, t* → t₀⁻,
so z → 0⁺.  Weaker than R1. -/
def BlindClaim_past : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ c : ℝ),
    ContDiffAt ℝ 6 a t₀ → 0 < a t₀ → 0 < hubble a t₀ → 0 < c →
    (fun tStar => dist c t₀ tStar
        - A2rhs c (hubble a t₀) (decel a t₀) (jerk a t₀) (snap a t₀) (lerk a t₀)
            (redshift a t₀ tStar))
      =O[𝓝[<] t₀] (fun tStar => (redshift a t₀ tStar) ^ 6)

/-- Reading R2 ("fifth-order accurate"): only C⁵ assumed (the cosmographic parameters up to
l₀ need only five derivatives), remainder o(z⁵). Weaker conclusion, weaker hypothesis. -/
def BlindClaim_littleO : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ c : ℝ),
    ContDiffAt ℝ 5 a t₀ → 0 < a t₀ → 0 < hubble a t₀ → 0 < c →
    (fun tStar => dist c t₀ tStar
        - A2rhs c (hubble a t₀) (decel a t₀) (jerk a t₀) (snap a t₀) (lerk a t₀)
            (redshift a t₀ tStar))
      =o[𝓝 t₀] (fun tStar => (redshift a t₀ tStar) ^ 5)

/-! ## Reading R3 (purely algebraic / formal power series)

The content that actually depends on the printed numbers: with x = H₀D/c and t − t₀ = −x/H₀,
(A1) gives 1/(1+z) = A(x) + O(x⁶) where
  A(x) = 1 − x − (q₀/2)x² − (j₀/6)x³ + (s₀/24)x⁴ − (l₀/120)x⁵.
(A2) claims x = z·P(z) + O(z⁶) with P the bracket. Formally: (1+z)·A(z·P(z)) ≡ 1 (mod z⁶),
for all real q₀, j₀, s₀, l₀.  (Any smooth a realises arbitrary (q₀,j₀,s₀,l₀), so R1 ⇔ R3.) -/

/-- The truncated (A1) in x = H₀ D / c, with t − t₀ = −x/H₀. -/
def A1poly (q j s l : ℝ) : ℝ[X] :=
  1 - X - C (q / 2) * X ^ 2 - C (j / 6) * X ^ 3 + C (s / 24) * X ^ 4 - C (l / 120) * X ^ 5

/-- The bracket of (A2) as a polynomial in z. -/
def bracketPoly (q j s l : ℝ) : ℝ[X] :=
  C (D0 q j s l) + C (D1 q j s l) * X + C (D2 q j s l) * X ^ 2 + C (D3 q j s l) * X ^ 3
    + C (D4 q j s l) * X ^ 4

def BlindClaim_formal : Prop :=
  ∀ q j s l : ℝ, ∀ k : ℕ, k ≤ 5 →
    ((1 + X) * (A1poly q j s l).comp (X * bracketPoly q j s l)).coeff k
      = if k = 0 then 1 else 0

/-! ## For the audit: the same claim with my sympy-derived D⁴ (q₀⁴ coefficient 7/8).
Sympy (C3_blind_sympy.py) finds derived − printed = −(21/8) q₀⁴; all other terms of D⁴ and all
of D⁰…D³ agree. I expect `BlindClaim`, `BlindClaim_past`, `BlindClaim_littleO`,
`BlindClaim_formal` to be FALSE as printed (counterexample: q₀ ≠ 0, e.g. matter-dominated
a ∝ t^{2/3}, where exact z⁵ coefficient of H₀D/c is 231/128 but printed gives 63/32). -/

def D4_derived (q j s l : ℝ) : ℝ :=
  1 + 2 * q + 3 * q ^ 2 + 5 / 2 * q ^ 3 + 7 / 8 * q ^ 4 - 5 / 3 * q * j - 7 / 8 * q ^ 2 * j
    - j + j ^ 2 / 12 - 1 / 8 * q * s - s / 6 - l / 120

def bracketPoly_derived (q j s l : ℝ) : ℝ[X] :=
  C (D0 q j s l) + C (D1 q j s l) * X + C (D2 q j s l) * X ^ 2 + C (D3 q j s l) * X ^ 3
    + C (D4_derived q j s l) * X ^ 4

def BlindClaim_formal_corrected : Prop :=
  ∀ q j s l : ℝ, ∀ k : ℕ, k ≤ 5 →
    ((1 + X) * (A1poly q j s l).comp (X * bracketPoly_derived q j s l)).coeff k
      = if k = 0 then 1 else 0

/-- Expected verdict on the printed claim (statement only). -/
theorem not_BlindClaim_formal : ¬ BlindClaim_formal := by
  sorry

theorem blindClaim_formal_corrected : BlindClaim_formal_corrected := by
  sorry

end Blind
