import Mathlib

open NumberField

/-- ζ has no zero in Re s > σ₀. The junk value at the pole s = 1 is avoided by excluding s = 1. -/
def ReadingZeta (σ₀ : ℝ) : Prop :=
  ∀ s : ℂ, σ₀ < s.re → s ≠ 1 → riemannZeta s ≠ 0

/-- Sep 30 reading: EVERY Dirichlet character χ mod N (N ≥ 1), imprimitive allowed, extended by zero
on nonunits (this is Mathlib's `DirichletCharacter`).  The only allowed pole is s = 1 for the
trivial character (mod N); for every other χ the point s = 1 is included in the claim
(Mathlib's `LFunction` is the entire continuation for χ ≠ 1). -/
def ReadingDirichlet (σ₀ : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    σ₀ < s.re → (χ ≠ 1 ∨ s ≠ 1) → χ.LFunction s ≠ 0

/-- Oct 5 reading: only primitive characters. -/
def ReadingDirichletPrim (σ₀ : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, σ₀ < s.re → (χ ≠ 1 ∨ s ≠ 1) → χ.LFunction s ≠ 0

/-- The field Q(√-3) = Q(ζ₃), and its ring of integers. -/
abbrev QsqrtNeg3 : Type := CyclotomicField 3 ℚ
abbrev OK : Type := 𝓞 QsqrtNeg3

/-- A finite-order Hecke character modulo a nonzero integral ideal `𝔣` of `OK`:
a character of the ray class group mod 𝔣 (K imaginary quadratic, so no real conditions),
extended by zero to ideals not coprime to 𝔣.  Ray class group = I(𝔣)/P_{𝔣,1}; every class has an
integral representative, so a character is encoded as a multiplicative function `toFun` on
nonzero integral ideals coprime to 𝔣 (which extends uniquely to fractional ideals coprime to 𝔣),
trivial on P_{𝔣,1}: principal ideals (α), α ≡ 1 mod^× 𝔣, i.e. α = a/b with a,b ∈ OK nonzero,
coprime to 𝔣, a - b ∈ 𝔣; this says exactly toFun (a) = toFun (b). -/
structure HeckeChar (𝔣 : Ideal OK) where
  toFun : Ideal OK → ℂ
  map_one : toFun ⊤ = 1
  map_mul : ∀ 𝔞 𝔟 : Ideal OK, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → toFun (𝔞 * 𝔟) = toFun 𝔞 * toFun 𝔟
  eq_zero_of_not_coprime : ∀ 𝔞 : Ideal OK, 𝔞 ≠ ⊥ → 𝔞 ⊔ 𝔣 ≠ ⊤ → toFun 𝔞 = 0
  trivial_on_principal : ∀ a b : OK, a ≠ 0 → b ≠ 0 →
    Ideal.span {a} ⊔ 𝔣 = ⊤ → Ideal.span {b} ⊔ 𝔣 = ⊤ → a - b ∈ 𝔣 →
    toFun (Ideal.span {a}) = toFun (Ideal.span {b})
  finite_order : ∃ n : ℕ, 0 < n ∧ ∀ 𝔞 : Ideal OK, 𝔞 ≠ ⊥ → 𝔞 ⊔ 𝔣 = ⊤ → toFun 𝔞 ^ n = 1

/-- The principal (trivial) character: value 1 on every ideal coprime to 𝔣. -/
def HeckeChar.IsPrincipal {𝔣 : Ideal OK} (η : HeckeChar 𝔣) : Prop :=
  ∀ 𝔞 : Ideal OK, 𝔞 ≠ ⊥ → 𝔞 ⊔ 𝔣 = ⊤ → η.toFun 𝔞 = 1

/-- Terms of `∑_{𝔞 ≠ 0} η(𝔞) N𝔞^{-s}`; `N𝔞 = |OK/𝔞|` is a positive natural number, so the
complex power and the division are harmless. -/
noncomputable def HeckeChar.term {𝔣 : Ideal OK} (η : HeckeChar 𝔣) (s : ℂ)
    (𝔞 : {I : Ideal OK // I ≠ ⊥}) : ℂ :=
  η.toFun 𝔞.1 / ((Ideal.absNorm 𝔞.1 : ℕ) : ℂ) ^ s

/-- Every finite-order Hecke L-function over Q(√-3) has no zero in Re s > σ₀.
Quantified over every `F` holomorphic off 1 and equal to the Dirichlet series for Re s > 1
(stated by `HasSum`, avoiding `tsum`; the series converges absolutely for Re s > 1 since η is
bounded by 1 on the coprime ideals and the Dedekind zeta series converges there; such F is unique
by the identity theorem).  Zero-freeness is claimed for s ≠ 1, and also at s = 1 whenever F is
continuous there (which for an actual L-function happens iff η is non-principal, the principal
case having a pole). -/
def ReadingHecke (σ₀ : ℝ) : Prop :=
  ∀ (𝔣 : Ideal OK), 𝔣 ≠ ⊥ → ∀ (η : HeckeChar 𝔣) (F : ℂ → ℂ),
    DifferentiableOn ℂ F {1}ᶜ →
    (∀ s : ℂ, 1 < s.re → HasSum (η.term s) (F s)) →
    ∀ s : ℂ, σ₀ < s.re → (s ≠ 1 ∨ ContinuousAt F 1) → F s ≠ 0

theorem reading_sep30 :
    ReadingHecke (7/8) ∧ ReadingDirichlet (7/8) ∧ ReadingZeta (7/8) := sorry

theorem reading_oct5 :
    ReadingHecke (11/12) ∧ ReadingDirichletPrim (11/12) ∧ ReadingZeta (11/12) := sorry

/-
AMBIGUITIES AND CHOICES
1. Zeta: Mathlib's riemannZeta is total; s = 1 is excluded (pole/junk).
2. Dirichlet characters. Sep 30: "For a Dirichlet character χ modulo q, extended by zero on nonunits"
   and "every Dirichlet L-function" -> all characters mod every N (ReadingDirichlet), imprimitive
   included. Oct 5: "For a primitive Dirichlet character χ of conductor q" and "for every
   primitive character" -> ReadingDirichletPrim. (Mathematically equivalent in effect, since
   imprimitive L-functions differ by finitely many Euler factors with zeros only on Re s = 0, but
   the formal statements differ.) The Oct 5 text says only "every Dirichlet L-function" in the
   theorem; I read it via its definition as primitive.
   Pole: only trivial χ at s = 1 is excluded. For trivial χ mod N > 1 Mathlib's LFunction is the
   zeta times Euler factors, also with a pole at 1.
3. Hecke: ray class group modelled literally as I(𝔣)/P_{𝔣,1} via integral representatives (see
   docstring); change: characters are functions on integral ideals rather than on fractional
   ideals (equivalent, unique extension). The ideal 𝔣 = ⊤ (conductor 1) is allowed; the zero ideal
   is excluded. Q(√-3) is modelled as CyclotomicField 3 ℚ. The conductor is any modulus, not
   necessarily the conductor (imprimitive characters allowed), in both manuscripts' "modulo 𝔣".
   The identification of "meromorphic continuation" is by quantifying over F; at s = 1, F is
   arbitrary a priori, so I only claim F 1 ≠ 0 under ContinuousAt F 1.
   The convergence of the Dirichlet series is not asserted; HasSum is a hypothesis on F.
4. "No zero in Re s > σ₀" is strict inequality in both; boundary not included (Sep 30 says so).

HEADLINE DIFFERENCES
 Sep 30: "all finite-order Hecke L-functions over Q(√-3) and all Dirichlet L-functions are zero-free
 in the half-plane Re s > 7/8, with the principal pole at s=1 allowed." (Theorem: "Every
 finite-order Hecke L-function over F has no zero in Re s>7/8. The same holds for every Dirichlet
 L-function, including ζ(s).")
 Oct 5: "every Dirichlet L-function, including Riemann's zeta function, has no zeros in the
 half-plane Re s>11/12. More generally, ... every finite-order Hecke L-function over K"; Theorem:
 "no zeros in the half-plane Re s>11/12."
 Differences: constant 7/8 vs 11/12 (7/8 is the STRONGER claim: a smaller half-plane threshold excludes more zeros; 11/12 is weaker); Sep 30 defines
 Dirichlet characters mod q generally, Oct 5 primitive ones; Oct 5 does not mention the pole at
 s = 1 allowance; Oct 5 adds the claim that Landau-Siegel zeros are ruled out; Sep 30 says the
 boundary and the exceptional zeros in (7/8,1) are excluded.
-/
