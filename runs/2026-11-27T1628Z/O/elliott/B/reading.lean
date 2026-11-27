import Mathlib

open Filter Topology Complex

namespace ReaderB

/-- Liouville function λ(n) = (-1)^Ω(n), as a complex number. -/
noncomputable def liouville (n : ℕ) : ℂ := (-1 : ℂ) ^ (ArithmeticFunction.cardFactors n)

/-- Multiplicative f : ℕ → 𝔻 : modulus ≤ 1 and f(mn) = f(m) f(n) for coprime positive m, n. -/
def IsMultUnit (f : ℕ → ℂ) : Prop :=
  (∀ n, ‖f n‖ ≤ 1) ∧ ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → f (m * n) = f m * f n

/-- D(f, χ n^{it}; X)^2 = ∑_{p ≤ X} (1 - Re(f(p) conj(χ(p)) p^{it})) / p. -/
noncomputable def distSq (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (X + 1)).filter Nat.Prime,
    (1 - (f p * (starRingEnd ℂ) (χ (p : ZMod q)) * (p : ℂ) ^ ((t : ℂ) * Complex.I)).re) / (p : ℝ)

/-- The distance D (nonnegative square root of a nonnegative sum). -/
noncomputable def dist' (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) : ℝ :=
  Real.sqrt (distSq f χ t X)

/-- Uniformly nonpretentious: for every fixed Dirichlet character χ,
inf_{|t| ≤ N} D(f, χ n^{it}; N) → ∞. -/
def UniformlyNonpretentious (f : ℕ → ℂ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    Tendsto (fun N : ℕ => ⨅ t : Set.Icc (-(N : ℝ)) (N : ℝ), dist' f χ t N) atTop atTop

/-- Theorem 1.1. -/
theorem readingThm1_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ a₁ a₂ b₁ b₂ : ℕ, 1 ≤ a₁ → 1 ≤ a₂ →
      (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0 →
      ∃ C : ℝ, ∀ X : ℝ, 3 ≤ X →
        ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, liouville (a₁ * n + b₁) * liouville (a₂ * n + b₂)‖
          ≤ C * (X / Real.log X ^ c) := sorry

/-- Theorem 1.2 (binary corrected Elliott). -/
theorem readingThm1_2 (f₁ f₂ : ℕ → ℂ) (h₁ : IsMultUnit f₁) (h₂ : IsMultUnit f₂)
    (hunp : UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂)
    (h₁' h₂' : ℕ) (hne : h₁' ≠ h₂') :
    Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N, f₁ (n + h₁') * f₂ (n + h₂'))
      atTop (𝓝 0) := sorry

/-- Corollary 1.3 (affine correlations). -/
theorem readingCor1_3 (f₁ f₂ : ℕ → ℂ) (h₁ : IsMultUnit f₁) (h₂ : IsMultUnit f₂)
    (hunp : UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂)
    (a₁ a₂ b₁ b₂ : ℕ) (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂)
    (hdet : (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0) :
    Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N, f₁ (a₁ * n + b₁) * f₂ (a₂ * n + b₂))
      atTop (𝓝 0) := sorry

/-
Ambiguities and choices.
* Ω(n): `ArithmeticFunction.cardFactors` (prime factors with multiplicity); λ(n) = (-1)^Ω(n) in ℂ.
* Thm 1.1: c absolute (quantified before the forms), C depends on (a₁,a₂,b₁,b₂) and is a real
  (no sign constraint needed). X real, ≥ 3, so log X > 0 and the real power X/(log X)^c is
  well defined (rpow with positive base, no junk). The sum is over 1 ≤ n ≤ X via ⌊X⌋₊.
  Nonvanishing a₁b₂ - a₂b₁ ≠ 0 is stated in ℤ (casts first), so no ℕ subtraction.
  a_i ≥ 1, b_i ≥ 0 as naturals; arguments a n + b ≥ 1 so λ is never evaluated at 0.
* Multiplicative: literal reading (coprime positive m,n). f(0) is unconstrained apart from
  |f(0)| ≤ 1 and never used in sums (arguments n+h ≥ 1). I do not require f 1 = 1
  (text doesn't; coprime case forces f 1 ∈ {0,1}). f : ℕ → 𝔻 encoded as ‖f n‖ ≤ 1.
* Dirichlet characters: `DirichletCharacter ℂ q` for every modulus q ≠ 0 (NeZero q);
  χ(p) = χ (p : ZMod q) (zero when gcd(p,q)>1). p^{it} = (p:ℂ)^(t*I) (complex cpow, p ≥ 2 so
  no 0^0 issue). Conjugation is `starRingEnd ℂ`.
* D: distSq is sum over primes p ≤ X of (1 - Re(...))/p; each summand is ≥ 0 since |f|≤1,
  |χ|≤1, |p^{it}|=1, so sqrt is of a nonnegative number. Division by p ≥ 2 never by zero.
  Cutoff X is a natural number N (the text uses real X ≥ 2 in general, but (eq:unp) only
  uses N → ∞ through naturals, so no loss). For N=0,1 the sum is empty (value 0); irrelevant
  for the limit.
* Uniform nonpretentiousness: iInf over the subtype Icc(-N,N) of reals, which is nonempty
  and bounded below by 0 (bounded, indeed a continuous function on a compact set, so the inf is a
  genuine min); no empty/unbounded inf. "Tends to ∞" is `Tendsto … atTop atTop` in ℝ.
  "Prime cutoff and the height bound are the same N" is respected.
* Thm 1.2: h₁ ≠ h₂ naturals (≥ 0). Average is (1/N)·sum with N:ℕ cast to ℂ; N = 0 gives the
  junk 1/0 = 0 but only affects one term, not the limit. Hypothesis "at least one satisfies
  (eq:unp)" is the disjunction. Limit is Tendsto atTop (𝓝 0).
* Cor 1.3: same, with the determinant condition in ℤ.
* Not formalized: Prop affine-progression, quantitative Liouville distance bound (not in the read
  text).
-/

end ReaderB
