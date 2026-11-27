import Mathlib

namespace ReaderB

open Filter Asymptotics Classical

/-- `a` is `k`-power-free: no prime power `p^k` divides `a` (so `0` is excluded, negatives allowed). -/
def IsKPowerFree (k : ℕ) (a : ℤ) : Prop := ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ^ k ∣ a)

/-- `ρ_f(q) = #{a ∈ ℤ/qℤ : f(a) ≡ 0 mod q}`. -/
noncomputable def rho (f : Polynomial ℤ) (q : ℕ) : ℕ :=
  Nat.card {a : ZMod q // (f.map (Int.castRingHom (ZMod q))).eval a = 0}

/-- `S_{f,k}(X) = #{1 ≤ n ≤ X : f(n) k-power-free}`, for real `X`. -/
noncomputable def S (f : Polynomial ℤ) (k : ℕ) (X : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊X⌋₊).filter (fun n : ℕ => IsKPowerFree k (f.eval (n : ℤ)))).card

/-- Local admissibility (1.1). -/
def LocallyAdmissible (f : Polynomial ℤ) (k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → rho f (p ^ k) < p ^ k

/-- The asymptotic claim, with the Euler product asserted convergent (`HasProd`) to `c > 0`. -/
def DensityStatement (f : Polynomial ℤ) (k : ℕ) : Prop :=
  ∃ c : ℝ, HasProd (fun p : Nat.Primes => 1 - (rho f (p ^ k) : ℝ) / ((p : ℕ) : ℝ) ^ k) c ∧
    0 < c ∧ (fun X : ℝ => (S f k X : ℝ) - c * X) =o[atTop] (fun X : ℝ => X)

/-- Theorem 1.1. -/
theorem readingTheorem11 (f : Polynomial ℤ) (d k : ℕ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hdeg : f.natDegree = d) (hd : 4 ≤ d ∧ d ≤ 8) (hk : k + 2 = d)
    (hloc : LocallyAdmissible f k) : DensityStatement f k := sorry

/-- Corollary 1.2. -/
theorem readingCorollary12 (f : Polynomial ℤ) (d k : ℕ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hdeg : f.natDegree = d) (hd : 4 ≤ d) (hk : k + 2 = d)
    (hno : ∀ p : ℕ, p.Prime → ¬ (∀ n : ℤ, ((p : ℤ) ^ k ∣ f.eval n))) :
    DensityStatement f k := sorry

end ReaderB

/-
Ambiguities and choices.
* k = d - 2 is encoded as hk : k + 2 = d (no ℕ subtraction). Degree d is f.natDegree (f irreducible so f ≠ 0
  and constants are excluded by d ≥ 4).
* "Irreducible over ℚ": Irreducible of the image in ℚ[x] (so primitive/content issues are as in the text:
  e.g. 2*(x^4+2) is reducible over ℤ-content-wise but irreducible over ℚ and is allowed; local admissibility
  then fails/holds as it may).
* ρ_f(q) via Nat.card of a subtype of ZMod q (finite, q = p^k ≥ 1 so ZMod q is Fin q; no junk).
* S_{f,k}(X): X real, count of naturals n with 1 ≤ n ≤ X, i.e. n ≤ ⌊X⌋₊ (X ≥ 0 the relevant range).
* k-power-free: ∀ primes p, ¬ p^k ∣ a over ℤ, exactly the text's convention (zero excluded, negatives included).
* Euler product: tprod avoided. The claim is HasProd of the family over Nat.Primes (unconditional
  multipliability in ℝ), with value c, plus 0 < c. This asserts convergence and avoids the tprod junk value 1.
  Since the factors are in [0,1], unconditional vs ordered-by-size convergence agree in value.
  The factors use real division by p^k > 0.
* o_f(X): Asymptotics.IsLittleO at atTop on real X; f is fixed, no uniformity.
* Corollary 1.2 hypothesis "no fixed prime k-th-power divisor": for all primes p, not every integer value f(n)
  is divisible by p^k (all n ∈ ℤ, equivalent to ρ_f(p^k) < p^k by periodicity). Kept as in the text rather
  than rewritten via ρ. The Theorem uses (1.1) literally via ρ.
* Same conclusion bundled as DensityStatement for both. "c_{f,k} = ∏…" is expressed as the existential c
  with HasProd c; equivalent.
-/
