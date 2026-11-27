import Mathlib

/-!
Blind reading (reader A) of O57, "Squarefree values of quartics and power-free values of
polynomials": Theorem 1.1 and Corollary 1.2 of the introduction.
-/

namespace ReaderA

open Polynomial Filter Asymptotics

/-- For an integer `k ≥ 2`, an integer `a` is `k`-power-free if no prime power `p^k`
divides `a`. Convention of the text: negative integers are allowed and zero is excluded. -/
def IsPowerFree (k : ℕ) (a : ℤ) : Prop :=
  a ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ^ k ∣ a)

/-- `ρ_f(q) = #{a ∈ ℤ/qℤ : f(a) ≡ 0 (mod q)}`, for `q ≥ 1`. The residue classes of `ℤ/qℤ`
are represented by `0, 1, …, q-1`. -/
noncomputable def rho (f : ℤ[X]) (q : ℕ) : ℕ := by
  classical
  exact ((Finset.range q).filter (fun a : ℕ => (q : ℤ) ∣ f.eval (a : ℤ))).card

/-- `S_{f,k}(X) = #{1 ≤ n ≤ X : f(n) is k-power-free}` for real `X`. -/
noncomputable def S (f : ℤ[X]) (k : ℕ) (X : ℝ) : ℕ := by
  classical
  exact ((Finset.Icc 1 ⌊X⌋₊).filter (fun n : ℕ => IsPowerFree k (f.eval (n : ℤ)))).card

/-- The local factor `1 - ρ_f(p^k) / p^k` (a real number; `p^k ≥ 1`, so no division by 0). -/
noncomputable def localFactor (f : ℤ[X]) (k p : ℕ) : ℝ :=
  1 - (rho f (p ^ k) : ℝ) / ((p : ℝ) ^ k)

/-- Partial Euler product `∏_{p < P, p prime} (1 - ρ_f(p^k)/p^k)`. -/
noncomputable def partialEulerProduct (f : ℤ[X]) (k P : ℕ) : ℝ := by
  classical
  exact ∏ p ∈ (Finset.range P).filter Nat.Prime, localFactor f k p

/-- `c` is the value of the Euler product `∏_p (1 - ρ_f(p^k)/p^k)`, i.e. the limit of the
partial products over the primes taken in increasing order. -/
def IsEulerProduct (f : ℤ[X]) (k : ℕ) (c : ℝ) : Prop :=
  Tendsto (fun P : ℕ => partialEulerProduct f k P) atTop (nhds c)

/-- The local admissibility condition (1.1): `ρ_f(p^k) < p^k` for every prime `p`. -/
def LocallyAdmissible (f : ℤ[X]) (k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → rho f (p ^ k) < p ^ k

/-- "`f` has no fixed prime `k`th-power divisor": there is no prime `p` such that `p^k`
divides `f(n)` for every integer `n`. -/
def NoFixedPrimePowerDivisor (f : ℤ[X]) (k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ ∀ n : ℤ, (p : ℤ) ^ k ∣ f.eval n

/-- **Theorem 1.1.** Let `f ∈ ℤ[x]` be irreducible over `ℚ`, of degree `d` with `4 ≤ d ≤ 8`,
and put `k = d - 2`. If (1.1) holds, then `S_{f,k}(X) = c_{f,k} X + o_f(X)` with
`c_{f,k} = ∏_p (1 - ρ_f(p^k)/p^k) > 0`. -/
theorem reading_thm_1_1 (f : ℤ[X]) (d k : ℕ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hdeg : f.natDegree = d) (hd4 : 4 ≤ d) (hd8 : d ≤ 8) (hk : k + 2 = d)
    (hloc : LocallyAdmissible f k) :
    ∃ c : ℝ, IsEulerProduct f k c ∧ 0 < c ∧
      (fun X : ℝ => (S f k X : ℝ) - c * X) =o[atTop] (fun X : ℝ => X) := sorry

/-- **Corollary 1.2.** Let `f ∈ ℤ[x]` be irreducible over `ℚ` of degree `d ≥ 4`, and put
`k = d - 2`. If `f` has no fixed prime `k`th-power divisor, then
`S_{f,k}(X) = c_{f,k} X + o_f(X)` with `c_{f,k} = ∏_p (1 - ρ_f(p^k)/p^k) > 0`. -/
theorem reading_cor_1_2 (f : ℤ[X]) (d k : ℕ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hdeg : f.natDegree = d) (hd4 : 4 ≤ d) (hk : k + 2 = d)
    (hfix : NoFixedPrimePowerDivisor f k) :
    ∃ c : ℝ, IsEulerProduct f k c ∧ 0 < c ∧
      (fun X : ℝ => (S f k X : ℝ) - c * X) =o[atTop] (fun X : ℝ => X) := sorry

end ReaderA

/-
Ambiguities and choices (reader A)
==================================

1. `k`-power-free. Literally "no prime power p^k divides a", with zero excluded and negative
   integers allowed (`IsPowerFree k a := a ≠ 0 ∧ ∀ p prime, ¬ p^k ∣ a`). Since `0` is excluded
   explicitly, the fact that every `p^k` divides `0` is not relied on.

2. `ρ_f(q)`. The text counts `a ∈ ℤ/qℤ` with `f(a) ≡ 0 (mod q)`. I count representatives
   `a ∈ {0, …, q-1}` with `q ∣ f(a)` in ℤ; this is the same number for `q ≥ 1`, and the
   function is only ever used at `q = p^k ≥ 2`. (Using `ZMod q` directly would need a
   `NeZero (p^k)` instance for a variable prime; the range version avoids it.)

3. `S_{f,k}(X)` with real `X`: `n` ranges over `1 ≤ n ≤ ⌊X⌋₊`. For `X < 1` the floor is `0`
   (or the range is empty), which is the correct count 0, so `⌊·⌋₊` is not a junk value here.

4. The Euler product. To avoid `tprod` of a possibly non-multipliable family, the product
   `∏_p` is read as the limit of the partial products over primes `p < P` as `P → ∞`
   (primes in increasing order, the usual meaning of an Euler product), and the theorem
   asserts that this limit EXISTS (`Tendsto … (nhds c)`), equals the constant `c` in the
   asymptotic, and is positive. Each factor `1 - ρ_f(p^k)/p^k` is a real division by
   `p^k ≥ 2`, so no `x/0` issue. The statement "`c_{f,k} = ∏ ... > 0`" is rendered as
   "∃ c, c is the Euler product ∧ 0 < c ∧ asymptotic with c".

5. `S_{f,k}(X) = c X + o_f(X)`: rendered as `S(X) - c X = o(X)` as `X → ∞` through the reals
   (`Asymptotics.IsLittleO` along `atTop` on ℝ). The subscript `f` only records that the
   error term may depend on the fixed `f` (the text says it is not uniform in `f`); since
   `f` is fixed before the `∃ c` and the little-o, this is automatic. No uniformity is claimed.

6. Irreducible over ℚ: `Irreducible (f.map (Int.castRingHom ℚ))` in `ℚ[X]`. No primitivity
   or sign condition on the leading coefficient is imposed, matching "No primitivity or sign
   condition on the leading coefficient is required". (Irreducibility over ℚ already forces
   `f` nonconstant.)

7. Degree: `f.natDegree = d`; with `f` irreducible over ℚ, `f ≠ 0`, so `natDegree` agrees
   with the degree and no junk value `natDegree 0 = 0` arises. `k = d - 2` is written
   `k + 2 = d` to avoid ℕ subtraction (with `d ≥ 4` both are the same).

8. Hypothesis of Theorem 1.1 is the local condition (1.1) `ρ_f(p^k) < p^k` for every prime p,
   as written. Hypothesis of Corollary 1.2 is worded differently in the text ("f has no fixed
   prime kth-power divisor"); I formalized that wording literally
   (`¬ ∃ prime p with p^k ∣ f(n) for all integers n`), rather than replacing it with (1.1).
   The text says (1.1) "says that no prime kth power divides every value of f", so the two
   are intended to be equivalent; I did not prove the equivalence. (Values at all integers n,
   not only positive n, are used; by periodicity mod p^k the two readings agree.)

9. Not formalized: the abstract's "together with Browning's theorem" (provenance only), the
   remarks about `x^4+2` and `x^4+1`, and the history section.
-/
