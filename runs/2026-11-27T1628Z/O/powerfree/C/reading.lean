import Mathlib

/-
Blind reading C, target O, family O57 "Squarefree values of quartics and power-free values of polynomials".
Source read: abstract and 01-introduction.tex lines 1-42 and 110-120 only (as the brief lists).
-/

namespace ReaderC

open Filter Asymptotics Topology

/-- An integer a is k-power-free if no prime power p^k divides a. -/
def IsKPowerFree (k : ℕ) (a : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ^ k ∣ a)

/-- ρ_f(q) = #{a ∈ Z/qZ : f(a) ≡ 0 mod q}, via the reduction of f mod q. Used with q = p^k ≥ 2,
where ZMod q is finite, so Nat.card is the honest count. -/
noncomputable def rho (f : Polynomial ℤ) (q : ℕ) : ℕ :=
  Nat.card {a : ZMod q // (f.map (Int.castRingHom (ZMod q))).eval a = 0}

open Classical in
/-- S_{f,k}(X) = #{1 ≤ n ≤ X : f(n) is k-power-free}, for real X. -/
noncomputable def S (f : Polynomial ℤ) (k : ℕ) (X : ℝ) : ℝ :=
  (((Finset.Icc 1 ⌊X⌋₊).filter (fun n : ℕ => IsKPowerFree k (f.eval (n : ℤ)))).card : ℝ)

/-- Partial Euler products ∏_{p ≤ N prime} (1 - ρ_f(p^k)/p^k). The Euler product c_{f,k} is
defined as the limit of these partial products (no tprod). -/
noncomputable def eulerPartial (f : Polynomial ℤ) (k : ℕ) (N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range N).filter Nat.Prime,
    (1 - (rho f (p ^ k) : ℝ) / ((p : ℝ) ^ k))

/-- Theorem 1.1. Let f ∈ Z[x] be irreducible over Q of degree d with 4 ≤ d ≤ 8, put k = d - 2
(written as d = k + 2). If ρ_f(p^k) < p^k for every prime p, then the partial Euler products
converge to some c_{f,k} > 0 and S_{f,k}(X) = c_{f,k} X + o_f(X) as X → ∞. -/
theorem reading_O57_thm1
    (f : Polynomial ℤ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (k d : ℕ) (hd : f.natDegree = d) (hk : d = k + 2)
    (h4 : 4 ≤ d) (h8 : d ≤ 8)
    (hadm : ∀ p : ℕ, p.Prime → rho f (p ^ k) < p ^ k) :
    ∃ c : ℝ, Tendsto (eulerPartial f k) atTop (𝓝 c) ∧ 0 < c ∧
      (fun X : ℝ => S f k X - c * X) =o[atTop] (fun X : ℝ => X) := by
  sorry

/-- Corollary 1.2. Let f ∈ Z[x] be irreducible over Q of degree d ≥ 4, put k = d - 2 (written as
d = k + 2), and suppose f has no fixed prime k-th power divisor, i.e. for no prime p does
p^k divide f(n) for all n ∈ Z. Then the same conclusion holds. -/
theorem reading_O57_cor2
    (f : Polynomial ℤ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (k d : ℕ) (hd : f.natDegree = d) (hk : d = k + 2)
    (h4 : 4 ≤ d)
    (hnofix : ∀ p : ℕ, p.Prime → ¬ (∀ n : ℤ, (p : ℤ) ^ k ∣ f.eval n)) :
    ∃ c : ℝ, Tendsto (eulerPartial f k) atTop (𝓝 c) ∧ 0 < c ∧
      (fun X : ℝ => S f k X - c * X) =o[atTop] (fun X : ℝ => X) := by
  sorry

end ReaderC

/-
## Comment block: ambiguities and choices (reader C, O57)

1. k-power-free. "no prime power p^k divides a" is IsKPowerFree k a := for all primes p,
   ¬ (p^k ∣ a) in ℤ. Negative integers are covered. Zero is excluded automatically, since
   p^k divides 0; I did not add a separate a ≠ 0 clause, as it is implied.

2. ρ_f(q). Defined with Nat.card over ZMod q of the roots of f mod q (f reduced by
   Int.castRingHom). For q = p^k ≥ 2, ZMod q is finite, so Nat.card is the actual count and
   there is no junk value. The text uses q = p^k only, and the admissibility hypothesis is
   stated only for q = p^k.

3. S_{f,k}(X). The text leaves X real. I take X : ℝ, count n ∈ ℕ with 1 ≤ n ≤ X, i.e. Icc 1 ⌊X⌋₊,
   and f evaluated at n as an integer. Positive inputs only, as the text says. The counts are
   returned as ℝ. For X < 1 the count is 0; this is not a junk value, the count is genuinely empty.

4. Degree and k. The text's k = d - 2 is written as the hypothesis d = k + 2, avoiding ℕ
   subtraction. Degree is f.natDegree = d. Irreducibility over Q is
   Irreducible (f.map (Int.castRingHom ℚ)), which is the text's "irreducible over Q". The text does
   not require primitivity or a sign condition on the leading coefficient, so none is assumed.

5. Theorem 1.1 hypotheses. "4 ≤ d ≤ 8" is h4 and h8. The local condition
   eq. (1), ρ_f(p^k) < p^k for every prime p, is hadm. It is an admissibility hypothesis; the
   text's remark that it says no prime k-th power divides every value of f is commentary.

6. Corollary 1.2 hypothesis. "No fixed prime k-th power divisor" is read literally as: for no
   prime p does p^k divide f(n) for all n ∈ ℤ (hnofix). I checked that this is the same as
   ρ_f(p^k) < p^k for all p, which is hadm; both forms are written as the text gives them.
   The corollary has no degree upper bound, only d ≥ 4 (h4).

7. Euler product. c_{f,k} = ∏_p (1 - ρ_f(p^k)/p^k). Instead of tprod (avoided), the product is
   the limit of the partial products over primes p < N (eulerPartial). The claim is that this
   limit exists, equals c_{f,k}, and is > 0. Each factor is > 0 under the admissibility
   hypothesis. The partial product is over Finset.range N filtered by Nat.Prime. Existence of
   the limit is part of the claim, not assumed.

8. Asymptotic. S_{f,k}(X) = c X + o_f(X) is written as
   (fun X => S X - c * X) =o[atTop] (fun X => X). The o-constant may depend on f, as the text
   says; the statement quantifies over f, k, c in the outer context, so this is captured.

9. Not formalized: the text's error term is not asserted uniform in f, and I did not add a
   uniformity clause. The introduction's remarks on Eisenstein and cyclotomic examples
   (x^4 + 2, x^4 + 1) and the degree 5-8 excluded powers are commentary and are not stated as
   separate claims. The Browning reference in Corollary 1.2 is not formalized as a separate
   claim either, since the corollary's own statement is formalized.

10. Avoided: ℕ subtraction, tsum/tprod, sSup/sInf, ⊤/⊥, x/0 (ρ and q are ≥ 2 here).

Status: the file is written; compile status is reported in the handback.
-/
