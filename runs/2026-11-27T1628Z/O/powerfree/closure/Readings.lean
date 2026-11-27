import Mathlib

/-! # Target O, family powerfree (O57): the three blind readings of run 2026-11-27T1628Z (brief 5dfa7d5), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


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
