import Mathlib

/-! # Target O, family logbm: the three blind readings of run 2026-11-27T1428Z (brief 7bfe069), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


/-!
Blind reading (reader A) of the introduction of
"Logarithmic and Lp Brunn–Minkowski inequalities": Theorem 1.1 and Corollary 1.2.
-/

namespace ReaderA

open MeasureTheory Metric
open scoped Pointwise

/-- The ambient space `ℝ^n`, with its Euclidean inner product and Lebesgue measure `volume`. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- "A convex body in `ℝ^n` is a compact convex set with nonempty interior." -/
def IsConvexBody {n : ℕ} (K : Set (Rn n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- Support function `h_K(u) = max_{x ∈ K} ⟨x, u⟩`.  Written as `sSup` of the image of `K`;
for a convex body `K` (compact, nonempty) the image is a nonempty compact subset of `ℝ`, so the
`sSup` is attained, i.e. it is the max.  Only values at `u ∈ S^{n-1}` are ever used. -/
noncomputable def supportFn {n : ℕ} (K : Set (Rn n)) (u : Rn n) : ℝ :=
  sSup ((fun x => inner ℝ x u) '' K)

/-- Wulff body `𝒲[f] = ⋂_{u ∈ S^{n-1}} {x ∈ ℝ^n : ⟨x, u⟩ ≤ f u}`.
`f` is given as a function on all of `ℝ^n`, but only its values on the unit sphere matter. -/
def wulff {n : ℕ} (f : Rn n → ℝ) : Set (Rn n) :=
  ⋂ u ∈ sphere (0 : Rn n) 1, {x | inner ℝ x u ≤ f u}

/-- Theorem 1.1 (even logarithmic Brunn–Minkowski inequality):
`|𝒲[h_K^{1-λ} h_L^λ]| ≥ |K|^{1-λ} |L|^λ`.
The conclusion also records that the left-hand volume is finite, so that `toReal` is faithful. -/
theorem reading_thm_1_1 (n : ℕ) (hn : 1 ≤ n) (K L : Set (Rn n))
    (hK : IsConvexBody K) (hL : IsConvexBody L) (hKs : K = -K) (hLs : L = -L)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    volume (wulff (fun u => supportFn K u ^ (1 - t) * supportFn L u ^ t)) ≠ ⊤ ∧
      (volume K).toReal ^ (1 - t) * (volume L).toReal ^ t ≤
        (volume (wulff (fun u => supportFn K u ^ (1 - t) * supportFn L u ^ t))).toReal := by
  sorry

/-- Corollary 1.2 (symmetric `L_p` Brunn–Minkowski inequality), `0 < p < 1`:
`|𝒲[((1-λ) h_K^p + λ h_L^p)^{1/p}]|^{p/n} ≥ (1-λ)|K|^{p/n} + λ|L|^{p/n}`. -/
theorem reading_cor_1_2 (n : ℕ) (hn : 1 ≤ n) (K L : Set (Rn n))
    (hK : IsConvexBody K) (hL : IsConvexBody L) (hKs : K = -K) (hLs : L = -L)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    volume (wulff (fun u => ((1 - t) * supportFn K u ^ p + t * supportFn L u ^ p) ^ (1 / p)))
        ≠ ⊤ ∧
      (1 - t) * (volume K).toReal ^ (p / n) + t * (volume L).toReal ^ (p / n) ≤
        (volume (wulff (fun u =>
          ((1 - t) * supportFn K u ^ p + t * supportFn L u ^ p) ^ (1 / p)))).toReal ^ (p / n) := by
  sorry

end ReaderA

/-!
## Ambiguities and choices (reader A)

* `ℝ^n` is `EuclideanSpace ℝ (Fin n)`, `⟨x,u⟩` is `inner ℝ x u`, `|K|` is Mathlib's `volume`
  (Lebesgue measure, transported from `Fin n → ℝ`). `S^{n-1}` is `Metric.sphere 0 1`.
* "convex body" = compact ∧ convex ∧ nonempty interior, exactly as the text defines it.
  `K = -K` uses pointwise negation of sets.  In Corollary 1.2, "full-dimensional
  origin-symmetric convex bodies" is read as the same hypotheses (full-dimensional is implied by
  nonempty interior); "origin-symmetric" is read as `K = -K`.
* The parameter `λ` is renamed `t` (`λ` is a Lean keyword); `0 ≤ t ≤ 1` as stated.  `n ≥ 1` is a
  hypothesis as stated.
* Support function: `max` is written as `sSup` of the image `{⟨x,u⟩ : x ∈ K}`.  Junk avoidance:
  under the hypotheses `K` is compact and nonempty, so this set is nonempty and bounded and the
  `sSup` is the attained maximum.  The function is defined on all `u`, but only `u ∈ S^{n-1}`
  enter (the Wulff body only looks at unit `u`).
* Wulff body: defined for any `f : ℝ^n → ℝ` by the displayed intersection over the unit sphere;
  the text's standing assumption "positive continuous function on the sphere" is not imposed in
  the definition.  It holds for the functions actually used (`h_K, h_L > 0` on the sphere for
  origin-symmetric bodies, as the text says), and is not added as a hypothesis since the theorem
  only applies `𝒲` to those functions.
* Real powers: `h_K^{1-λ}`, `h_L^λ`, `h^p`, `(…)^{1/p}` are `Real.rpow`.  Junk avoidance: bases
  are strictly positive on the sphere (support functions of symmetric bodies with nonempty
  interior, and positive combinations of positive powers of them), the only place they are
  evaluated in the Wulff body.  `|K|^{1-λ}`, `|L|^λ`, `|·|^{p/n}` are rpow of real volumes,
  which are strictly positive (nonempty interior).  `p/n` is real division with `n ≥ 1`, so no
  division by zero.
* Volumes: stated with `ENNReal.toReal`.  Junk avoidance: `volume K, volume L < ⊤` because
  compact sets have finite Lebesgue measure (`IsCompact.measure_lt_top`), so no extra hypothesis
  is needed; for the Wulff body the finiteness (`≠ ⊤`) is stated as an explicit conjunct of the
  conclusion (the text asserts the Wulff body is a convex body, hence bounded), so `toReal`
  can never silently turn `⊤` into `0`.
* Inequality direction: written as `rhs ≤ lhs`, equivalent to the text's `lhs ≥ rhs`.
* Corollary 1.2: `|𝒲[…]|^{p/n}` is the real volume raised to the real power `p/n`.
-/


open MeasureTheory

namespace ReaderB

/-- A convex body in `ℝⁿ`: compact, convex, nonempty interior. -/
def IsConvexBody {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- Support function `h_K(u) = max_{x ∈ K} ⟨x,u⟩`, written as `sSup` of the image
(for a convex body the image is nonempty, bounded, and the sup is attained). -/
noncomputable def supportFn {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun x => inner ℝ x u) '' K)

/-- Wulff body `⋂_{u ∈ S^{n-1}} {x | ⟨x,u⟩ ≤ f u}`. -/
def wulff {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  ⋂ u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, {x | inner ℝ x u ≤ f u}

/-- Theorem 1.1 (even logarithmic Brunn–Minkowski). Volumes are `(volume ·).toReal`. -/
theorem reading_thm_1_1 (n : ℕ) (hn : 1 ≤ n)
    (K L : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hKs : K = -K) (hLs : L = -L) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    (volume K).toReal ^ (1 - lam) * (volume L).toReal ^ lam ≤
      (volume (wulff (fun u => supportFn K u ^ (1 - lam) * supportFn L u ^ lam))).toReal := by
  sorry

/-- Corollary 1.2 (symmetric `L_p` Brunn–Minkowski), `0 < p < 1`. -/
theorem reading_cor_1_2 (n : ℕ) (hn : 1 ≤ n)
    (K L : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hKs : K = -K) (hLs : L = -L) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    (1 - lam) * (volume K).toReal ^ (p / n) + lam * (volume L).toReal ^ (p / n) ≤
      (volume (wulff (fun u =>
        ((1 - lam) * supportFn K u ^ p + lam * supportFn L u ^ p) ^ (1 / p)))).toReal ^ (p / n) := by
  sorry

/-
Ambiguities and choices.
* Ambient space: `EuclideanSpace ℝ (Fin n)`, with its Lebesgue `volume`; `n ≥ 1` as hypothesis `1 ≤ n`.
* Convex body = compact, convex, nonempty interior (as the text). `K = -K` stated as set equality with
  pointwise negation (`Set.neg`, in scope via `-K`).
* Support function: `sSup` of the image of K; harmless since K is compact nonempty (interior nonempty), so the
  set is nonempty and bounded. Only evaluated on the unit sphere by `wulff`; off the sphere it is irrelevant.
* Wulff body is defined for any `f : E → ℝ`; the text requires f positive continuous on the sphere, which holds
  for f built from symmetric bodies' support functions (positive since 0 is interior); not assumed as hypothesis
  since it is a consequence.
* Real powers: h_K(u), h_L(u) > 0 on the sphere (origin-symmetric body), so rpow of positive reals is fine.
  Off the sphere f is never read. `1/p` fine since p>0. |K|^{..}: volumes of convex bodies are positive and finite
  (compact, nonempty interior), so `toReal` loses nothing; the Wulff body lies in a ball of radius max h, so its
  volume is finite as well, hence `toReal` is faithful there too. In the corollary, `p/n` with n ≥ 1 cast to ℝ,
  no division by zero.
* The Corollary is written with `≤` flipped (RHS ≤ LHS), same as the text's `≥`. The text's "full-dimensional"
  is already part of IsConvexBody (nonempty interior).
* The even log-concave measure part (second half of abstract / Saroglou) is not part of the asked claims.
-/

end ReaderB


open MeasureTheory Metric

namespace ReaderC

/-- The ambient space `ℝ^n` with its Euclidean structure. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A convex body: compact, convex, with nonempty interior. -/
def IsConvexBody {n : ℕ} (K : Set (Rn n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- Origin-symmetric: `K = -K`. -/
def IsOriginSymmetric {n : ℕ} (K : Set (Rn n)) : Prop :=
  ∀ x : Rn n, x ∈ K ↔ -x ∈ K

/-- Support function `h_K(u) = max_{x ∈ K} ⟨x, u⟩`, as a supremum of the image. -/
noncomputable def supportFn {n : ℕ} (K : Set (Rn n)) (u : Rn n) : ℝ :=
  sSup ((fun x : Rn n => inner ℝ x u) '' K)

/-- Wulff body `W[f] = ⋂_{u ∈ S^{n-1}} {x : ⟨x, u⟩ ≤ f(u)}`. Only the values of `f`
on the unit sphere are used. -/
def wulff {n : ℕ} (f : Rn n → ℝ) : Set (Rn n) :=
  {x | ∀ u ∈ sphere (0 : Rn n) 1, inner ℝ x u ≤ f u}

/-- Theorem 1.1: the even logarithmic Brunn–Minkowski inequality. -/
theorem reading_theorem_1_1 (n : ℕ) (hn : 1 ≤ n) (K L : Set (Rn n))
    (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hKs : IsOriginSymmetric K) (hLs : IsOriginSymmetric L)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume (wulff (fun u => supportFn K u ^ (1 - t) * supportFn L u ^ t))).toReal
      ≥ (volume K).toReal ^ (1 - t) * (volume L).toReal ^ t := sorry

/-- Corollary 1.2: the symmetric `L_p` Brunn–Minkowski inequality for `0 < p < 1`. -/
theorem reading_corollary_1_2 (n : ℕ) (hn : 1 ≤ n) (K L : Set (Rn n))
    (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hKs : IsOriginSymmetric K) (hLs : IsOriginSymmetric L)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume (wulff (fun u =>
        ((1 - t) * supportFn K u ^ p + t * supportFn L u ^ p) ^ (1 / p)))).toReal ^ (p / (n : ℝ))
      ≥ (1 - t) * (volume K).toReal ^ (p / (n : ℝ))
        + t * (volume L).toReal ^ (p / (n : ℝ)) := sorry

/-!
## Ambiguities and choices

1. Parameter name: the text's interpolation parameter `λ` is written `t` (`λ` is a Lean keyword).
2. Ambient space: `ℝ^n` is `EuclideanSpace ℝ (Fin n)`; `n ≥ 1` is the hypothesis `hn`.
   `hn` is unused in the proofs of the statements (it is kept to match the text).
3. Convex body: compact, convex, nonempty interior (the text's definition). Origin-symmetric
   means `x ∈ K ↔ -x ∈ K` (the text's `K = -K`, written elementwise to avoid pointwise
   set-negation instances). With nonempty interior and symmetry, `0` lies in the interior,
   as the text claims; this is not needed as a separate hypothesis.
4. Support function: `h_K(u) = sSup {⟨x,u⟩ : x ∈ K}`. For a nonempty compact set this is a
   maximum, so `sSup` agrees with the text's `max`. No junk value arises because `K` is
   nonempty and bounded. It is evaluated only at unit vectors `u`.
5. Positivity of the base of every real power: for an origin-symmetric convex body and a
   unit vector `u`, `h_K(u) > 0` (the text's claim). So `h_K(u)^(1-t)`, `h_K(u)^p` and
   `(...)^(1/p)` are applied to positive numbers, and `Real.rpow` is the intended power on
   positive reals. The formulas are written for all `u`, but the Wulff body only reads them on
   the unit sphere, so the values off the sphere (where a base could be nonpositive) are unused.
6. Wulff body: the text requires `f` positive and continuous; for `f = h_K^(1-t) h_L^t` (or
   the `L_p` version) this holds, so no extra hypothesis is added. The set
   `{x | ∀ u ∈ sphere 0 1, ⟨x,u⟩ ≤ f u}` is the literal intersection of half-spaces.
7. Volume: Mathlib's `volume` on `EuclideanSpace` is Lebesgue measure, valued in `ℝ≥0∞`.
   I take `.toReal` of both sides, so the statement is real-valued. This is faithful because
   every body involved is finite-volume: `K`, `L` are compact, and the Wulff body is
   contained in a ball (text: it lies inside the ball of radius `max f`), so no `⊤` occurs.
   The `toReal` of `⊤` would be `0`, so the reading relies on this finiteness; it is
   not hidden by any hypothesis.
8. Real powers with base `0`: `volume K`, `volume L` are positive because the bodies have
   nonempty interior, so `0 ^ (1-t)` and `0 ^ t` (with `t = 0` or `1`) never occur. For
   `Real.rpow` with base `0` and exponent `0`, Lean gives `1`, and no such case arises.
9. Corollary 1.2: `full-dimensional` is the nonempty-interior clause of `IsConvexBody`. The
   exponent `p/n` uses `n` cast to `ℝ`, so there is no ℕ subtraction or division.
   `1 - t` is real subtraction, since `t : ℝ`. No ℕ-subtraction junk appears anywhere.
10. Division by `0`: none in the statement except `1 / p` and `p / n`, where `p > 0` and
   `n ≥ 1` (so `(n:ℝ) ≠ 0`) are given.
-/

end ReaderC
