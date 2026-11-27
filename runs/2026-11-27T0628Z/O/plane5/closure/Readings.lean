import Mathlib

namespace ReaderA

/-!
Blind reading A, family O4 (plane5): "The Euclidean plane is not five-colorable".
Source: plane5/sources/introduction_lines1-75.tex, Theorem 1.1 (`thm:main`), lines 62-68,
with the definitions of lines 3-7.
-/

namespace Plane5ReadingA

/-- The Euclidean plane `ℝ²`, with the Euclidean (ℓ²) norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The colour set `{1, …, k}` of the source (line 4), taken literally as a subtype of `ℕ`. -/
abbrev Colors (k : ℕ) := Set.Icc (1 : ℕ) k

/-- Source lines 3-5: a proper `k`-coloring of the Euclidean plane is a function
`c : ℝ² → {1,…,k}` with `c x ≠ c y` whenever `‖x - y‖ = 1`.
No regularity (measurability etc.) is imposed on `c`. -/
def IsProperColoring (k : ℕ) (c : Plane → Colors k) : Prop :=
  ∀ x y : Plane, ‖x - y‖ = 1 → c x ≠ c y

/-- The plane admits a proper `k`-coloring (arbitrary colour classes). -/
def ProperlyColorable (k : ℕ) : Prop :=
  ∃ c : Plane → Colors k, IsProperColoring k c

/-- Source lines 5-6: `χ(ℝ²)` is "the least such `k`". Instead of a possibly-junk `sInf`/`Nat.find`,
we say what it means for a natural number `n` to *be* `χ(ℝ²)`: `n` admits a proper coloring and
no smaller `k` does. -/
def IsChromaticNumberOfPlane (n : ℕ) : Prop :=
  ProperlyColorable n ∧ ∀ k < n, ¬ ProperlyColorable k

/-- Theorem 1.1, first sentence: the Euclidean plane has no proper five-coloring, even when
arbitrary color classes are allowed. -/
theorem reading_thm_1_1_no_five_coloring : ¬ ProperlyColorable 5 := sorry

/-- Theorem 1.1, "Consequently, 6 ≤ χ(ℝ²) ≤ 7", in the junk-free form:
the least `k` admitting a proper `k`-coloring exists and lies in `[6, 7]`. -/
theorem reading_thm_1_1_bounds :
    ∃ n : ℕ, IsChromaticNumberOfPlane n ∧ 6 ≤ n ∧ n ≤ 7 := sorry

/-- The same consequence, unpacked into the two bounds with no reference to a "least" element:
`χ(ℝ²) ≥ 6` ⇔ no `k ≤ 5` works; `χ(ℝ²) ≤ 7` ⇔ some `k ≤ 7` works. -/
theorem reading_thm_1_1_bounds_unpacked :
    (∀ k ≤ 5, ¬ ProperlyColorable k) ∧ (∃ k ≤ 7, ProperlyColorable k) := sorry

/-- Cross-check against the source's "Equivalently" (lines 7-9): the chromatic number of the
unit-distance graph on all points of the plane, via Mathlib's `SimpleGraph.chromaticNumber`
(valued in `ℕ∞`, equal to `⊤` when no finite coloring exists, so no junk). -/
def unitDistanceGraph : SimpleGraph Plane :=
  -- `fromRel r` has `Adj x y ↔ x ≠ y ∧ (r x y ∨ r y x)`; for `r x y := ‖x - y‖ = 1` the extra
  -- conjuncts are automatic (unit distance forces `x ≠ y`, and `‖x - y‖ = ‖y - x‖`).
  SimpleGraph.fromRel fun x y => ‖x - y‖ = 1

theorem reading_thm_1_1_bounds_graph :
    6 ≤ unitDistanceGraph.chromaticNumber ∧ unitDistanceGraph.chromaticNumber ≤ 7 := sorry

end Plane5ReadingA

/-
AMBIGUITIES AND CHOICES (reader A)

1. "Euclidean plane" / `‖x-y‖`: modelled as `EuclideanSpace ℝ (Fin 2)`, whose norm is the
   Euclidean ℓ² norm. Deliberately NOT `ℝ × ℝ`, whose Mathlib norm is the sup norm (that would
   change the problem to unit sup-distance).

2. Colour set `{1,…,k}`: taken literally as `Set.Icc 1 k ⊆ ℕ` (a type with exactly k elements,
   empty for k = 0). Equivalent to `Fin k`; nothing depends on the labelling.

3. "even when arbitrary color classes are allowed": the coloring is an arbitrary function; no
   measurability, Borel, or regularity hypothesis. Lean's classical logic matches "working
   throughout in ZFC" (line 60); the statement is a plain existence/non-existence of functions.

4. χ(ℝ²) is "the least such k" (line 5-6). To avoid junk values (`sInf ∅ = 0`, or `Nat.find`
   needing an existence proof) I define the predicate `IsChromaticNumberOfPlane n` and state the
   consequence as "∃ n, n is χ(ℝ²) ∧ 6 ≤ n ≤ 7". This statement includes the existence of a finite
   coloring, which is part of the meaning of "χ(ℝ²) ≤ 7". I also give an unpacked form
   (∀ k ≤ 5 not colorable, ∃ k ≤ 7 colorable) and a Mathlib-graph form (`chromaticNumber : ℕ∞`)
   matching the source's "Equivalently, ... chromatic number of the graph ..." sentence.
   All three forms are equivalent given monotonicity of colorability in k (a k-coloring is a
   k'-coloring for k ≤ k'), which is elementary.

5. "Consequently": the bounds are presented as consequences of the first sentence. Since lower
   bounds for ≤ 5 colours follow from the no-5-coloring by monotonicity, χ ≥ 6 is genuinely a
   consequence; but χ ≤ 7 is NOT a consequence of the first sentence — it is the classical upper
   bound.

WHICH PARTS THE SOURCE PROVES AND WHICH IT CITES (from the excerpt only):
   * Proved (line 60 "We prove the following result"): the non-existence of a proper
     five-coloring with arbitrary colour classes (`reading_thm_1_1_no_five_coloring`). The lower
     bound χ ≥ 6 then follows by monotonicity.
   * Cited: the upper bound χ(ℝ²) ≤ 7, attributed to John Isbell's hexagonal coloring (lines 11-13,
     historical record in Soifer 2003; also in Hadwiger 1961, line 15-16). The excerpt does not
     indicate that the paper reproves it.
   * Cited background, not part of the theorem: lower bound 5 (de Grey 2018 and successors),
     de Bruijn–Erdős compactness (lines 32-34), Falconer's measurable bound χ_m ≥ 5 (lines 40-41),
     Moser spindle (lines 17-20, reused in the final step of the proof).
-/
end ReaderA

namespace ReaderB

/-- A proper `k`-coloring of the Euclidean plane: any function (no regularity) to `Fin k`
with different colors at distance exactly 1. -/
def IsProperColoring (k : ℕ) (c : EuclideanSpace ℝ (Fin 2) → Fin k) : Prop :=
  ∀ x y : EuclideanSpace ℝ (Fin 2), dist x y = 1 → c x ≠ c y

/-- The plane admits a proper `k`-coloring. -/
def PlaneColorable (k : ℕ) : Prop :=
  ∃ c : EuclideanSpace ℝ (Fin 2) → Fin k, IsProperColoring k c

/-- Theorem 1.1, first sentence (arbitrary color classes; no measurability). -/
theorem reading_plane_not_five_colorable : ¬ PlaneColorable 5 := sorry

/-- Theorem 1.1, consequence: χ(ℝ²) is the least `k` with `PlaneColorable k`; it exists and
lies in [6,7]. -/
theorem reading_chromatic_number_bounds :
    ∃ m : ℕ, IsLeast {k : ℕ | PlaneColorable k} m ∧ 6 ≤ m ∧ m ≤ 7 := sorry

/- Ambiguities / choices:
* ℝ² = EuclideanSpace ℝ (Fin 2), Euclidean norm; ‖x-y‖=1 rendered as dist x y = 1.
* Colors Fin k (k=0 gives no colorings, harmless). χ(ℝ²) defined as the least element of
  {k | PlaneColorable k}, stated by existence of an IsLeast witness (avoids sInf junk).
* "6 ≤ χ ≤ 7": the source's text says the upper bound 7 is Isbell's hexagonal coloring
  (cited, history; not proved in the excerpt) and the lower bound 4 / 5 are cited (Nelson,
  de Grey 2018 etc.). What the paper proves is "no proper 5-coloring" (hence ≥ 6), working in
  ZFC, using Moser spindle constraints and measurable-data arguments. The theorem as stated
  says "Consequently 6 ≤ χ ≤ 7", so the 7 part is a consequence relying on the cited Isbell
  coloring; my second theorem bundles both.
* The theorem does not need AC/measure; any function allowed (as formalized).
-/
end ReaderB

namespace ReaderC

/-! Reader C, family O4: "The Euclidean plane is not five-colorable" (Theorem 1.1, excerpt lines 1-75). -/

/-- The Euclidean plane ℝ². -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- `c : ℝ² → {0,…,k-1}` (i.e. `{1,…,k}` shifted) is a proper coloring: any two points at
unit distance receive different colors. No measurability is imposed on the color classes. -/
def IsProperColoring {k : ℕ} (c : Plane → Fin k) : Prop :=
  ∀ x y : Plane, dist x y = 1 → c x ≠ c y

/-- `k` colors suffice for the plane (no measurability). This replaces the junk-valued
`χ(ℝ²)`: the chromatic number is the least `k` with `Colorable k`, and statements about
`χ` are stated as statements about which `k` are `Colorable`. -/
def Colorable (k : ℕ) : Prop :=
  ∃ c : Plane → Fin k, IsProperColoring c

/-- Theorem 1.1, headline: no proper five-coloring of the plane, arbitrary color classes allowed.
Source: stated as the main theorem; the excerpt gives no proof text beyond the introduction. -/
theorem reading_no_proper_five_coloring : ¬ ∃ c : Plane → Fin 5, IsProperColoring c := sorry

/-- Theorem 1.1, consequence (lower bound): no `k ≤ 5` admits a proper coloring, i.e. `6 ≤ χ(ℝ²)`.
Source: "Consequently, 6 ≤ χ(ℝ²)". -/
theorem reading_chi_lower : ∀ k : ℕ, k < 6 → ¬ Colorable k := sorry

/-- Theorem 1.1, consequence (upper bound): seven colors suffice, i.e. `χ(ℝ²) ≤ 7`.
Source: the excerpt attributes the upper bound seven to Isbell (via the historical record in
Soifer2003History), i.e. it is cited, not proved in the excerpt. -/
theorem reading_chi_upper : Colorable 7 := sorry

/-!
## Ambiguity notes (reader C, O4)

1. Coloring codomain: the source uses `c : ℝ² → {1,…,k}`. I used `Fin k` (0-indexed). This is
   equivalent; no junk values arise (`Fin 0` is empty, and ℝ² is nonempty, so `Colorable 0` is false).
2. Unit distance: the source writes `‖x−y‖ = 1`. I used `dist x y = 1` on `EuclideanSpace ℝ (Fin 2)`,
   which is the Euclidean norm, so the two agree.
3. "Even when arbitrary color classes are allowed": I read this as the absence of any measurability
   hypothesis, so the headline is stated for all functions `c`. The measurable variant `χ_m`
   (Falconer, Payne) is not defined here because the headline does not need it.
4. χ(ℝ²) is not defined as a number. Following the brief, I express "6 ≤ χ ≤ 7" as
   `(∀ k < 6, ¬Colorable k) ∧ Colorable 7`. The lower bound is derived in the source from the
   five-color theorem by monotonicity (a `k`-coloring with `k ≤ 5` gives a 5-coloring); I did not
   formalize that step; `reading_chi_lower` states the consequence directly as a sorry claim.
5. Source boundaries: the excerpt is `introduction_lines1-75.tex`. It ends mid-footnote on the
   Reed2026 manuscript, so the proof of Theorem 1.1 is not in the excerpt. The excerpt cites:
   the upper bound seven (Isbell, via Soifer2003History), the compactness theorem (de Bruijn-Erdős),
   and the measurable/regular-region results (Falconer, Payne, Woodall, Townsend, SokolovVoronov2025).
   None of those are formalized here; the theorem is stated only as the claim.
6. The excerpt mentions a Moser-spindle step "in the final step of our proof"; no proof text is
   in the excerpt, so nothing from it is encoded.
7. The footnote about Reed2026 is a remark about another manuscript; it does not state a claim of
   this paper and is not encoded.
-/
end ReaderC
