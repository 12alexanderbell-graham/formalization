import Mathlib
import Readings.Doubling
import ComparatorChallenges.DoublingHilbert
import ComparatorChallenges.CompactBanach

/-! # Target O, family O27 (a doubling Hilbert subset with no finite-dimensional bi-Lipschitz embedding):
closures (run 2026-11-27T0628Z). Frozen statements taken with `type_of%`, never retyped: `DoublingHilbert.main`
(a subset of real ℓ₂, open-ball doubling with at most 76800 centres in the subset, no embedding into any ℝ^k,
k > 0, with scale a > 0 and distortion D ≥ 1) and `CompactBanach.main` (a universal Λ : ℕ and in every
infinite-dimensional real Banach space a compact Λ-doubling K with no such embedding into any finite-dimensional
real normed space; at universes 0, the readers'). Closed (frozen ⇒ reading): readers A and C, both theorems (their
open-ball doubling is the frozen one; an embedding with distortion D < 1 is one with distortion 1). Not closed:
reader B, both theorems — B reads "balls" as *closed* balls, and doubling with constant 76800 for closed balls is
not a consequence of the frozen open-ball statement; the source does not say which (reader A flagged that the
number may depend on it). -/

namespace TargetO.Doubling

/-- Frozen-style doubling gives reader A's/C's form. -/
theorem ball_cover {X : Type*} [MetricSpace X] {bound : ℕ}
    (h : ∀ x : X, ∀ r : ℝ, 0 < r → ∃ centers : Finset X, centers.card ≤ bound ∧
      ∀ y : X, dist y x < r → ∃ c ∈ centers, dist y c < r / 2)
    (x : X) (r : ℝ) : ∃ t : Finset X, (t.card : ℝ) ≤ bound ∧
      Metric.ball x r ⊆ ⋃ y ∈ t, Metric.ball y (r / 2) := by
  by_cases hr : 0 < r
  · obtain ⟨t, ht, hc⟩ := h x r hr
    refine ⟨t, by exact_mod_cast ht, fun y hy => ?_⟩
    obtain ⟨c, hc, hd⟩ := hc y hy
    exact Set.mem_biUnion hc hd
  · refine ⟨∅, by simp, fun y hy => ?_⟩
    have : dist y x < r := hy
    exact absurd (lt_of_le_of_lt dist_nonneg this) hr

/-- An embedding at distortion D gives one at distortion max D 1. -/
theorem no_embed {X V : Type*} [MetricSpace X] [NormedAddCommGroup V]
    (h : ¬ ∃ f : X → V, ∃ a : ℝ, 0 < a ∧ ∃ D : ℝ, 1 ≤ D ∧
      ∀ x y : X, a * dist x y ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ D * a * dist x y)
    (D : ℝ) (f : X → V) :
    ¬ ∃ a : ℝ, 0 < a ∧ ∀ x y : X, a * dist x y ≤ ‖f x - f y‖ ∧ ‖f x - f y‖ ≤ D * a * dist x y := by
  rintro ⟨a, ha, hf⟩
  refine h ⟨f, a, ha, max D 1, le_max_right _ _, fun x y => ?_⟩
  obtain ⟨h1, h2⟩ := hf x y
  rw [dist_eq_norm]
  refine ⟨h1, h2.trans ?_⟩
  have := mul_nonneg ha.le (dist_nonneg (x := x) (y := y))
  nlinarith [le_max_left D 1]

theorem A_thm : (type_of% @OAI.DoublingHilbert.main) → (type_of% @ReaderA.reading_thm_1_1) := by
  rintro ⟨S, hd, hn⟩
  refine ⟨S, fun x r _ => ?_, fun k hk D f => no_embed (hn k hk) D f⟩
  exact ball_cover hd x r

theorem C_thm : (type_of% @OAI.DoublingHilbert.main) →
    (type_of% @ReaderC.reading_thm_1_1_hilbert_subset) := by
  rintro ⟨S, hd, hn⟩
  refine ⟨S, fun x r => ?_, fun k hk f D => no_embed (hn k hk) D f⟩
  exact ball_cover hd x r

theorem A_banach : (type_of% @OAI.CompactBanach.main.{0, 0}) →
    (type_of% @ReaderA.reading_banach_compact_obstruction) := by
  rintro ⟨Λ, h⟩
  refine ⟨Λ, fun Y _ _ _ hY => ?_⟩
  obtain ⟨K, hK, hd, hn⟩ := h Y hY
  refine ⟨K, hK, fun x r _ => ?_, fun V _ _ _ D f => no_embed (hn V) D f⟩
  obtain ⟨t, ht, hc⟩ := ball_cover (bound := Λ) (fun x r hr => by
    obtain ⟨c, hc1, hc2⟩ := hd x r hr
    exact ⟨c, hc1, fun y hy => by simpa using hc2 y hy⟩) x r
  exact ⟨t, ht, hc⟩

theorem C_banach : (type_of% @OAI.CompactBanach.main.{0, 0}) →
    (type_of% @ReaderC.reading_thm_compact_banach_obstruction) := by
  rintro ⟨Λ, h⟩
  refine ⟨Λ, fun E _ _ _ hE => ?_⟩
  obtain ⟨K, hK, hd, hn⟩ := h E hE
  refine ⟨K, hK, fun x r => ?_, fun F _ _ hF f D => ?_⟩
  · exact ball_cover (bound := Λ) (fun x r hr => by
      obtain ⟨c, hc1, hc2⟩ := hd x r hr
      exact ⟨c, hc1, fun y hy => by simpa using hc2 y hy⟩) x r
  · exact no_embed (hn F) D f

end TargetO.Doubling

#print axioms TargetO.Doubling.A_thm
#print axioms TargetO.Doubling.C_thm
#print axioms TargetO.Doubling.A_banach
#print axioms TargetO.Doubling.C_banach
