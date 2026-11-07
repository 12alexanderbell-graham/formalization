import Mathlib
import Work.Hiemenz.HiemenzBlind
import Work.Hiemenz.Hiemenz

/-!
# Hiemenz shooting events: the blind restatement, closed

The blind restater's `Blind.Hiemenz.blind_under` and `blind_over` (run 2026-11-07T2028Z: a quadruple
f, f1, f2, f3 with derivatives within [0, 7.5] and the equation f3 + f f2 + 1 − f1² = 0 pointwise)
follow from the program's frozen `Work.Hiemenz.hiemenz_under` and `hiemenz_over` with S = 7.5.
The blind `blind_exists` is closed once `Work.Hiemenz.hiemenz_exists` is proved.
-/

namespace Work.Hiemenz.BlindClosed
open Set Filter Topology

theorem under_closed (f f1 f2 f3 : ℝ → ℝ)
    (h : Blind.Hiemenz.HiemenzODE (Icc 0 7.5) f f1 f2 f3)
    (h0 : f 0 = 0) (h1 : f1 0 = 0) (h2 : f2 0 = 1.2325876568) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 7.5 ∧ f2 η < 0 ∧ ∀ s ∈ Icc 0 η, f1 s < 1 := by
  obtain ⟨hf, hp, hq, he⟩ := h
  obtain ⟨η, hη, k1, k2⟩ := Work.Hiemenz.hiemenz_under 7.5 (by norm_num) f f1 f2 hf hp
    (fun t ht => (hq t ht).congr_deriv (by linear_combination he t ht)) h0 h1 h2
  exact ⟨η, hη.1, by linarith [hη.2], k1, k2⟩

theorem over_closed (f f1 f2 f3 : ℝ → ℝ)
    (h : Blind.Hiemenz.HiemenzODE (Icc 0 7.5) f f1 f2 f3)
    (h0 : f 0 = 0) (h1 : f1 0 = 0) (h2 : f2 0 = 1.2325876569) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 7.5 ∧ 1 < f1 η ∧ ∀ s ∈ Icc 0 η, 0 < f2 s := by
  obtain ⟨hf, hp, hq, he⟩ := h
  obtain ⟨η, hη, k1, k2⟩ := Work.Hiemenz.hiemenz_over 7.5 (by norm_num) f f1 f2 hf hp
    (fun t ht => (hq t ht).congr_deriv (by linear_combination he t ht)) h0 h1 h2
  exact ⟨η, hη.1, by linarith [hη.2], k1, k2⟩

end Work.Hiemenz.BlindClosed
