import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
/-!
# Geometric coefficient bounds from a recurrence (run 2026-11-26T1628Z)

The certificate of the H₂⁺ route computes finitely many coefficients of each series over ℚ and bounds the rest
by induction from the recurrence (`runs/2026-11-26T1628Z/scripts/h2p_emulate.py`, `frob_tail`, `step_basis`).
`geom_bound`: if |bₙ₊₄| ≤ α|bₙ₊₃| + β|bₙ₊₂| + γ|bₙ₊₁| + δ|bₙ| for every n ≥ N, with α q³ + β q² + γ q + δ ≤ q⁴
(q > 0, all coefficients ≥ 0), and |bⱼ| ≤ C qʲ for j ≤ N + 3, then |bₙ| ≤ C qⁿ for every n. A recurrence with
fewer terms takes the missing coefficients zero.
-/

namespace Work.Quantum.GeomBound

theorem geom_bound {b : ℕ → ℝ} {C q α β γ δ : ℝ} {N : ℕ} (hq : 0 < q)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (hrec : ∀ n, N ≤ n → |b (n + 4)| ≤ α * |b (n + 3)| + β * |b (n + 2)| + γ * |b (n + 1)| + δ * |b n|)
    (hchar : α * q ^ 3 + β * q ^ 2 + γ * q + δ ≤ q ^ 4)
    (hstart : ∀ j, j ≤ N + 3 → |b j| ≤ C * q ^ j) :
    ∀ n, |b n| ≤ C * q ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n ≤ N + 3
    · exact hstart n hn
    · push Not at hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hm : N ≤ m := by omega
      have h3 := ih (m + 3) (by omega)
      have h2 := ih (m + 2) (by omega)
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      have hC : 0 ≤ C := by
        have := hstart 0 (by omega)
        simp only [pow_zero, mul_one] at this
        exact le_trans (abs_nonneg _) this
      calc |b (m + 4)| ≤ α * |b (m + 3)| + β * |b (m + 2)| + γ * |b (m + 1)| + δ * |b m| := hrec m hm
        _ ≤ α * (C * q ^ (m + 3)) + β * (C * q ^ (m + 2)) + γ * (C * q ^ (m + 1)) + δ * (C * q ^ m) := by
          gcongr
        _ = C * q ^ m * (α * q ^ 3 + β * q ^ 2 + γ * q + δ) := by ring
        _ ≤ C * q ^ m * q ^ 4 := by
          gcongr
        _ = C * q ^ (m + 4) := by ring

end Work.Quantum.GeomBound
