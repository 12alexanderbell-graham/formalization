import Mathlib

open Filter Topology Complex

/-- Sign vectors of length `N` (real coefficients ±1). -/
def Signs (N : ℕ) : Type := {ε : Fin N → ℝ // ∀ k, ε k = 1 ∨ ε k = -1}

/-- The polynomial `∑ ε_k z^k`. -/
noncomputable def littlePoly {N : ℕ} (ε : Fin N → ℝ) (z : ℂ) : ℂ :=
  ∑ k : Fin N, (ε k : ℂ) * z ^ (k : ℕ)

/-- `‖P‖_∞ = max_{t ∈ ℝ/ℤ} |P(e(t))|`, taken as a sup over `t : ℝ` (1-periodic). -/
noncomputable def supNorm {N : ℕ} (ε : Fin N → ℝ) : ℝ :=
  ⨆ t : ℝ, ‖littlePoly ε (Complex.exp (2 * Real.pi * Complex.I * t))‖

/-- `m_N = min over signs of ‖P‖_∞ / √N` (as an infimum). -/
noncomputable def mN (N : ℕ) : ℝ :=
  ⨅ ε : Signs N, supNorm ε.1 / Real.sqrt N

theorem reading_littlewood_limit : Tendsto mN atTop (𝓝 1) := sorry

theorem reading_littlewood_equiv :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ ε : Fin N → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) ∧
        ∀ z : ℂ, ‖z‖ = 1 → ‖∑ k : Fin N, (ε k : ℂ) * z ^ (k : ℕ)‖ ≤ (1 + η) * Real.sqrt N := sorry

/-
Ambiguities / choices:
* Signs as functions Fin N → ℝ with values ±1 (subtype `Signs N`); polynomial evaluated over ℂ.
* "max over t ∈ T": written as iSup over t : ℝ of |P(exp(2πit))|; by periodicity equals the max over T.
  The set is bounded above (by N) so iSup is the honest sup; no junk. It is a max in fact (continuity, compact).
* "min over signs": iInf over the finite nonempty (for N ≥ 1) type Signs N, so a genuine min. For N = 0
  the type has one element, sup over an empty-sum polynomial is 0, and 0/√0 = 0: junk at N = 0 only, irrelevant
  to the limit. Real.sqrt used for √N.
* Limit as N → ∞ over ℕ (atTop), target 1.
* Equivalent form: stated directly with |z| = 1 (all z, not only e(t)), "N ≥ N₀" over ℕ, as in source.
  Source says `≤ (1+η)√N`, same here.
* No requirement that equivalence be derived; both are separate theorems.
-/
