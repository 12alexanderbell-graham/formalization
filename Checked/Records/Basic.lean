import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Certified numbers in the records (trust track T4/T5, run 2026-10-31T0228Z)

A decimal written in `FINDINGS.md` ("at Ω_m = 0.3 the printed l₀ is 0.685") is a claim. Red-team
defects A06 and B07 (run 0028Z) changed such numbers and every check accepted them: prose was not
machine-checked. From this run, every computed decimal in the verified findings carries a tag
`[✓name]` naming a registered headline `Checked.Records.name` whose statement contains
`RoundsTo x d k`, and CI (`scripts/trust/check_numbers.py`) checks that the prose shows exactly
`d` written with `k` decimals.

`RoundsTo x d k` says: `x` rounds to `d` at `k` decimal places (half-unit tolerance, both ends
closed). It is pure mathematics; *what* `x` is, is the rest of the record theorem's statement
(a physical quantity in a model, built from pinned definitions, or a printed formula).
-/

namespace Checked.Records

/-- `x` rounds to `d` at `k` decimal places: `|x − d| ≤ ½·10⁻ᵏ`. -/
def RoundsTo (x d : ℝ) (k : ℕ) : Prop := |x - d| ≤ 1 / (2 * 10 ^ k)

lemma roundsTo_of_mem {x d : ℝ} {k : ℕ} (h1 : d - 1 / (2 * 10 ^ k) ≤ x)
    (h2 : x ≤ d + 1 / (2 * 10 ^ k)) : RoundsTo x d k := by
  unfold RoundsTo; rw [abs_le]; constructor <;> linarith

/-- A sign change of a continuous function across the rounding interval of `d` gives a root
that rounds to `d` (intermediate value theorem). -/
lemma exists_root_roundsTo {f : ℝ → ℝ} (hf : Continuous f) (d : ℝ) (k : ℕ)
    (h : f (d - 1 / (2 * 10 ^ k)) * f (d + 1 / (2 * 10 ^ k)) ≤ 0) :
    ∃ r, RoundsTo r d k ∧ f r = 0 := by
  set e : ℝ := 1 / (2 * 10 ^ k) with he
  have he0 : 0 ≤ e := by positivity
  have hab : d - e ≤ d + e := by linarith
  have mem : ∀ r ∈ Set.Icc (d - e) (d + e), RoundsTo r d k := fun r hr =>
    roundsTo_of_mem hr.1 hr.2
  have hc : ContinuousOn f (Set.Icc (d - e) (d + e)) := hf.continuousOn
  have root_lo : f (d - e) = 0 → ∃ r, RoundsTo r d k ∧ f r = 0 := fun h0 =>
    ⟨d - e, mem _ ⟨le_refl _, hab⟩, h0⟩
  rcases le_total (f (d - e)) 0 with hlo | hlo
  · rcases le_total 0 (f (d + e)) with hhi | hhi
    · obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc hab hc ⟨hlo, hhi⟩
      exact ⟨r, mem r hr, hr0⟩
    · rcases lt_or_eq_of_le hhi with hlt | heq
      · exact root_lo (by nlinarith)
      · exact ⟨d + e, mem _ ⟨hab, le_refl _⟩, heq⟩
  · rcases le_total (f (d + e)) 0 with hhi | hhi
    · obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' hab hc ⟨hhi, hlo⟩
      exact ⟨r, mem r hr, hr0⟩
    · rcases lt_or_eq_of_le hhi with hlt | heq
      · exact root_lo (by nlinarith)
      · exact ⟨d + e, mem _ ⟨hab, le_refl _⟩, heq.symm⟩

end Checked.Records
