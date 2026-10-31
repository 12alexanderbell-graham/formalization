import Mathlib
noncomputable def cubicP (R a b u w T v : ℝ) : ℝ := R * T / (v - b) - a / (v ^ 2 + u * b * v + w * b ^ 2)
def RoundsTo (x d : ℝ) (k : ℕ) : Prop := |x - d| ≤ 1 / (2 * 10 ^ k)
def IsMaxwellCoexistence (p : ℝ → ℝ) (vl vg ps : ℝ) : Prop :=
  vl < vg ∧ p vl = ps ∧ p vg = ps ∧ ∫ v in vl..vg, p v = ps * (vg - vl)

-- a = 0: the uniqueness statement is false (so `ha` is genuinely needed)
example : ¬ (∀ (R a b vl vg ps : ℝ), 0 < R → 0 ≤ a → 0 < b → b < vl →
    IsMaxwellCoexistence (cubicP R a b 0 0 (7 / 10 * (8 * a / (27 * R * b)))) vl vg ps →
    RoundsTo (ps / (a / (27 * b ^ 2))) 0.20046 5) := by
  intro h
  have := h 1 0 1 2 3 0 one_pos le_rfl one_pos (by norm_num)
    ⟨by norm_num, by simp [cubicP], by simp [cubicP], by simp [cubicP]⟩
  unfold RoundsTo at this; norm_num [abs_of_neg] at this

-- R = 0: the temperature is the junk value 0 and the isotherm is -a/v^2
example (a b v : ℝ) : cubicP 0 a b 0 0 (7 / 10 * (8 * a / (27 * 0 * b))) v = -a / v ^ 2 := by
  simp [cubicP]; ring
-- R*T does not depend on R (R ≠ 0)
example (R a b : ℝ) (hR : R ≠ 0) (hb : b ≠ 0) : R * (7 / 10 * (8 * a / (27 * R * b))) = 28 * a / (135 * b) := by
  field_simp; ring
-- the pole: 1/(v-b) is not interval integrable on any nondegenerate interval containing b
example (b c : ℝ) (h : b < c) : ¬ IntervalIntegrable (fun v => (v - b)⁻¹) MeasureTheory.volume b c := by
  rw [intervalIntegrable_sub_inv_iff]; simp [h.ne, Set.left_mem_uIcc]
