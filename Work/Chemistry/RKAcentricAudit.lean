import Work.Chemistry.RKAcentricBlind
import Work.Chemistry.RKAcentric

/-!
# Blind restatement of `Work.Chemistry.RKAcentric` closed in Lean (run 2026-11-04T1828Z)

The blind restater (this run, `Work/Chemistry/RKAcentricBlind.lean`; from the textbook claim
alone, without seeing the program's statement) wrote the RK pressure as
`R T/(v − b) − A/(√T · v (v + b))`, the critical point by vanishing first and second `deriv`,
coexistence by equal areas with `b < v_l`, and added the conclusion `0 < p_s/P_c`.
The bridge is that the blind pressure is literally the program's `cubicP R (A/√T) b 1 0 T`
(`rkP_eq`, everywhere, by `A/(s·w) = (A/s)/w`). The blind `coexistence_numbers`,
`coexistence_exists` and `rk_acentric` are proved here from the frozen theorems
`rk_coexistence_unique` and `rk_coexistence_exists`. The blind supporting statements
`critical_point_exists` and `critical_point_unique` are not used by the claim and stay open.
-/

namespace Work.Chemistry.RKAcentricAudit

open Blind.RKAcentric Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence

lemma rkP_eq (R A b T : ℝ) : (fun v => rkP R A b v T) = cubicP R (A / Real.sqrt T) b 1 0 T := by
  funext v
  unfold rkP cubicP
  rw [div_div, mul_assoc]
  ring_nf

theorem blind_numbers_closed (R A b : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b)
    (Tc vc Pc : ℝ) (hc : IsCriticalPoint R A b Tc vc Pc)
    (vl vg ps : ℝ) (hco : IsCoexistence R A b (7 / 10 * Tc) vl vg ps) :
    0 < ps / Pc ∧
    RoundsTo (ps / Pc) (87 / 1000) 3 ∧
    RoundsTo (Blind.RKAcentric.acentric ps Pc) (58 / 1000) 3 := by
  obtain ⟨hTc, hvc, hd1, hd2, hPc⟩ := hc
  obtain ⟨hl, hlg, hpl, hpg, hint⟩ := hco
  have hcrit : IsCriticalIsotherm (cubicP R (A / Real.sqrt Tc) b 1 0 Tc) vc := by
    rw [← rkP_eq]; exact ⟨hd1, hd2⟩
  have hM : IsMaxwellCoexistence
      (cubicP R (A / Real.sqrt (7 / 10 * Tc)) b 1 0 (7 / 10 * Tc)) vl vg ps := by
    rw [← rkP_eq]; exact ⟨hlg, hpl, hpg, hint⟩
  have hPc' : Pc = cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc := by
    rw [hPc, ← rkP_eq]
  obtain ⟨h1, h2⟩ := Work.Chemistry.RKAcentric.rk_coexistence_unique R A b Tc vc vl vg ps
    hR hA hb hTc hvc hcrit hl hM
  rw [← hPc'] at h1 h2
  have e1 : (87 / 1000 : ℝ) = 0.087 := by norm_num
  have e2 : (58 / 1000 : ℝ) = 0.058 := by norm_num
  refine ⟨?_, by rw [e1]; exact h1, by rw [e2]; exact h2⟩
  unfold RoundsTo at h1
  rw [abs_le] at h1
  norm_num at h1
  linarith [h1.1]

theorem blind_exists_closed (R A b : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b)
    (Tc vc Pc : ℝ) (hc : IsCriticalPoint R A b Tc vc Pc) :
    ∃ vl vg ps, IsCoexistence R A b (7 / 10 * Tc) vl vg ps := by
  obtain ⟨hTc, hvc, hd1, hd2, _⟩ := hc
  have hcrit : IsCriticalIsotherm (cubicP R (A / Real.sqrt Tc) b 1 0 Tc) vc := by
    rw [← rkP_eq]; exact ⟨hd1, hd2⟩
  obtain ⟨vl, vg, ps, hl, hM, _, _⟩ :=
    Work.Chemistry.RKAcentric.rk_coexistence_exists R A b Tc vc hR hA hb hTc hvc hcrit
  rw [← rkP_eq] at hM
  obtain ⟨hlg, hpl, hpg, hint⟩ := hM
  exact ⟨vl, vg, ps, hl, hlg, hpl, hpg, hint⟩

theorem blind_full_closed (R A b : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b)
    (Tc vc Pc : ℝ) (hc : IsCriticalPoint R A b Tc vc Pc) :
    (∃ vl vg ps, IsCoexistence R A b (7 / 10 * Tc) vl vg ps) ∧
    ∀ vl vg ps, IsCoexistence R A b (7 / 10 * Tc) vl vg ps →
      0 < ps / Pc ∧
      RoundsTo (ps / Pc) (87 / 1000) 3 ∧
      RoundsTo (Blind.RKAcentric.acentric ps Pc) (58 / 1000) 3 :=
  ⟨blind_exists_closed R A b hR hA hb Tc vc Pc hc,
    fun vl vg ps h => blind_numbers_closed R A b hR hA hb Tc vc Pc hc vl vg ps h⟩

/-- The blind acentric factor is the program's. -/
lemma acentric_eq (ps Pc : ℝ) : Blind.RKAcentric.acentric ps Pc =
    Checked.Chemistry.Coexistence.acentric ps Pc := rfl

end Work.Chemistry.RKAcentricAudit
