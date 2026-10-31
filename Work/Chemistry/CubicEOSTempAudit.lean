import Work.Chemistry.CubicEOSTempBlind
import Work.Chemistry.CubicEOSTemp

/-!
# Blind restatement of `Work.Chemistry.CubicEOSTemp` closed in Lean (run 2026-10-31T0628Z)

The blind restater (`Work/Chemistry/CubicEOSTempBlind.lean`, textbook only) stated the
Redlich–Kwong 1949 form `A/(√T v(v+b))` literally and the general a(T) family with its own
`IsCriticalPoint` (nested `deriv` in v at fixed T). Both are proved here from the program's
theorems.
-/

namespace Work.Chemistry.CubicEOSTempAudit

open Work.Chemistry.CubicEOSTempBlind Checked.Chemistry.CubicEOS

lemma crit_eq (P : ℝ → ℝ → ℝ) (T v : ℝ) :
    IsCriticalPoint P T v ↔ IsCriticalIsotherm (fun x => P T x) v := Iff.rfl

theorem cubic_existsUnique_critical (R b u w : ℝ) (a : ℝ → ℝ)
    (hR : 0 < R) (hb : 0 < b) (hu : -2 < u) (huw : 0 < 1 + u + w)
    (ha_pos : ∀ T, 0 < T → 0 < a T)
    (ha_mono : StrictMonoOn (fun T => T / a T) (Set.Ioi 0))
    (ha_surj : ∀ y, 0 < y → ∃ T, 0 < T ∧ T / a T = y) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ b < p.2 ∧
      IsCriticalPoint (cubicPressure R b u w a) p.1 p.2 := by
  have h : ∀ T, (fun x => cubicPressure R b u w a T x) = cubicP R (a T) b u w T := by
    intro T; funext x; rfl
  simp only [crit_eq, h]
  exact Work.Chemistry.CubicEOSTemp.exists_unique_critical_T R b u w a hR hb hu huw ha_pos
    ha_mono ha_surj

theorem rk_existsUnique_critical (R A b : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ b < p.2 ∧ IsCriticalPoint (rkPressure R A b) p.1 p.2 := by
  have h : ∀ T, (fun x => rkPressure R A b T x) = cubicP R (A / Real.sqrt T) b 1 0 T := by
    intro T; funext x; unfold rkPressure cubicP
    rw [div_div]; ring_nf
  simp only [crit_eq, h]
  exact Work.Chemistry.CubicEOSTemp.rk_exists_unique_critical R A b hR hA hb

end Work.Chemistry.CubicEOSTempAudit
