import Work.Chemistry.CubicEOSBlind
import Checked.Chemistry.CubicEOS

/-!
# Fidelity audit of `Checked.Chemistry.CubicEOS` (run 2026-10-31T0628Z): blind restatement closed

The blind restater (`Work/Chemistry/CubicEOSBlind.lean`, written from textbook knowledge
without seeing the program's files) stated existence/uniqueness of the critical point and the
constants Z_c, Ω_b, Ω_a for van der Waals, Redlich–Kwong and Peng–Robinson with its own
pressure functions and its own `IsCriticalPoint` (T > 0, v > b, both `deriv` conditions).
Every blind statement is proved here from the program's Checked theorems.
-/

namespace Work.Chemistry.CubicEOSAudit

open Work.Chemistry.CubicEOSBlind Checked.Chemistry.CubicEOS

lemma vdW_eq (R a b T : ℝ) : (fun w => vdWPressure R a b T w) = cubicP R a b 0 0 T := by
  funext w; unfold vdWPressure cubicP; ring_nf

lemma rk_eq (R a b T : ℝ) : (fun w => rkPressure R a b T w) = cubicP R a b 1 0 T := by
  funext w; unfold rkPressure cubicP; ring_nf

lemma pr_eq (R a b T : ℝ) : (fun w => prPressure R a b T w) = cubicP R a b 2 (-1) T := by
  funext w; unfold prPressure cubicP; ring_nf

lemma blind_iff (P : ℝ → ℝ → ℝ) (u w R a b : ℝ) (hP : ∀ T, (fun x => P T x) = cubicP R a b u w T)
    (T v : ℝ) : IsCriticalPoint P b T v ↔ 0 < T ∧ b < v ∧ IsCriticalIsotherm (cubicP R a b u w T) v := by
  unfold IsCriticalPoint IsCriticalIsotherm; rw [hP T]

lemma blind_eu (P : ℝ → ℝ → ℝ) (u w R a b : ℝ) (hP : ∀ T, (fun x => P T x) = cubicP R a b u w T)
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) (hu : -2 < u) (h1 : 0 < 1 + u + w) :
    ∃! p : ℝ × ℝ, IsCriticalPoint P b p.1 p.2 := by
  simp only [blind_iff P u w R a b hP]
  exact exists_unique_critical R a b u w hR ha hb hu h1

theorem vdW_critical_existsUnique (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    ∃! p : ℝ × ℝ, IsCriticalPoint (vdWPressure R a b) b p.1 p.2 :=
  blind_eu _ 0 0 R a b (vdW_eq R a b) hR ha hb (by norm_num) (by norm_num)

theorem rk_critical_existsUnique (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    ∃! p : ℝ × ℝ, IsCriticalPoint (rkPressure R a b) b p.1 p.2 :=
  blind_eu _ 1 0 R a b (rk_eq R a b) hR ha hb (by norm_num) (by norm_num)

theorem pr_critical_existsUnique (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    ∃! p : ℝ × ℝ, IsCriticalPoint (prPressure R a b) b p.1 p.2 :=
  blind_eu _ 2 (-1) R a b (pr_eq R a b) hR ha hb (by norm_num) (by norm_num)

theorem vdW_critical_constants (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (Tc vc : ℝ) (hc : IsCriticalPoint (vdWPressure R a b) b Tc vc) :
    vdWPressure R a b Tc vc * vc / (R * Tc) = 3 / 8 ∧
    b * vdWPressure R a b Tc vc / (R * Tc) = 1 / 8 ∧
    a * vdWPressure R a b Tc vc / (R * Tc) ^ 2 = 27 / 64 := by
  obtain ⟨-, hv, hc⟩ := (blind_iff _ 0 0 R a b (vdW_eq R a b) Tc vc).1 hc
  have e : vdWPressure R a b Tc vc = cubicP R a b 0 0 Tc vc := congrFun (vdW_eq R a b Tc) vc
  rw [e]; exact Checked.Chemistry.CubicEOS.vdW_constants R a b Tc vc ha hb hv hc

theorem rk_critical_constants (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (Tc vc : ℝ) (hc : IsCriticalPoint (rkPressure R a b) b Tc vc) :
    rkPressure R a b Tc vc * vc / (R * Tc) = 1 / 3 ∧
    Work.Chemistry.CubicEOSBlind.RoundsTo (b * rkPressure R a b Tc vc / (R * Tc)) 0.08664 5 ∧
    Work.Chemistry.CubicEOSBlind.RoundsTo (a * rkPressure R a b Tc vc / (R * Tc) ^ 2) 0.42748 5 := by
  obtain ⟨-, hv, hc⟩ := (blind_iff _ 1 0 R a b (rk_eq R a b) Tc vc).1 hc
  have e : rkPressure R a b Tc vc = cubicP R a b 1 0 Tc vc := congrFun (rk_eq R a b Tc) vc
  rw [e]; exact Checked.Chemistry.CubicEOS.rk_constants R a b Tc vc ha hb hv hc

theorem pr_critical_constants (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (Tc vc : ℝ) (hc : IsCriticalPoint (prPressure R a b) b Tc vc) :
    Work.Chemistry.CubicEOSBlind.RoundsTo (prPressure R a b Tc vc * vc / (R * Tc)) 0.3074 4 ∧
    Work.Chemistry.CubicEOSBlind.RoundsTo (b * prPressure R a b Tc vc / (R * Tc)) 0.07780 5 ∧
    Work.Chemistry.CubicEOSBlind.RoundsTo (a * prPressure R a b Tc vc / (R * Tc) ^ 2) 0.45724 5 := by
  obtain ⟨-, hv, hc⟩ := (blind_iff _ 2 (-1) R a b (pr_eq R a b) Tc vc).1 hc
  have e : prPressure R a b Tc vc = cubicP R a b 2 (-1) Tc vc := congrFun (pr_eq R a b Tc) vc
  rw [e]; exact Checked.Chemistry.CubicEOS.pr_constants R a b Tc vc ha hb hv hc

end Work.Chemistry.CubicEOSAudit
