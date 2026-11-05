import Mathlib
import Checked.Records.Basic

open Real MeasureTheory Checked.Records

namespace Blind.PR78Acentric

/-- Robinson–Peng 1978 correlation. -/
noncomputable def kappa (ω : ℝ) : ℝ :=
  0.379642 + 1.48503 * ω - 0.164423 * ω ^ 2 + 0.016666 * ω ^ 3

/-- Soave's temperature function. -/
noncomputable def aT (a_c T_c κ T : ℝ) : ℝ :=
  a_c * (1 + κ * (1 - Real.sqrt (T / T_c))) ^ 2

/-- Peng–Robinson pressure at volume `v`, temperature `T`. -/
noncomputable def P (R a_c b T_c κ v T : ℝ) : ℝ :=
  R * T / (v - b) - aT a_c T_c κ T / (v ^ 2 + 2 * b * v - b ^ 2)

/-- `(T_c, v_c)` is a critical point: first and second volume derivatives of the
critical isotherm vanish at `v_c` (with `v_c > b`, `T_c > 0`). -/
def IsCritical (R a_c b κ T_c v_c : ℝ) : Prop :=
  0 < T_c ∧ b < v_c ∧
  deriv (fun v => P R a_c b T_c κ v T_c) v_c = 0 ∧
  deriv (deriv (fun v => P R a_c b T_c κ v T_c)) v_c = 0

/-- Maxwell equal-area coexistence at temperature `T`. -/
def IsMaxwell (R a_c b T_c κ T v_l v_g p_s : ℝ) : Prop :=
  b < v_l ∧ v_l < v_g ∧
  P R a_c b T_c κ v_l T = p_s ∧ P R a_c b T_c κ v_g T = p_s ∧
  ∫ v in v_l..v_g, P R a_c b T_c κ v T = p_s * (v_g - v_l)

theorem pr78_acentric (R a_c b T_c v_c v_l v_g p_s : ℝ)
    (hR : 0 < R) (ha : 0 < a_c) (hb : 0 < b)
    (hcrit : IsCritical R a_c b (kappa 1) T_c v_c)
    (hmax : IsMaxwell R a_c b T_c (kappa 1) (0.7 * T_c) v_l v_g p_s) :
    RoundsTo (p_s / P R a_c b T_c (kappa 1) v_c T_c) 0.0100 4 ∧
    RoundsTo (-Real.logb 10 (p_s / P R a_c b T_c (kappa 1) v_c T_c) - 1) 1.000 3 := by
  sorry

theorem pr78_exists (R a_c b T_c v_c : ℝ)
    (hR : 0 < R) (ha : 0 < a_c) (hb : 0 < b)
    (hcrit : IsCritical R a_c b (kappa 1) T_c v_c) :
    ∃ v_l v_g p_s : ℝ, IsMaxwell R a_c b T_c (kappa 1) (0.7 * T_c) v_l v_g p_s ∧
      RoundsTo (p_s / P R a_c b T_c (kappa 1) v_c T_c) 0.0100 4 ∧
      RoundsTo (-Real.logb 10 (p_s / P R a_c b T_c (kappa 1) v_c T_c) - 1) 1.000 3 := by
  sorry

end Blind.PR78Acentric
