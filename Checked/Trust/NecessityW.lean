import Checked.Trust.NecessityB
import Checked.Chemistry.RKAcentric

/-!
# The co-volume sign in the Redlich–Kwong existence claim (run 2026-11-13T1522Z)

Witness (`necessity%`) that hypothesis 3, `0 < b`, of
`Checked.Chemistry.RKAcentric.rk_coexistence_exists` is needed. Data: b = −1, R = 1, A = 4,
T_c = 10/7 (so 0.7 T_c = 1 and the attraction at 0.7 T_c is 4). The volume v_c = 1 is a zero of
the attraction denominator v² − v; there the junk derivatives meet the critical-point condition
(`Checked.Trust.NCB.crit_at_root`) and the "critical pressure" is (10/7)/2 = 5/7 (Lean's x/0 = 0).
A ratio 0.087 to three decimals then needs a coexistence pressure p_s in (3/50, 1/15). The
isotherm p(v) = 1/(v + 1) − 4/(v² − v) at 0.7 T_c takes such a value at no volume v ≥ 0
(p(0) = 1 and p(1) = 1/2 by x/0 = 0; p > 1/2 on (0, 1); p < 1/17 on (1, ∞), since
v³ − 17v² + 84v + 68 > 0) and is strictly decreasing on (−1, 0), so two volumes above b = −1 with
the same pressure p_s do not exist: no coexistence state, whatever the integral condition says.
No integral and no non-integrability argument is used.
-/

open Set Filter Topology

namespace Checked.Trust.NecessityW
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence

/-- The isotherm of the witness at 0.7 T_c, in closed form. -/
theorem pW_eq (v : ℝ) : cubicP 1 4 (-1) 1 0 1 v = 1 / (v + 1) - 4 / (v ^ 2 - v) := by
  unfold cubicP; congr 1 <;> ring_nf

/-- The witness isotherm is strictly decreasing on (−1, 0). -/
theorem pW_anti {x y : ℝ} (hx : -1 < x) (hxy : x < y) (hy : y < 0) :
    cubicP 1 4 (-1) 1 0 1 y < cubicP 1 4 (-1) 1 0 1 x := by
  rw [pW_eq, pW_eq]
  have h1 : 1 / (y + 1) < 1 / (x + 1) := one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have hy2 : 0 < y ^ 2 - y := by nlinarith
  have hxy2 : y ^ 2 - y < x ^ 2 - x := by nlinarith
  have h2 : 4 / (x ^ 2 - x) < 4 / (y ^ 2 - y) := div_lt_div_of_pos_left (by norm_num) hy2 hxy2
  linarith

/-- Above b = −1, a pressure in (3/50, 1/15) is taken only at negative volumes. -/
theorem pW_neg {v ps : ℝ} (hv : -1 < v) (hp : cubicP 1 4 (-1) 1 0 1 v = ps)
    (h1 : 3 / 50 < ps) (h2 : ps < 1 / 15) : v < 0 := by
  rw [pW_eq] at hp
  by_contra hneg'
  have hneg : 0 ≤ v := not_lt.1 hneg'
  rcases hneg.eq_or_lt with h0 | h0
  · subst h0; norm_num at hp; linarith
  rcases lt_trichotomy v 1 with h | h | h
  · have hd : v ^ 2 - v < 0 := by nlinarith
    have : 4 / (v ^ 2 - v) < 0 := div_neg_of_pos_of_neg (by norm_num) hd
    have : 1 / 2 < 1 / (v + 1) := one_div_lt_one_div_of_lt (by linarith) (by linarith)
    linarith
  · subst h; norm_num at hp; linarith
  · have hd : 0 < v ^ 2 - v := by nlinarith
    have hv1 : 0 < v + 1 := by linarith
    have hlt : 1 / (v + 1) - 4 / (v ^ 2 - v) < 1 / 17 := by
      rw [div_sub_div _ _ hv1.ne' hd.ne', div_lt_div_iff₀ (mul_pos hv1 hd) (by norm_num)]
      nlinarith [sq_nonneg (v - 17 / 2), mul_nonneg (le_of_lt (by linarith : (0 : ℝ) < v))
        (sq_nonneg (v - 17 / 2))]
    linarith

/-- `0 < b` is needed for existence: b = −1, R = 1, A = 4, T_c = 10/7. The junk critical point
v_c = 1 (a zero of the attraction denominator) has "critical pressure" 5/7, so the ratio 0.087
needs a coexistence pressure between 3/50 and 1/15; the isotherm at 0.7 T_c takes such a value at
most once above b (strictly decreasing on (−1, 0), never on [0, ∞)), so there is no coexistence
state at all. -/
theorem rk_coexistence_exists_h3 :
    necessity% Checked.Chemistry.RKAcentric.rk_coexistence_exists 3 := by
  have e7 : (7 / 10 : ℝ) * (10 / 7) = 1 := by norm_num
  refine ⟨1, 4, -1, 10 / 7, 1, one_pos, by norm_num, by norm_num, by norm_num,
    Checked.Trust.NCB.crit_at_root 1 _ (-1) 1 0 (10 / 7) 1 (by norm_num) (by positivity) (by norm_num) ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    intro h; nlinarith
  · rintro ⟨vl, vg, ps, hl, ⟨hlt, h1, h2, -⟩, hr, -⟩
    rw [e7, Real.sqrt_one, div_one] at h1 h2
    have hpc : cubicP 1 (4 / Real.sqrt (10 / 7)) (-1) 1 0 (10 / 7) 1 = 5 / 7 := by
      norm_num [cubicP]
    rw [hpc] at hr
    unfold RoundsTo at hr
    rw [abs_le] at hr
    obtain ⟨hr1, hr2⟩ := hr
    have hps1 : 3 / 50 < ps := by norm_num at hr1; linarith
    have hps2 : ps < 1 / 15 := by norm_num at hr2; linarith
    have hl0 := pW_neg hl h1 hps1 hps2
    have hg0 := pW_neg (by linarith) h2 hps1 hps2
    have := pW_anti hl hlt hg0
    linarith

end Checked.Trust.NecessityW
