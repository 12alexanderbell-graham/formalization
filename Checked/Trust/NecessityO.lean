import Checked.Trust.NonVacuity
import Checked.Trust.NecessityB
import Checked.Trust.Witnesses
import Checked.Chemistry.CubicEOS
import Checked.Chemistry.Coexistence
import Checked.Chemistry.RKAcentric
import Checked.Chemistry.SRKAcentric
import Checked.Chemistry.PRAcentric
import Checked.Chemistry.PR78Acentric
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Hypothesis necessity for the acentric-factor headlines (run 2026-11-12T1228Z)

Witnesses (`necessity%`) and redundancy proofs (`dropped%`) for the hypotheses of the
Redlich–Kwong, Soave–Redlich–Kwong and Peng–Robinson (1976, 1978) acentric-factor headlines
(`Checked.Chemistry.RKAcentric`, `SRKAcentric`, `PRAcentric`, `PR78Acentric`). Routes:

* **attraction positivity dropped** (SRK, PR, PR78): attraction 0 at temperature 0 makes both
  isotherms identically 0, so every volume is a critical point, every pair of volumes a coexistence
  state at pressure 0, and the pressure ratio is 0;
* **temperature positivity dropped** (RK): T_c = 0 gives attraction A/√0 = 0 in Lean's arithmetic,
  the same zero isotherms;
* **co-volume positivity dropped**: b = −1 puts the zeros of the attraction denominator inside the
  allowed volumes; there the isotherm takes the junk value 0 and meets the critical-point condition
  by junk derivatives (`Checked.Trust.NCB.crit_at_root`), and the coexistence condition holds with
  pressure 0 between two zeros of the isotherm because Lean's integral of a function that is not
  integrable across a pole is 0 (`maxwell_zero_of_pole`);
* **b < v_c dropped**: v_c = b, where the junk derivatives meet the critical-point condition
  (`Checked.Trust.NCB.crit_at_b`) and the "critical pressure" is −a/(2b²) < 0, while every
  coexistence pressure at a genuine critical point is positive;
* **critical-point condition dropped**: a volume just above b, where the pressure exceeds 200 times
  the coexistence pressure (100 times the genuine critical pressure for existence), so the ratio
  is far below the certified window;
* **R > 0 and A > 0 in RK are redundant**: a critical point of the RK isotherm with v_c > b > 0 and
  T_c > 0 forces R > 0 (the critical relations give b P_c/(R T_c) > 0 and a P_c/(R T_c)² > 0), and
  with A ≤ 0 the isotherm is strictly decreasing, so there is no critical point.
-/

open Set Filter Topology Asymptotics MeasureTheory

namespace Checked.Trust.NecessityO
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence

/-! ## Generic lemmas -/

/-- A function behaving like `k / ((x − c) m(x))` near `c` (`k ≠ 0`, `m` continuous and nonzero at
`c`, plus a term continuous at `c`) is not interval integrable on any nontrivial interval containing
`c`. -/
theorem not_ii_of_pole (f h m : ℝ → ℝ) (c k : ℝ) (hk : k ≠ 0) (hm : ContinuousAt m c) (hmc : m c ≠ 0)
    (hh : ContinuousAt h c) (hf : ∀ᶠ x in 𝓝[≠] c, f x = h x + k / ((x - c) * m x)) {a b : ℝ}
    (hab : a ≠ b) (hc : c ∈ uIcc a b) : ¬ IntervalIntegrable f volume a b := by
  apply not_intervalIntegrable_of_sub_inv_isBigO_punctured _ hab hc
  set L := k / m c with hL
  have hL0 : L ≠ 0 := div_ne_zero hk hmc
  have hT : Tendsto (fun x => h x * (x - c) + k / m x) (𝓝[≠] c) (𝓝 L) := by
    have h1 : Tendsto (fun x => h x * (x - c)) (𝓝 c) (𝓝 (h c * (c - c))) :=
      (hh.tendsto).mul ((continuousAt_id.sub continuousAt_const).tendsto)
    have h2 : Tendsto (fun x => k / m x) (𝓝 c) (𝓝 (k / m c)) :=
      (continuousAt_const.div hm hmc).tendsto
    have := (h1.add h2).mono_left (nhdsWithin_le_nhds (s := {c}ᶜ))
    simpa [hL] using this
  have hev : ∀ᶠ x in 𝓝[≠] c, |L| / 2 < |h x * (x - c) + k / m x| :=
    hT.abs.eventually (lt_mem_nhds (half_lt_self (abs_pos.2 hL0)))
  have hm' : ∀ᶠ x in 𝓝[≠] c, m x ≠ 0 :=
    (hm.eventually_ne hmc).filter_mono nhdsWithin_le_nhds
  refine IsBigO.of_bound (2 / |L|) ?_
  filter_upwards [hev, hf, hm', self_mem_nhdsWithin] with x hx hfx hmx hxc
  have hxc' : x - c ≠ 0 := sub_ne_zero.2 hxc
  have e : (x - c) * f x = h x * (x - c) + k / m x := by
    rw [hfx]; field_simp
  rw [← e, abs_mul] at hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv]
  have hpos : 0 < |x - c| := abs_pos.2 hxc'
  have hLpos : 0 < |L| := abs_pos.2 hL0
  rw [inv_le_iff_one_le_mul₀' hpos]
  have : |L| / 2 * (2 / |L|) = 1 := by field_simp
  nlinarith [abs_nonneg (f x)]

/-- Two zeros of an isotherm with a non-integrable pole between them form a Maxwell coexistence
state at pressure 0 (the junk integral is 0). -/
theorem maxwell_zero_of_pole (p h m : ℝ → ℝ) (c k vl vg : ℝ) (hk : k ≠ 0) (hm : ContinuousAt m c)
    (hmc : m c ≠ 0) (hh : ContinuousAt h c) (hf : ∀ᶠ x in 𝓝[≠] c, p x = h x + k / ((x - c) * m x))
    (hlg : vl < vg) (hc : c ∈ Icc vl vg) (hl : p vl = 0) (hg : p vg = 0) :
    IsMaxwellCoexistence p vl vg 0 := by
  refine ⟨hlg, hl, hg, ?_⟩
  rw [intervalIntegral.integral_undef
    (not_ii_of_pole p h m c k hk hm hmc hh hf hlg.ne (by rw [uIcc_of_le hlg.le]; exact hc))]
  ring

/-- At a genuine critical point (v > b > 0) of the cubic isotherm with u = 1, w = 0 (RK, SRK) or
u = 2, w = −1 (PR), R T > 0 and the critical pressure is positive. -/
theorem crit_RT_pos (R a b u w T v : ℝ) (ha : 0 < a) (hb : 0 < b) (hv : b < v)
    (huw : (u = 1 ∧ w = 0) ∨ (u = 2 ∧ w = -1))
    (hc : IsCriticalIsotherm (cubicP R a b u w T) v) :
    0 < R * T ∧ 0 < cubicP R a b u w T v := by
  have hu : -2 < u := by rcases huw with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  have hD : 0 < v ^ 2 + u * b * v + w * b ^ 2 := by
    rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> nlinarith
  obtain ⟨hf, hx1, -, h2, h3⟩ := reduced R a b u w T v ha hb hu hv hD hc
  set x := v / b
  set P := cubicP R a b u w T v
  have hN : 0 < ((x - 1) * (2 * x + u) - (x ^ 2 + u * x + w)) := by
    unfold critCubic at hf
    rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> nlinarith
  have hQ : 0 < x ^ 2 + u * x + w := by
    rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> nlinarith
  have h2u : 0 < 2 * x + u := by rcases huw with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> linarith
  have hx1' : 0 < x - 1 := by linarith
  have hr3 : 0 < a * P / (R * T) ^ 2 := by rw [h3]; positivity
  have hr2 : 0 < b * P / (R * T) := by rw [h2]; positivity
  have hRT : R * T ≠ 0 := by intro h0; rw [h0] at hr2; simp at hr2
  have hP : 0 < P := by
    have hsq : 0 < (R * T) ^ 2 := by positivity
    have := (div_pos_iff_of_pos_right hsq).1 hr3
    exact pos_of_mul_pos_right this ha.le
  refine ⟨?_, hP⟩
  have hbP : 0 < b * P := mul_pos hb hP
  exact (div_pos_iff_of_pos_left hbP).1 hr2

/-- With b = 1, a = 1, R = 1 and T > 0, the isotherm exceeds any bound just above the co-volume
(when its attraction denominator is at least 2 there). -/
theorem big_pressure (u w T M : ℝ) (hT : 0 < T) (hD : ∀ v : ℝ, 1 < v → 2 ≤ v ^ 2 + u * 1 * v + w * 1 ^ 2) :
    ∃ v, 1 < v ∧ M < cubicP 1 1 1 u w T v := by
  have hM : 0 < |M| + 1 := by positivity
  refine ⟨1 + T / (|M| + 1), by have := div_pos hT hM; linarith, ?_⟩
  have hv : 1 < 1 + T / (|M| + 1) := by have := div_pos hT hM; linarith
  have hD' := hD _ hv
  unfold cubicP
  have e : 1 * T / (1 + T / (|M| + 1) - 1) = |M| + 1 := by
    rw [show 1 + T / (|M| + 1) - 1 = T / (|M| + 1) by ring, one_mul, div_div_cancel₀ hT.ne']
  rw [e]
  have : 1 / ((1 + T / (|M| + 1)) ^ 2 + u * 1 * (1 + T / (|M| + 1)) + w * 1 ^ 2) ≤ 1 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hD'
  have := le_abs_self M
  linarith

/-- A pressure ratio that rounds to a positive value `d` forces the same sign. -/
theorem pos_of_roundsTo {x d : ℝ} {k : ℕ} (h : RoundsTo x d k) (hd : 1 / (2 * 10 ^ k) < d) : 0 < x := by
  unfold RoundsTo at h; rw [abs_le] at h; linarith

theorem sqrt07_lt : Real.sqrt (7 / 10) < 1 := by
  rw [Real.sqrt_lt' one_pos]; norm_num

/-! ## Soave–Redlich–Kwong at ω = 1 (`Checked.Chemistry.SRKAcentric`) -/

section SRK
open Checked.Trust.NCB Checked.Trust.NV

/-- The SRK isotherm with b = −1 and R = 0 is −a/(v(v − 1)): zero (junk) at v = 0 and v = 1, with a
non-integrable pole at 0 between them. -/
theorem srk_junk_maxwell (a T : ℝ) (ha : a ≠ 0) : IsMaxwellCoexistence (cubicP 0 a (-1) 1 0 T) 0 1 0 :=
  maxwell_zero_of_pole _ (fun _ => 0) (fun x => x - 1) 0 (-a) 0 1 (neg_ne_zero.2 ha)
    (by fun_prop) (by norm_num) continuousAt_const
    (Eventually.of_forall fun x => by unfold cubicP; ring) one_pos ⟨le_rfl, zero_le_one⟩
    (by simp [cubicP]) (by simp [cubicP])

theorem srk_alpha_pos : 0 < 1 + (0.480 + 1.574 * 1 - 0.176 * 1 ^ 2) * (1 - Real.sqrt (7 / 10)) := by
  have h1 : 0 < 1 - Real.sqrt (7 / 10) := by linarith [sqrt07_lt]
  have hk : (0 : ℝ) < 0.480 + 1.574 * 1 - 0.176 * 1 ^ 2 := by norm_num
  nlinarith [mul_pos hk h1]

/-- `b < v_c` is needed: at v_c = b the junk derivatives meet the critical-point
condition and the "critical pressure" is −1/2, while the coexistence pressure is positive. -/
theorem srk_omega1_unique_h3 : necessity% Checked.Chemistry.SRKAcentric.srk_omega1_unique 3 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := srk_crit_witness
  obtain ⟨vl, vg, ps, hl, h, hr, -⟩ := Checked.Chemistry.SRKAcentric.srk_omega1_exists
    1 1 1 Tc vc one_pos one_pos hv hc
  have hPc := (crit_RT_pos 1 1 1 1 0 Tc vc one_pos one_pos hv (Or.inl ⟨rfl, rfl⟩) hc).2
  have hps : 0 < ps := by
    have := pos_of_roundsTo hr (by norm_num)
    exact (div_pos_iff_of_pos_right hPc).1 this
  refine ⟨1, 1, 1, Tc, 1, vl, vg, ps, one_pos, one_pos,
    crit_at_b 1 1 1 1 0 Tc (by simpa using hT.ne') (by norm_num), hl, h, ?_⟩
  rintro ⟨h1, -⟩
  have e : cubicP 1 1 1 1 0 Tc 1 = -1 / 2 := by norm_num [cubicP]
  rw [e] at h1
  have := pos_of_roundsTo h1 (by norm_num)
  have : ps / (-1 / 2) < 0 := div_neg_of_pos_of_neg hps (by norm_num)
  linarith

/-- The critical-point condition is needed: at a volume just above b the pressure exceeds 200 times
the coexistence pressure, so the ratio is below 0.005. -/
theorem srk_omega1_unique_h4 : necessity% Checked.Chemistry.SRKAcentric.srk_omega1_unique 4 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := srk_crit_witness
  obtain ⟨vl, vg, ps, hl, h, -, -⟩ := Checked.Chemistry.SRKAcentric.srk_omega1_exists
    1 1 1 Tc vc one_pos one_pos hv hc
  obtain ⟨v, hv1, hbig⟩ := big_pressure 1 0 Tc (200 * |ps| + 1) hT (fun v hv => by nlinarith)
  refine ⟨1, 1, 1, Tc, v, vl, vg, ps, one_pos, one_pos, hv1, hl, h, ?_⟩
  rintro ⟨h1, -⟩
  have hP : 0 < cubicP 1 1 1 1 0 Tc v := by linarith [abs_nonneg ps]
  have := pos_of_roundsTo h1 (by norm_num)
  unfold RoundsTo at h1; rw [abs_le] at h1
  have hle : ps / cubicP 1 1 1 1 0 Tc v * cubicP 1 1 1 1 0 Tc v = ps := div_mul_cancel₀ _ hP.ne'
  nlinarith [le_abs_self ps]

/-- `0 < a_c` is needed: with a_c = 0 and T_c = 0 both isotherms are identically 0. -/
theorem srk_omega1_unique_h1 : necessity% Checked.Chemistry.SRKAcentric.srk_omega1_unique 1 := by
  have hz : cubicP 1 (0 * (1 + (0.480 + 1.574 * 1 - 0.176 * 1 ^ 2) * (1 - Real.sqrt (7 / 10))) ^ 2)
      1 1 0 (7 / 10 * 0) = fun _ => 0 := by funext x; simp [cubicP]
  refine ⟨1, 0, 1, 0, 2, 2, 3, 0, one_pos, by norm_num, zero_isotherm_critical 1 1 1 0 2,
    by norm_num, ?_, ?_⟩
  · rw [hz]; exact ⟨by norm_num, rfl, rfl, by simp⟩
  · rintro ⟨h1, -⟩; norm_num [RoundsTo, abs_le] at h1

/-- `0 < b` is needed: b = −1, R = 0 (Lean's junk values at the zeros 0, 1 of the attraction
denominator give a critical point at v_c = 1 and a coexistence state at pressure 0). -/
theorem srk_omega1_unique_h2 : necessity% Checked.Chemistry.SRKAcentric.srk_omega1_unique 2 := by
  have hα := srk_alpha_pos
  refine ⟨0, 1, -1, 1, 1, 0, 1, 0, one_pos, by norm_num,
    crit_at_root 0 1 (-1) 1 0 1 1 (by norm_num) one_ne_zero (by norm_num) ?_, by norm_num,
    srk_junk_maxwell _ _ (by positivity), ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    intro h; nlinarith
  · rintro ⟨h1, -⟩; norm_num [RoundsTo, abs_le] at h1

/-- `0 < a_c` is needed for existence: with a_c = 0, T_c = 0 every coexistence pressure is 0. -/
theorem srk_omega1_exists_h1 : necessity% Checked.Chemistry.SRKAcentric.srk_omega1_exists 1 := by
  refine ⟨1, 0, 1, 0, 2, by norm_num, by norm_num, zero_isotherm_critical 1 1 1 0 2, ?_⟩
  rintro ⟨vl, vg, ps, -, ⟨-, hpl, -, -⟩, h1, -⟩
  simp [cubicP] at hpl
  subst hpl
  norm_num [RoundsTo, abs_le] at h1

/-- `0 < b` is needed for existence: b = −1, R = 0, v_c = 1 (junk critical point), where the
"critical pressure" is the junk value 0, so every pressure ratio is 0. -/
theorem srk_omega1_exists_h2 : necessity% Checked.Chemistry.SRKAcentric.srk_omega1_exists 2 := by
  refine ⟨0, 1, -1, 1, 1, one_pos, by norm_num,
    crit_at_root 0 1 (-1) 1 0 1 1 (by norm_num) one_ne_zero (by norm_num) ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    intro h; nlinarith
  · rintro ⟨vl, vg, ps, -, -, h1, -⟩
    norm_num [cubicP, RoundsTo, abs_le] at h1

/-- `b < v_c` is needed for existence: at v_c = b the "critical pressure" is −1/2, so a positive
ratio needs a negative coexistence pressure, but every coexistence pressure is positive (the
uniqueness theorem at the genuine critical point). -/
theorem srk_omega1_exists_h3 : necessity% Checked.Chemistry.SRKAcentric.srk_omega1_exists 3 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := srk_crit_witness
  have hPc := (crit_RT_pos 1 1 1 1 0 Tc vc one_pos one_pos hv (Or.inl ⟨rfl, rfl⟩) hc).2
  refine ⟨1, 1, 1, Tc, 1, one_pos, one_pos,
    crit_at_b 1 1 1 1 0 Tc (by simpa using hT.ne') (by norm_num), ?_⟩
  rintro ⟨vl, vg, ps, hl, h, h1, -⟩
  obtain ⟨hr, -⟩ := Checked.Chemistry.SRKAcentric.srk_omega1_unique 1 1 1 Tc vc vl vg ps one_pos
    one_pos hv hc hl h
  have hps : 0 < ps := (div_pos_iff_of_pos_right hPc).1 (pos_of_roundsTo hr (by norm_num))
  have e : cubicP 1 1 1 1 0 Tc 1 = -1 / 2 := by norm_num [cubicP]
  rw [e] at h1
  have := pos_of_roundsTo h1 (by norm_num)
  have : ps / (-1 / 2) < 0 := div_neg_of_pos_of_neg hps (by norm_num)
  linarith

/-- The critical-point condition is needed for existence: at a volume just above b with pressure
above 100 P_c every coexistence ratio is below 0.0002. -/
theorem srk_omega1_exists_h4 : necessity% Checked.Chemistry.SRKAcentric.srk_omega1_exists 4 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := srk_crit_witness
  have hPc := (crit_RT_pos 1 1 1 1 0 Tc vc one_pos one_pos hv (Or.inl ⟨rfl, rfl⟩) hc).2
  obtain ⟨v, hv1, hbig⟩ := big_pressure 1 0 Tc (100 * cubicP 1 1 1 1 0 Tc vc) hT (fun v hv => by nlinarith)
  refine ⟨1, 1, 1, Tc, v, one_pos, one_pos, hv1, ?_⟩
  rintro ⟨vl, vg, ps, hl, h, h1, -⟩
  obtain ⟨hr, -⟩ := Checked.Chemistry.SRKAcentric.srk_omega1_unique 1 1 1 Tc vc vl vg ps one_pos
    one_pos hv hc hl h
  have hP : 0 < cubicP 1 1 1 1 0 Tc v := by linarith
  unfold RoundsTo at h1 hr; rw [abs_le] at h1 hr
  have e1 : ps / cubicP 1 1 1 1 0 Tc v * cubicP 1 1 1 1 0 Tc v = ps := div_mul_cancel₀ _ hP.ne'
  have e2 : ps / cubicP 1 1 1 1 0 Tc vc * cubicP 1 1 1 1 0 Tc vc = ps := div_mul_cancel₀ _ hPc.ne'
  nlinarith

end SRK

/-! ## PR at ω = 1 (`Checked.Chemistry.PRAcentric`) -/

section PR
open Checked.Trust.NCB Checked.Trust.NV

/-- The PR isotherm with b = −1 and R = 0 is −a/(v² − 2v − 1): zero (junk) at v = 1 ± √2, with a
non-integrable pole at 1 − √2. -/
theorem pr_junk_maxwell (a T : ℝ) (ha : a ≠ 0) :
    IsMaxwellCoexistence (cubicP 0 a (-1) 2 (-1) T) (1 - Real.sqrt 2) (1 + Real.sqrt 2) 0 := by
  have s := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have s0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hD1 : (1 - Real.sqrt 2) ^ 2 + 2 * (-1) * (1 - Real.sqrt 2) + (-1) * (-1) ^ 2 = 0 := by
    linear_combination s
  have hD2 : (1 + Real.sqrt 2) ^ 2 + 2 * (-1) * (1 + Real.sqrt 2) + (-1) * (-1) ^ 2 = 0 := by
    linear_combination s
  refine maxwell_zero_of_pole _ (fun _ => 0) (fun x => x - (1 + Real.sqrt 2)) (1 - Real.sqrt 2) (-a)
    _ _ (neg_ne_zero.2 ha) (by fun_prop) (by intro h; linarith) continuousAt_const
    (Eventually.of_forall fun x => ?_) (by linarith) ⟨le_rfl, by linarith⟩ ?_ ?_
  · have e : (x - (1 - Real.sqrt 2)) * (x - (1 + Real.sqrt 2)) = x ^ 2 + 2 * (-1) * x + (-1) * (-1) ^ 2 := by
      linear_combination (-1) * s
    rw [e]; unfold cubicP; ring
  · unfold cubicP; rw [hD1]; simp
  · unfold cubicP; rw [hD2]; simp

theorem pr_alpha_pos : 0 < 1 + (0.37464 + 1.54226 * 1 - 0.26992 * 1 ^ 2) * (1 - Real.sqrt (7 / 10)) := by
  have h1 : 0 < 1 - Real.sqrt (7 / 10) := by linarith [sqrt07_lt]
  have hk : (0 : ℝ) < 0.480 + 1.574 * 1 - 0.176 * 1 ^ 2 := by norm_num
  nlinarith [mul_pos hk h1]

/-- `b < v_c` is needed: at v_c = b the junk derivatives meet the critical-point
condition and the "critical pressure" is −1/2, while the coexistence pressure is positive. -/
theorem pr_omega1_unique_h3 : necessity% Checked.Chemistry.PRAcentric.pr_omega1_unique 3 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := pr_crit_witness
  obtain ⟨vl, vg, ps, hl, h, hr, -⟩ := Checked.Chemistry.PRAcentric.pr_omega1_exists
    1 1 1 Tc vc one_pos one_pos hv hc
  have hPc := (crit_RT_pos 1 1 1 2 (-1) Tc vc one_pos one_pos hv (Or.inr ⟨rfl, rfl⟩) hc).2
  have hps : 0 < ps := by
    have := pos_of_roundsTo hr (by norm_num)
    exact (div_pos_iff_of_pos_right hPc).1 this
  refine ⟨1, 1, 1, Tc, 1, vl, vg, ps, one_pos, one_pos,
    crit_at_b 1 1 1 2 (-1) Tc (by simpa using hT.ne') (by norm_num), hl, h, ?_⟩
  rintro ⟨h1, -⟩
  have e : cubicP 1 1 1 2 (-1) Tc 1 = -1 / 2 := by norm_num [cubicP]
  rw [e] at h1
  have := pos_of_roundsTo h1 (by norm_num)
  have : ps / (-1 / 2) < 0 := div_neg_of_pos_of_neg hps (by norm_num)
  linarith

/-- The critical-point condition is needed: at a volume just above b the pressure exceeds 200 times
the coexistence pressure, so the ratio is below 0.005. -/
theorem pr_omega1_unique_h4 : necessity% Checked.Chemistry.PRAcentric.pr_omega1_unique 4 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := pr_crit_witness
  obtain ⟨vl, vg, ps, hl, h, -, -⟩ := Checked.Chemistry.PRAcentric.pr_omega1_exists
    1 1 1 Tc vc one_pos one_pos hv hc
  obtain ⟨v, hv1, hbig⟩ := big_pressure 2 (-1) Tc (200 * |ps| + 1) hT (fun v hv => by nlinarith)
  refine ⟨1, 1, 1, Tc, v, vl, vg, ps, one_pos, one_pos, hv1, hl, h, ?_⟩
  rintro ⟨h1, -⟩
  have hP : 0 < cubicP 1 1 1 2 (-1) Tc v := by linarith [abs_nonneg ps]
  have := pos_of_roundsTo h1 (by norm_num)
  unfold RoundsTo at h1; rw [abs_le] at h1
  have hle : ps / cubicP 1 1 1 2 (-1) Tc v * cubicP 1 1 1 2 (-1) Tc v = ps := div_mul_cancel₀ _ hP.ne'
  nlinarith [le_abs_self ps]

/-- `0 < a_c` is needed: with a_c = 0 and T_c = 0 both isotherms are identically 0. -/
theorem pr_omega1_unique_h1 : necessity% Checked.Chemistry.PRAcentric.pr_omega1_unique 1 := by
  have hz : cubicP 1 (0 * (1 + (0.37464 + 1.54226 * 1 - 0.26992 * 1 ^ 2) * (1 - Real.sqrt (7 / 10))) ^ 2)
      1 2 (-1) (7 / 10 * 0) = fun _ => 0 := by funext x; simp [cubicP]
  refine ⟨1, 0, 1, 0, 2, 2, 3, 0, one_pos, by norm_num, zero_isotherm_critical 1 1 2 (-1) 2,
    by norm_num, ?_, ?_⟩
  · rw [hz]; exact ⟨by norm_num, rfl, rfl, by simp⟩
  · rintro ⟨h1, -⟩; norm_num [RoundsTo, abs_le] at h1

/-- `0 < b` is needed: b = −1, R = 0 (Lean's junk values at the zeros 1 ± √2 of the attraction
denominator give a critical point at v_c = 1 + √2 and a coexistence state at pressure 0). -/
theorem pr_omega1_unique_h2 : necessity% Checked.Chemistry.PRAcentric.pr_omega1_unique 2 := by
  have hα := pr_alpha_pos
  have s := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have s0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  refine ⟨0, 1, -1, 1, 1 + Real.sqrt 2, 1 - Real.sqrt 2, 1 + Real.sqrt 2, 0, one_pos, by linarith,
    crit_at_root 0 1 (-1) 2 (-1) 1 (1 + Real.sqrt 2) (by linarith) one_ne_zero
      (by linear_combination s) ?_, by nlinarith,
    pr_junk_maxwell _ _ (by positivity), ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 + Real.sqrt 2 < x)
    intro h; nlinarith
  · rintro ⟨h1, -⟩; norm_num [RoundsTo, abs_le] at h1

/-- `0 < a_c` is needed for existence: with a_c = 0, T_c = 0 every coexistence pressure is 0. -/
theorem pr_omega1_exists_h1 : necessity% Checked.Chemistry.PRAcentric.pr_omega1_exists 1 := by
  refine ⟨1, 0, 1, 0, 2, by norm_num, by norm_num, zero_isotherm_critical 1 1 2 (-1) 2, ?_⟩
  rintro ⟨vl, vg, ps, -, ⟨-, hpl, -, -⟩, h1, -⟩
  simp [cubicP] at hpl
  subst hpl
  norm_num [RoundsTo, abs_le] at h1

/-- `0 < b` is needed for existence: b = −1, R = 0, v_c = 1 + √2 (junk critical point), where the
"critical pressure" is the junk value 0, so every pressure ratio is 0. -/
theorem pr_omega1_exists_h2 : necessity% Checked.Chemistry.PRAcentric.pr_omega1_exists 2 := by
  have s := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have s0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hD2 : (1 + Real.sqrt 2) ^ 2 + 2 * (-1) * (1 + Real.sqrt 2) + (-1) * (-1) ^ 2 = 0 := by
    linear_combination s
  refine ⟨0, 1, -1, 1, 1 + Real.sqrt 2, one_pos, by linarith,
    crit_at_root 0 1 (-1) 2 (-1) 1 (1 + Real.sqrt 2) (by linarith) one_ne_zero hD2 ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 + Real.sqrt 2 < x)
    intro h; nlinarith
  · rintro ⟨vl, vg, ps, -, -, h1, -⟩
    have e : cubicP 0 1 (-1) 2 (-1) 1 (1 + Real.sqrt 2) = 0 := by unfold cubicP; rw [hD2]; simp
    rw [e] at h1
    norm_num [RoundsTo, abs_le] at h1

/-- `b < v_c` is needed for existence: at v_c = b the "critical pressure" is −1/2, so a positive
ratio needs a negative coexistence pressure, but every coexistence pressure is positive (the
uniqueness theorem at the genuine critical point). -/
theorem pr_omega1_exists_h3 : necessity% Checked.Chemistry.PRAcentric.pr_omega1_exists 3 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := pr_crit_witness
  have hPc := (crit_RT_pos 1 1 1 2 (-1) Tc vc one_pos one_pos hv (Or.inr ⟨rfl, rfl⟩) hc).2
  refine ⟨1, 1, 1, Tc, 1, one_pos, one_pos,
    crit_at_b 1 1 1 2 (-1) Tc (by simpa using hT.ne') (by norm_num), ?_⟩
  rintro ⟨vl, vg, ps, hl, h, h1, -⟩
  obtain ⟨hr, -⟩ := Checked.Chemistry.PRAcentric.pr_omega1_unique 1 1 1 Tc vc vl vg ps one_pos
    one_pos hv hc hl h
  have hps : 0 < ps := (div_pos_iff_of_pos_right hPc).1 (pos_of_roundsTo hr (by norm_num))
  have e : cubicP 1 1 1 2 (-1) Tc 1 = -1 / 2 := by norm_num [cubicP]
  rw [e] at h1
  have := pos_of_roundsTo h1 (by norm_num)
  have : ps / (-1 / 2) < 0 := div_neg_of_pos_of_neg hps (by norm_num)
  linarith

/-- The critical-point condition is needed for existence: at a volume just above b with pressure
above 100 P_c every coexistence ratio is below 0.0002. -/
theorem pr_omega1_exists_h4 : necessity% Checked.Chemistry.PRAcentric.pr_omega1_exists 4 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := pr_crit_witness
  have hPc := (crit_RT_pos 1 1 1 2 (-1) Tc vc one_pos one_pos hv (Or.inr ⟨rfl, rfl⟩) hc).2
  obtain ⟨v, hv1, hbig⟩ := big_pressure 2 (-1) Tc (100 * cubicP 1 1 1 2 (-1) Tc vc) hT (fun v hv => by nlinarith)
  refine ⟨1, 1, 1, Tc, v, one_pos, one_pos, hv1, ?_⟩
  rintro ⟨vl, vg, ps, hl, h, h1, -⟩
  obtain ⟨hr, -⟩ := Checked.Chemistry.PRAcentric.pr_omega1_unique 1 1 1 Tc vc vl vg ps one_pos
    one_pos hv hc hl h
  have hP : 0 < cubicP 1 1 1 2 (-1) Tc v := by linarith
  unfold RoundsTo at h1 hr; rw [abs_le] at h1 hr
  have e1 : ps / cubicP 1 1 1 2 (-1) Tc v * cubicP 1 1 1 2 (-1) Tc v = ps := div_mul_cancel₀ _ hP.ne'
  have e2 : ps / cubicP 1 1 1 2 (-1) Tc vc * cubicP 1 1 1 2 (-1) Tc vc = ps := div_mul_cancel₀ _ hPc.ne'
  nlinarith

end PR

/-! ## PR78 at ω = 1 (`Checked.Chemistry.PR78Acentric`) -/

section PR78
open Checked.Trust.NCB Checked.Trust.NV

/-- The PR isotherm with b = −1 and R = 0 is −a/(v² − 2v − 1): zero (junk) at v = 1 ± √2, with a
non-integrable pole at 1 − √2. -/
theorem pr78_junk_maxwell (a T : ℝ) (ha : a ≠ 0) :
    IsMaxwellCoexistence (cubicP 0 a (-1) 2 (-1) T) (1 - Real.sqrt 2) (1 + Real.sqrt 2) 0 := by
  have s := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have s0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hD1 : (1 - Real.sqrt 2) ^ 2 + 2 * (-1) * (1 - Real.sqrt 2) + (-1) * (-1) ^ 2 = 0 := by
    linear_combination s
  have hD2 : (1 + Real.sqrt 2) ^ 2 + 2 * (-1) * (1 + Real.sqrt 2) + (-1) * (-1) ^ 2 = 0 := by
    linear_combination s
  refine maxwell_zero_of_pole _ (fun _ => 0) (fun x => x - (1 + Real.sqrt 2)) (1 - Real.sqrt 2) (-a)
    _ _ (neg_ne_zero.2 ha) (by fun_prop) (by intro h; linarith) continuousAt_const
    (Eventually.of_forall fun x => ?_) (by linarith) ⟨le_rfl, by linarith⟩ ?_ ?_
  · have e : (x - (1 - Real.sqrt 2)) * (x - (1 + Real.sqrt 2)) = x ^ 2 + 2 * (-1) * x + (-1) * (-1) ^ 2 := by
      linear_combination (-1) * s
    rw [e]; unfold cubicP; ring
  · unfold cubicP; rw [hD1]; simp
  · unfold cubicP; rw [hD2]; simp

theorem pr78_alpha_pos : 0 < 1 + (0.379642 + 1.48503 * 1 - 0.164423 * 1 ^ 2 + 0.016666 * 1 ^ 3) * (1 - Real.sqrt (7 / 10)) := by
  have h1 : 0 < 1 - Real.sqrt (7 / 10) := by linarith [sqrt07_lt]
  have hk : (0 : ℝ) < 0.480 + 1.574 * 1 - 0.176 * 1 ^ 2 := by norm_num
  nlinarith [mul_pos hk h1]

/-- `b < v_c` is needed: at v_c = b the junk derivatives meet the critical-point
condition and the "critical pressure" is −1/2, while the coexistence pressure is positive. -/
theorem pr78_omega1_unique_h3 : necessity% Checked.Chemistry.PR78Acentric.pr78_omega1_unique 3 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := pr_crit_witness
  obtain ⟨vl, vg, ps, hl, h, hr, -⟩ := Checked.Chemistry.PR78Acentric.pr78_omega1_exists
    1 1 1 Tc vc one_pos one_pos hv hc
  have hPc := (crit_RT_pos 1 1 1 2 (-1) Tc vc one_pos one_pos hv (Or.inr ⟨rfl, rfl⟩) hc).2
  have hps : 0 < ps := by
    have := pos_of_roundsTo hr (by norm_num)
    exact (div_pos_iff_of_pos_right hPc).1 this
  refine ⟨1, 1, 1, Tc, 1, vl, vg, ps, one_pos, one_pos,
    crit_at_b 1 1 1 2 (-1) Tc (by simpa using hT.ne') (by norm_num), hl, h, ?_⟩
  rintro ⟨h1, -⟩
  have e : cubicP 1 1 1 2 (-1) Tc 1 = -1 / 2 := by norm_num [cubicP]
  rw [e] at h1
  have := pos_of_roundsTo h1 (by norm_num)
  have : ps / (-1 / 2) < 0 := div_neg_of_pos_of_neg hps (by norm_num)
  linarith

/-- The critical-point condition is needed: at a volume just above b the pressure exceeds 200 times
the coexistence pressure, so the ratio is below 0.005. -/
theorem pr78_omega1_unique_h4 : necessity% Checked.Chemistry.PR78Acentric.pr78_omega1_unique 4 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := pr_crit_witness
  obtain ⟨vl, vg, ps, hl, h, -, -⟩ := Checked.Chemistry.PR78Acentric.pr78_omega1_exists
    1 1 1 Tc vc one_pos one_pos hv hc
  obtain ⟨v, hv1, hbig⟩ := big_pressure 2 (-1) Tc (200 * |ps| + 1) hT (fun v hv => by nlinarith)
  refine ⟨1, 1, 1, Tc, v, vl, vg, ps, one_pos, one_pos, hv1, hl, h, ?_⟩
  rintro ⟨h1, -⟩
  have hP : 0 < cubicP 1 1 1 2 (-1) Tc v := by linarith [abs_nonneg ps]
  have := pos_of_roundsTo h1 (by norm_num)
  unfold RoundsTo at h1; rw [abs_le] at h1
  have hle : ps / cubicP 1 1 1 2 (-1) Tc v * cubicP 1 1 1 2 (-1) Tc v = ps := div_mul_cancel₀ _ hP.ne'
  nlinarith [le_abs_self ps]

/-- `0 < a_c` is needed: with a_c = 0 and T_c = 0 both isotherms are identically 0. -/
theorem pr78_omega1_unique_h1 : necessity% Checked.Chemistry.PR78Acentric.pr78_omega1_unique 1 := by
  have hz : cubicP 1 (0 * (1 + (0.379642 + 1.48503 * 1 - 0.164423 * 1 ^ 2 + 0.016666 * 1 ^ 3) * (1 - Real.sqrt (7 / 10))) ^ 2)
      1 2 (-1) (7 / 10 * 0) = fun _ => 0 := by funext x; simp [cubicP]
  refine ⟨1, 0, 1, 0, 2, 2, 3, 0, one_pos, by norm_num, zero_isotherm_critical 1 1 2 (-1) 2,
    by norm_num, ?_, ?_⟩
  · rw [hz]; exact ⟨by norm_num, rfl, rfl, by simp⟩
  · rintro ⟨h1, -⟩; norm_num [RoundsTo, abs_le] at h1

/-- `0 < b` is needed: b = −1, R = 0 (Lean's junk values at the zeros 1 ± √2 of the attraction
denominator give a critical point at v_c = 1 + √2 and a coexistence state at pressure 0). -/
theorem pr78_omega1_unique_h2 : necessity% Checked.Chemistry.PR78Acentric.pr78_omega1_unique 2 := by
  have hα := pr78_alpha_pos
  have s := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have s0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  refine ⟨0, 1, -1, 1, 1 + Real.sqrt 2, 1 - Real.sqrt 2, 1 + Real.sqrt 2, 0, one_pos, by linarith,
    crit_at_root 0 1 (-1) 2 (-1) 1 (1 + Real.sqrt 2) (by linarith) one_ne_zero
      (by linear_combination s) ?_, by nlinarith,
    pr78_junk_maxwell _ _ (by positivity), ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 + Real.sqrt 2 < x)
    intro h; nlinarith
  · rintro ⟨h1, -⟩; norm_num [RoundsTo, abs_le] at h1

/-- `0 < a_c` is needed for existence: with a_c = 0, T_c = 0 every coexistence pressure is 0. -/
theorem pr78_omega1_exists_h1 : necessity% Checked.Chemistry.PR78Acentric.pr78_omega1_exists 1 := by
  refine ⟨1, 0, 1, 0, 2, by norm_num, by norm_num, zero_isotherm_critical 1 1 2 (-1) 2, ?_⟩
  rintro ⟨vl, vg, ps, -, ⟨-, hpl, -, -⟩, h1, -⟩
  simp [cubicP] at hpl
  subst hpl
  norm_num [RoundsTo, abs_le] at h1

/-- `0 < b` is needed for existence: b = −1, R = 0, v_c = 1 + √2 (junk critical point), where the
"critical pressure" is the junk value 0, so every pressure ratio is 0. -/
theorem pr78_omega1_exists_h2 : necessity% Checked.Chemistry.PR78Acentric.pr78_omega1_exists 2 := by
  have s := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have s0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hD2 : (1 + Real.sqrt 2) ^ 2 + 2 * (-1) * (1 + Real.sqrt 2) + (-1) * (-1) ^ 2 = 0 := by
    linear_combination s
  refine ⟨0, 1, -1, 1, 1 + Real.sqrt 2, one_pos, by linarith,
    crit_at_root 0 1 (-1) 2 (-1) 1 (1 + Real.sqrt 2) (by linarith) one_ne_zero hD2 ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 + Real.sqrt 2 < x)
    intro h; nlinarith
  · rintro ⟨vl, vg, ps, -, -, h1, -⟩
    have e : cubicP 0 1 (-1) 2 (-1) 1 (1 + Real.sqrt 2) = 0 := by unfold cubicP; rw [hD2]; simp
    rw [e] at h1
    norm_num [RoundsTo, abs_le] at h1

/-- `b < v_c` is needed for existence: at v_c = b the "critical pressure" is −1/2, so a positive
ratio needs a negative coexistence pressure, but every coexistence pressure is positive (the
uniqueness theorem at the genuine critical point). -/
theorem pr78_omega1_exists_h3 : necessity% Checked.Chemistry.PR78Acentric.pr78_omega1_exists 3 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := pr_crit_witness
  have hPc := (crit_RT_pos 1 1 1 2 (-1) Tc vc one_pos one_pos hv (Or.inr ⟨rfl, rfl⟩) hc).2
  refine ⟨1, 1, 1, Tc, 1, one_pos, one_pos,
    crit_at_b 1 1 1 2 (-1) Tc (by simpa using hT.ne') (by norm_num), ?_⟩
  rintro ⟨vl, vg, ps, hl, h, h1, -⟩
  obtain ⟨hr, -⟩ := Checked.Chemistry.PR78Acentric.pr78_omega1_unique 1 1 1 Tc vc vl vg ps one_pos
    one_pos hv hc hl h
  have hps : 0 < ps := (div_pos_iff_of_pos_right hPc).1 (pos_of_roundsTo hr (by norm_num))
  have e : cubicP 1 1 1 2 (-1) Tc 1 = -1 / 2 := by norm_num [cubicP]
  rw [e] at h1
  have := pos_of_roundsTo h1 (by norm_num)
  have : ps / (-1 / 2) < 0 := div_neg_of_pos_of_neg hps (by norm_num)
  linarith

/-- The critical-point condition is needed for existence: at a volume just above b with pressure
above 100 P_c every coexistence ratio is below 0.0002. -/
theorem pr78_omega1_exists_h4 : necessity% Checked.Chemistry.PR78Acentric.pr78_omega1_exists 4 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := pr_crit_witness
  have hPc := (crit_RT_pos 1 1 1 2 (-1) Tc vc one_pos one_pos hv (Or.inr ⟨rfl, rfl⟩) hc).2
  obtain ⟨v, hv1, hbig⟩ := big_pressure 2 (-1) Tc (100 * cubicP 1 1 1 2 (-1) Tc vc) hT (fun v hv => by nlinarith)
  refine ⟨1, 1, 1, Tc, v, one_pos, one_pos, hv1, ?_⟩
  rintro ⟨vl, vg, ps, hl, h, h1, -⟩
  obtain ⟨hr, -⟩ := Checked.Chemistry.PR78Acentric.pr78_omega1_unique 1 1 1 Tc vc vl vg ps one_pos
    one_pos hv hc hl h
  have hP : 0 < cubicP 1 1 1 2 (-1) Tc v := by linarith
  unfold RoundsTo at h1 hr; rw [abs_le] at h1 hr
  have e1 : ps / cubicP 1 1 1 2 (-1) Tc v * cubicP 1 1 1 2 (-1) Tc v = ps := div_mul_cancel₀ _ hP.ne'
  have e2 : ps / cubicP 1 1 1 2 (-1) Tc vc * cubicP 1 1 1 2 (-1) Tc vc = ps := div_mul_cancel₀ _ hPc.ne'
  nlinarith

end PR78

/-! ## Redlich–Kwong (`Checked.Chemistry.RKAcentric`) -/

section RK
open Checked.Trust.NCB Checked.Trust.NV

/-- `0 < R` is redundant: a critical point with v_c > b > 0, T_c > 0 and A > 0 forces R T_c > 0. -/
theorem rk_coexistence_unique_r1 : dropped% Checked.Chemistry.RKAcentric.rk_coexistence_unique 1 := by
  intro R A b Tc vc vl vg ps hA hb hTc hvc hc hl h
  have hRT := (crit_RT_pos R (A / Real.sqrt Tc) b 1 0 Tc vc (div_pos hA (Real.sqrt_pos.2 hTc)) hb hvc
    (Or.inl ⟨rfl, rfl⟩) hc).1
  have hR : 0 < R := by by_contra hR; nlinarith [not_lt.1 hR]
  exact Checked.Chemistry.RKAcentric.rk_coexistence_unique R A b Tc vc vl vg ps hR hA hb hTc hvc hc hl h

theorem rk_coexistence_exists_r1 : dropped% Checked.Chemistry.RKAcentric.rk_coexistence_exists 1 := by
  intro R A b Tc vc hA hb hTc hvc hc
  have hRT := (crit_RT_pos R (A / Real.sqrt Tc) b 1 0 Tc vc (div_pos hA (Real.sqrt_pos.2 hTc)) hb hvc
    (Or.inl ⟨rfl, rfl⟩) hc).1
  have hR : 0 < R := by by_contra hR; nlinarith [not_lt.1 hR]
  exact Checked.Chemistry.RKAcentric.rk_coexistence_exists R A b Tc vc hR hA hb hTc hvc hc

/-- With attraction a ≤ 0, R T > 0 and v > b > 0 the RK isotherm has negative slope: no critical
point. -/
theorem rk_no_crit (R a b T v : ℝ) (ha : a ≤ 0) (hRT : 0 < R * T) (hb : 0 < b) (hv : b < v) :
    ¬ IsCriticalIsotherm (cubicP R a b 1 0 T) v := by
  intro hc
  have hv0 : v - b ≠ 0 := sub_ne_zero.2 (ne_of_gt hv)
  have hD : 0 < v ^ 2 + 1 * b * v + 0 * b ^ 2 := by nlinarith
  have hd := (hasDerivAt_P R a b 1 0 T v hv0 hD.ne').deriv
  rw [hc.1] at hd
  have h1 : 0 < R * T / (v - b) ^ 2 := div_pos hRT (by positivity)
  have h2 : a * (2 * v + 1 * b) / (v ^ 2 + 1 * b * v + 0 * b ^ 2) ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg ha (by linarith)) (by positivity)
  rw [neg_div] at hd
  linarith

/-- `0 < A` is redundant: with A ≤ 0 (and R, T_c > 0) there is no critical point. -/
theorem rk_coexistence_unique_r2 : dropped% Checked.Chemistry.RKAcentric.rk_coexistence_unique 2 := by
  intro R A b Tc vc vl vg ps hR hb hTc hvc hc hl h
  rcases lt_or_ge 0 A with hA | hA
  · exact Checked.Chemistry.RKAcentric.rk_coexistence_unique R A b Tc vc vl vg ps hR hA hb hTc hvc hc hl h
  · exact absurd hc (rk_no_crit R _ b Tc vc (div_nonpos_of_nonpos_of_nonneg hA (Real.sqrt_nonneg _))
      (mul_pos hR hTc) hb hvc)

theorem rk_coexistence_exists_r2 : dropped% Checked.Chemistry.RKAcentric.rk_coexistence_exists 2 := by
  intro R A b Tc vc hR hb hTc hvc hc
  rcases lt_or_ge 0 A with hA | hA
  · exact Checked.Chemistry.RKAcentric.rk_coexistence_exists R A b Tc vc hR hA hb hTc hvc hc
  · exact absurd hc (rk_no_crit R _ b Tc vc (div_nonpos_of_nonpos_of_nonneg hA (Real.sqrt_nonneg _))
      (mul_pos hR hTc) hb hvc)

/-- `0 < b` is needed: b = −1, R = 1, A = 3/2, T_c = 10/7 (so 0.7 T_c = 1): v_c = 1 is a junk critical
point (zero of the attraction denominator), and the isotherm 1/(v + 1) − (3/2)/(v² − v) at T = 1 has
zeros −1/2 and 3 with a non-integrable pole at 0 between them, a coexistence state at pressure 0. -/
theorem rk_coexistence_unique_h3 : necessity% Checked.Chemistry.RKAcentric.rk_coexistence_unique 3 := by
  have e7 : (7 / 10 : ℝ) * (10 / 7) = 1 := by norm_num
  refine ⟨1, 3 / 2, -1, 10 / 7, 1, -1 / 2, 3, 0, one_pos, by norm_num, by norm_num, by norm_num,
    crit_at_root 1 _ (-1) 1 0 (10 / 7) 1 (by norm_num) (by positivity) (by norm_num) ?_,
    by norm_num, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    intro h; nlinarith
  · rw [e7, Real.sqrt_one, div_one]
    refine maxwell_zero_of_pole _ (fun x => 1 * 1 / (x - -1)) (fun x => x - 1) 0 (-(3 / 2)) _ _
      (by norm_num) (by fun_prop) (by norm_num)
      (continuousAt_const.div (by fun_prop) (by norm_num))
      (Eventually.of_forall fun x => by unfold cubicP; ring) (by norm_num) ⟨by norm_num, by norm_num⟩
      (by norm_num [cubicP]) (by norm_num [cubicP])
  · rintro ⟨h1, -⟩; norm_num [RoundsTo, abs_le] at h1

/-- `0 < T_c` is needed: T_c = 0 gives attraction A/√0 = 0, both isotherms identically 0. -/
theorem rk_coexistence_unique_h4 : necessity% Checked.Chemistry.RKAcentric.rk_coexistence_unique 4 := by
  have hz : ∀ T : ℝ, T = 0 → cubicP 1 (1 / Real.sqrt T) 1 1 0 T = fun _ => 0 := by
    intro T hT; subst hT; funext x; simp [cubicP]
  refine ⟨1, 1, 1, 0, 2, 2, 3, 0, one_pos, one_pos, one_pos, by norm_num, ?_, by norm_num, ?_, ?_⟩
  · rw [hz 0 rfl]; simp [IsCriticalIsotherm]
  · rw [hz _ (by norm_num)]; exact ⟨by norm_num, rfl, rfl, by simp⟩
  · rintro ⟨h1, -⟩; norm_num [RoundsTo, abs_le] at h1

theorem rk_coexistence_exists_h4 : necessity% Checked.Chemistry.RKAcentric.rk_coexistence_exists 4 := by
  have hz : ∀ T : ℝ, T = 0 → cubicP 1 (1 / Real.sqrt T) 1 1 0 T = fun _ => 0 := by
    intro T hT; subst hT; funext x; simp [cubicP]
  refine ⟨1, 1, 1, 0, 2, one_pos, one_pos, one_pos, by norm_num, ?_, ?_⟩
  · rw [hz 0 rfl]; simp [IsCriticalIsotherm]
  · rintro ⟨vl, vg, ps, -, ⟨-, hpl, -, -⟩, h1, -⟩
    rw [hz _ (by norm_num)] at hpl
    subst hpl
    norm_num [RoundsTo, abs_le] at h1

/-- `b < v_c` is needed: at v_c = b the "critical pressure" is −1/2 < 0, while the coexistence
pressure is positive. -/
theorem rk_coexistence_unique_h5 : necessity% Checked.Chemistry.RKAcentric.rk_coexistence_unique 5 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := rk_crit_witness
  have hA1 : Real.sqrt Tc / Real.sqrt Tc = 1 := div_self (Real.sqrt_pos.2 hT).ne'
  obtain ⟨vl, vg, ps, hl, h, hr, -⟩ := Checked.Chemistry.RKAcentric.rk_coexistence_exists
    1 (Real.sqrt Tc) 1 Tc vc one_pos (Real.sqrt_pos.2 hT) one_pos hT hv hc
  rw [hA1] at hc hr
  have hPc := (crit_RT_pos 1 1 1 1 0 Tc vc one_pos one_pos hv (Or.inl ⟨rfl, rfl⟩) hc).2
  have hps : 0 < ps := (div_pos_iff_of_pos_right hPc).1 (pos_of_roundsTo hr (by norm_num))
  refine ⟨1, Real.sqrt Tc, 1, Tc, 1, vl, vg, ps, one_pos, Real.sqrt_pos.2 hT, one_pos, hT, ?_, hl, h, ?_⟩
  · rw [hA1]; exact crit_at_b 1 1 1 1 0 Tc (by simpa using hT.ne') (by norm_num)
  · rw [hA1]
    rintro ⟨h1, -⟩
    have e : cubicP 1 1 1 1 0 Tc 1 = -1 / 2 := by norm_num [cubicP]
    rw [e] at h1
    have := pos_of_roundsTo h1 (by norm_num)
    have : ps / (-1 / 2) < 0 := div_neg_of_pos_of_neg hps (by norm_num)
    linarith

/-- The critical-point condition is needed: at a volume just above b the pressure exceeds 200 times
the coexistence pressure. -/
theorem rk_coexistence_unique_h6 : necessity% Checked.Chemistry.RKAcentric.rk_coexistence_unique 6 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := rk_crit_witness
  have hA1 : Real.sqrt Tc / Real.sqrt Tc = 1 := div_self (Real.sqrt_pos.2 hT).ne'
  obtain ⟨vl, vg, ps, hl, h, -, -⟩ := Checked.Chemistry.RKAcentric.rk_coexistence_exists
    1 (Real.sqrt Tc) 1 Tc vc one_pos (Real.sqrt_pos.2 hT) one_pos hT hv hc
  obtain ⟨v, hv1, hbig⟩ := big_pressure 1 0 Tc (200 * |ps| + 1) hT (fun v hv => by nlinarith)
  refine ⟨1, Real.sqrt Tc, 1, Tc, v, vl, vg, ps, one_pos, Real.sqrt_pos.2 hT, one_pos, hT, hv1, hl, h, ?_⟩
  rw [hA1]
  rintro ⟨h1, -⟩
  have hP : 0 < cubicP 1 1 1 1 0 Tc v := by linarith [abs_nonneg ps]
  have := pos_of_roundsTo h1 (by norm_num)
  unfold RoundsTo at h1; rw [abs_le] at h1
  have hle : ps / cubicP 1 1 1 1 0 Tc v * cubicP 1 1 1 1 0 Tc v = ps := div_mul_cancel₀ _ hP.ne'
  nlinarith [le_abs_self ps]

/-- `b < v_c` is needed for existence: at v_c = b the "critical pressure" is −1/2, so a ratio 0.087
needs a negative coexistence pressure, but every coexistence pressure is positive. -/
theorem rk_coexistence_exists_h5 : necessity% Checked.Chemistry.RKAcentric.rk_coexistence_exists 5 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := rk_crit_witness
  have hA1 : Real.sqrt Tc / Real.sqrt Tc = 1 := div_self (Real.sqrt_pos.2 hT).ne'
  have hc' := hc
  rw [hA1] at hc'
  have hPc := (crit_RT_pos 1 1 1 1 0 Tc vc one_pos one_pos hv (Or.inl ⟨rfl, rfl⟩) hc').2
  refine ⟨1, Real.sqrt Tc, 1, Tc, 1, one_pos, Real.sqrt_pos.2 hT, one_pos, hT, ?_, ?_⟩
  · rw [hA1]; exact crit_at_b 1 1 1 1 0 Tc (by simpa using hT.ne') (by norm_num)
  · rintro ⟨vl, vg, ps, hl, h, h1, -⟩
    obtain ⟨hr, -⟩ := Checked.Chemistry.RKAcentric.rk_coexistence_unique 1 (Real.sqrt Tc) 1 Tc vc vl vg
      ps one_pos (Real.sqrt_pos.2 hT) one_pos hT hv hc hl h
    rw [hA1] at hr h1
    have hps : 0 < ps := (div_pos_iff_of_pos_right hPc).1 (pos_of_roundsTo hr (by norm_num))
    have e : cubicP 1 1 1 1 0 Tc 1 = -1 / 2 := by norm_num [cubicP]
    rw [e] at h1
    have := pos_of_roundsTo h1 (by norm_num)
    have : ps / (-1 / 2) < 0 := div_neg_of_pos_of_neg hps (by norm_num)
    linarith

/-- The critical-point condition is needed for existence: at a volume just above b with pressure
above 100 P_c every coexistence ratio is below 0.001. -/
theorem rk_coexistence_exists_h6 : necessity% Checked.Chemistry.RKAcentric.rk_coexistence_exists 6 := by
  obtain ⟨Tc, vc, hT, hv, hc⟩ := rk_crit_witness
  have hA1 : Real.sqrt Tc / Real.sqrt Tc = 1 := div_self (Real.sqrt_pos.2 hT).ne'
  have hc' := hc
  rw [hA1] at hc'
  have hPc := (crit_RT_pos 1 1 1 1 0 Tc vc one_pos one_pos hv (Or.inl ⟨rfl, rfl⟩) hc').2
  obtain ⟨v, hv1, hbig⟩ := big_pressure 1 0 Tc (100 * cubicP 1 1 1 1 0 Tc vc) hT (fun v hv => by nlinarith)
  refine ⟨1, Real.sqrt Tc, 1, Tc, v, one_pos, Real.sqrt_pos.2 hT, one_pos, hT, hv1, ?_⟩
  rintro ⟨vl, vg, ps, hl, h, h1, -⟩
  obtain ⟨hr, -⟩ := Checked.Chemistry.RKAcentric.rk_coexistence_unique 1 (Real.sqrt Tc) 1 Tc vc vl vg
    ps one_pos (Real.sqrt_pos.2 hT) one_pos hT hv hc hl h
  rw [hA1] at hr h1
  have hP : 0 < cubicP 1 1 1 1 0 Tc v := by linarith
  unfold RoundsTo at h1 hr; rw [abs_le] at h1 hr
  have e1 : ps / cubicP 1 1 1 1 0 Tc v * cubicP 1 1 1 1 0 Tc v = ps := div_mul_cancel₀ _ hP.ne'
  have e2 : ps / cubicP 1 1 1 1 0 Tc vc * cubicP 1 1 1 1 0 Tc vc = ps := div_mul_cancel₀ _ hPc.ne'
  nlinarith

end RK

end Checked.Trust.NecessityO
