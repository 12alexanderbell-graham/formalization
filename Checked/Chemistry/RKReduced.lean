import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Records.Basic
import Checked.Chemistry.CubicEOS
import Checked.Chemistry.Coexistence

/-!
# Redlich–Kwong coexistence at seven tenths of the critical temperature, reduced variables (run 2026-11-04T1828Z)

Promoted from `Work/Chemistry/RKReduced.lean` in the same run (imports narrowed, namespace
changed; proofs unchanged).

Reduced volume `x = v/b`, `θ = R T b / a` (attraction `a` at the temperature `T`), reduced
pressure `π = p b² / a`. The RK isotherm is `(a/b²) · g θ x` with
`g θ x = θ/(x−1) − 1/(x² + x)`; `ψ θ π x = θ log(x−1) + (log(x+1) − log x) − π x` is a primitive
of `g θ − π` on `x > 1`. The derivative of `g θ` has the sign of
`q θ x = (2x+1)(x−1)² − θ(x²+x)²`, which is linear in `θ`.

For every `θ` in a narrow rational interval around its value at seven tenths of the critical
temperature (endpoints in `reduced_window`), every Maxwell coexistence state has its reduced
pressure in a narrow rational window (`reduced_window`; the numbers are in its statement and in
the generator). Route as for van der Waals (`Checked.Chemistry.CoexistenceReduced`): Rolle gives
two critical points of `g`, which are roots of `q`; these are localised in two rational intervals
(sign of `q` and of its derivative on generated subintervals); comparison with rational brackets
and certified logarithms (generated: `runs/2026-11-04T1828Z/scripts/gen_rk.py`).
`rk_unique_core` turns the window into the statement of
`Checked.Chemistry.RKAcentric.rk_coexistence_unique` (θ and the critical pressure from the
critical point via `Checked.Chemistry.CubicEOS.reduced`).
-/

namespace Checked.Chemistry.RKReduced

open Real Set

noncomputable def g (θ x : ℝ) : ℝ := θ / (x - 1) - 1 / (x ^ 2 + x)

noncomputable def ψ (θ p x : ℝ) : ℝ :=
  θ * Real.log (x - 1) + (Real.log (x + 1) - Real.log x) - p * x

def q (θ x : ℝ) : ℝ := (2 * x + 1) * (x - 1) ^ 2 - θ * (x ^ 2 + x) ^ 2

def dq (θ x : ℝ) : ℝ := 6 * x * (x - 1) - 2 * θ * x * (x + 1) * (2 * x + 1)

lemma hasDerivAt_g (θ : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (g θ) (q θ x / ((x - 1) ^ 2 * (x ^ 2 + x) ^ 2)) x := by
  have h1 : x - 1 ≠ 0 := by linarith
  have h2 : x ^ 2 + x ≠ 0 := by positivity
  have hA : HasDerivAt (fun y => θ / (y - 1)) (-θ / (x - 1) ^ 2) x := by
    have := (((hasDerivAt_id x).sub_const 1).inv h1).const_mul θ
    convert this using 1
    · ext y; simp [div_eq_mul_inv]
    · simp; field_simp
  have hB : HasDerivAt (fun y => 1 / (y ^ 2 + y)) (-(2 * x + 1) / (x ^ 2 + x) ^ 2) x := by
    have := ((hasDerivAt_pow 2 x).add (hasDerivAt_id x)).inv h2
    convert this using 1
    · ext y; simp
    · simp
  have := hA.sub hB
  convert this using 1
  · ext y; simp [g]
  · unfold q; field_simp; ring

lemma hasDerivAt_ψ (θ p : ℝ) {x : ℝ} (hx : 1 < x) : HasDerivAt (ψ θ p) (g θ x - p) x := by
  have h1 : x - 1 ≠ 0 := by linarith
  have h0 : x ≠ 0 := by linarith
  have h2 : x + 1 ≠ 0 := by linarith
  have hL1 := ((hasDerivAt_id x).sub_const 1).log h1
  have hL2 := ((hasDerivAt_id x).add_const 1).log h2
  have hL3 := (hasDerivAt_id x).log h0
  have := ((hL1.const_mul θ).add (hL2.sub hL3)).sub ((hasDerivAt_id x).const_mul p)
  convert this using 1
  · ext y; simp [ψ]
  · simp [g]; field_simp; ring

lemma hasDerivAt_q (θ x : ℝ) : HasDerivAt (q θ) (dq θ x) x := by
  have := ((((hasDerivAt_id x).const_mul 2).add_const 1).mul
    (((hasDerivAt_id x).sub_const 1).pow 2)).sub
    (((((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).pow 2).const_mul θ)
  convert this using 1
  · ext y; simp [q]
  · simp [dq]; ring

lemma continuousOn_g (θ : ℝ) {s t : ℝ} (hs : 1 < s) : ContinuousOn (g θ) (Icc s t) := fun x hx =>
  (hasDerivAt_g θ (by linarith [hx.1] : 1 < x)).continuousAt.continuousWithinAt

lemma continuousOn_ψ (θ p : ℝ) {s t : ℝ} (hs : 1 < s) : ContinuousOn (ψ θ p) (Icc s t) :=
  fun x hx => (hasDerivAt_ψ θ p (by linarith [hx.1] : 1 < x)).continuousAt.continuousWithinAt

lemma log_series' (x : ℝ) (h : |x| < 1) (n : ℕ) :
    |(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) + Real.log (1 - x)| ≤ |x| ^ (n + 1) / (1 - |x|) :=
  Real.abs_log_sub_add_sum_range_le h n

/-! ## Sign of `q` and `q'` on subintervals (crude monotone bounds) -/

lemma q_neg_piece {θ a b x : ℝ} (hθ0 : 1187001329 / 10000000000 ≤ θ) (_hθ1 : θ ≤ 593500771 / 5000000000)
    (ha : 1 ≤ a) (hax : a ≤ x) (hxb : x ≤ b)
    (hc : (2 * b + 1) * (b - 1) ^ 2 < 1187001329 / 10000000000 * (a ^ 2 + a) ^ 2) : q θ x < 0 := by
  have e1 : (2 * x + 1) * (x - 1) ^ 2 ≤ (2 * b + 1) * (b - 1) ^ 2 :=
    mul_le_mul (by linarith) (pow_le_pow_left₀ (by linarith) (by linarith) 2) (by positivity)
      (by linarith)
  have e2 : (a ^ 2 + a) ^ 2 ≤ (x ^ 2 + x) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) 2
  have e3 : 1187001329 / 10000000000 * (a ^ 2 + a) ^ 2 ≤ θ * (x ^ 2 + x) ^ 2 :=
    mul_le_mul hθ0 e2 (by positivity) (by linarith)
  unfold q; linarith

lemma q_pos_piece {θ a b x : ℝ} (_hθ0 : 1187001329 / 10000000000 ≤ θ) (hθ1 : θ ≤ 593500771 / 5000000000)
    (ha : 1 ≤ a) (hax : a ≤ x) (hxb : x ≤ b)
    (hc : 593500771 / 5000000000 * (b ^ 2 + b) ^ 2 < (2 * a + 1) * (a - 1) ^ 2) : 0 < q θ x := by
  have e1 : (2 * a + 1) * (a - 1) ^ 2 ≤ (2 * x + 1) * (x - 1) ^ 2 :=
    mul_le_mul (by linarith) (pow_le_pow_left₀ (by linarith) (by linarith) 2) (by positivity)
      (by linarith)
  have e2 : (x ^ 2 + x) ^ 2 ≤ (b ^ 2 + b) ^ 2 :=
    pow_le_pow_left₀ (by nlinarith) (by nlinarith) 2
  have hθ : 0 ≤ θ := by linarith
  have e3 : θ * (x ^ 2 + x) ^ 2 ≤ 593500771 / 5000000000 * (b ^ 2 + b) ^ 2 :=
    mul_le_mul hθ1 e2 (by positivity) (by norm_num)
  unfold q; linarith

lemma dq_pos_piece {θ a b x : ℝ} (_hθ0 : 1187001329 / 10000000000 ≤ θ) (hθ1 : θ ≤ 593500771 / 5000000000)
    (ha : 1 ≤ a) (hax : a ≤ x) (hxb : x ≤ b)
    (hc : 2 * (593500771 / 5000000000) * b * (b + 1) * (2 * b + 1) < 6 * a * (a - 1)) : 0 < dq θ x := by
  have e1 : 6 * a * (a - 1) ≤ 6 * x * (x - 1) := by nlinarith
  have hθ : 0 ≤ θ := by linarith
  have e2 : x * (x + 1) * (2 * x + 1) ≤ b * (b + 1) * (2 * b + 1) := by
    have h1 : x * (x + 1) ≤ b * (b + 1) := by nlinarith
    exact mul_le_mul h1 (by linarith) (by linarith) (by nlinarith)
  have e3 : θ * (x * (x + 1) * (2 * x + 1)) ≤ 593500771 / 5000000000 * (b * (b + 1) * (2 * b + 1)) :=
    mul_le_mul hθ1 e2 (by have : 0 ≤ x := (by linarith); positivity) (by norm_num)
  unfold dq; nlinarith

lemma dq_neg_piece {θ a b x : ℝ} (hθ0 : 1187001329 / 10000000000 ≤ θ) (_hθ1 : θ ≤ 593500771 / 5000000000)
    (ha : 1 ≤ a) (hax : a ≤ x) (hxb : x ≤ b)
    (hc : 6 * b * (b - 1) < 2 * (1187001329 / 10000000000) * a * (a + 1) * (2 * a + 1)) : dq θ x < 0 := by
  have e1 : 6 * x * (x - 1) ≤ 6 * b * (b - 1) := by nlinarith
  have e2 : a * (a + 1) * (2 * a + 1) ≤ x * (x + 1) * (2 * x + 1) := by
    have h1 : a * (a + 1) ≤ x * (x + 1) := by nlinarith
    exact mul_le_mul h1 (by linarith) (by linarith) (by nlinarith)
  have e3 : 1187001329 / 10000000000 * (a * (a + 1) * (2 * a + 1)) ≤ θ * (x * (x + 1) * (2 * x + 1)) :=
    mul_le_mul hθ0 e2 (by have : 0 ≤ a := (by linarith); positivity) (by linarith)
  unfold dq; nlinarith

/-! ## Generated certificates -/

lemma logA_lo : 1338265344913 / 250000000000 < Real.log (((844017 / 10000) - 1) / ((6973967 / 5000000) - 1)) := by
  have e : (((844017 / 10000) - 1) / ((6973967 / 5000000) - 1) : ℝ) = (2:ℝ) ^ 8 * (1 - (17479 / 100000)) * (325787890625 / 325787461614) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have h := log_series' (17479 / 100000) (by norm_num [abs_lt]) 14
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have u1 : Real.log (325787890625 / 325787461614 : ℝ) ≤ 325787890625 / 325787461614 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have u2 : 1 - (325787890625 / 325787461614 : ℝ)⁻¹ ≤ Real.log (325787890625 / 325787461614) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  push_cast
  norm_num at h u1 u2 ⊢
  linarith [h.1, h.2]

lemma logB_lo : -26438609853 / 50000000000 < Real.log ((((844017 / 10000) + 1) / (844017 / 10000)) / (((6973967 / 5000000) + 1) / (6973967 / 5000000))) := by
  have e : ((((844017 / 10000) + 1) / (844017 / 10000)) / (((6973967 / 5000000) + 1) / (6973967 / 5000000)) : ℝ) = (1 - (-8933 / 50000)) / (2:ℝ) ^ 1 * (85084091077700000 / 85084364728090941) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  have h := log_series' (-8933 / 50000) (by norm_num [abs_lt]) 14
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have u1 : Real.log (85084091077700000 / 85084364728090941 : ℝ) ≤ 85084091077700000 / 85084364728090941 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have u2 : 1 - (85084091077700000 / 85084364728090941 : ℝ)⁻¹ ≤ Real.log (85084091077700000 / 85084364728090941) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  push_cast
  norm_num at h u1 u2 ⊢
  linarith [h.1, h.2]

lemma logC_hi : Real.log (((52733 / 625) - 1) / ((3486981 / 2500000) - 1)) < 42821738727 / 8000000000 := by
  have e : (((52733 / 625) - 1) / ((3486981 / 2500000) - 1) : ℝ) = (2:ℝ) ^ 8 * (1 - (17507 / 100000)) * (81418750000 / 81419023633) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have h := log_series' (17507 / 100000) (by norm_num [abs_lt]) 14
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have u1 : Real.log (81418750000 / 81419023633 : ℝ) ≤ 81418750000 / 81419023633 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have u2 : 1 - (81418750000 / 81419023633 : ℝ)⁻¹ ≤ Real.log (81418750000 / 81419023633) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  push_cast
  norm_num at h u1 u2 ⊢
  linarith [h.1, h.2]

lemma logD_hi : Real.log ((((52733 / 625) + 1) / (52733 / 625)) / (((3486981 / 2500000) + 1) / (3486981 / 2500000))) < -528768485147 / 1000000000000 := by
  have e : ((((52733 / 625) + 1) / (52733 / 625)) / (((3486981 / 2500000) + 1) / (3486981 / 2500000)) : ℝ) = (1 - (-8933 / 50000)) / (2:ℝ) ^ 1 * (18605833219800000 / 18605824006879109) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  have h := log_series' (-8933 / 50000) (by norm_num [abs_lt]) 14
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have u1 : Real.log (18605833219800000 / 18605824006879109 : ℝ) ≤ 18605833219800000 / 18605824006879109 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have u2 : 1 - (18605833219800000 / 18605824006879109 : ℝ)⁻¹ ≤ Real.log (18605833219800000 / 18605824006879109) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  push_cast
  norm_num at h u1 u2 ⊢
  linarith [h.1, h.2]

lemma q_neg_L {θ x : ℝ} (hθ0 : (1187001329 / 10000000000) ≤ θ) (hθ1 : θ ≤ (593500771 / 5000000000)) (h1 : (1) < x) (h2 : x ≤ (8 / 5)) :
    q θ x < 0 := by
  rcases le_or_gt x ((11 / 10)) with c1 | c1
  · exact q_neg_piece hθ0 hθ1 (a := (1)) (b := (11 / 10)) (by norm_num) (by linarith) c1 (by norm_num)
  rcases le_or_gt x ((6 / 5)) with c2 | c2
  · exact q_neg_piece hθ0 hθ1 (a := (11 / 10)) (b := (6 / 5)) (by norm_num) (by linarith) c2 (by norm_num)
  rcases le_or_gt x ((13 / 10)) with c3 | c3
  · exact q_neg_piece hθ0 hθ1 (a := (6 / 5)) (b := (13 / 10)) (by norm_num) (by linarith) c3 (by norm_num)
  rcases le_or_gt x ((7 / 5)) with c4 | c4
  · exact q_neg_piece hθ0 hθ1 (a := (13 / 10)) (b := (7 / 5)) (by norm_num) (by linarith) c4 (by norm_num)
  rcases le_or_gt x ((3 / 2)) with c5 | c5
  · exact q_neg_piece hθ0 hθ1 (a := (7 / 5)) (b := (3 / 2)) (by norm_num) (by linarith) c5 (by norm_num)
  exact q_neg_piece hθ0 hθ1 (a := (3 / 2)) (b := (8 / 5)) (by norm_num) (by linarith) h2 (by norm_num)

lemma dq_pos_W1 {θ x : ℝ} (hθ0 : (1187001329 / 10000000000) ≤ θ) (hθ1 : θ ≤ (593500771 / 5000000000)) (h1 : (8 / 5) ≤ x) (h2 : x ≤ (21 / 10)) :
    0 < dq θ x := by
  rcases le_or_gt x ((17 / 10)) with c1 | c1
  · exact dq_pos_piece hθ0 hθ1 (a := (8 / 5)) (b := (17 / 10)) (by norm_num) (by linarith) c1 (by norm_num)
  rcases le_or_gt x ((9 / 5)) with c2 | c2
  · exact dq_pos_piece hθ0 hθ1 (a := (17 / 10)) (b := (9 / 5)) (by norm_num) (by linarith) c2 (by norm_num)
  rcases le_or_gt x ((19 / 10)) with c3 | c3
  · exact dq_pos_piece hθ0 hθ1 (a := (9 / 5)) (b := (19 / 10)) (by norm_num) (by linarith) c3 (by norm_num)
  rcases le_or_gt x ((2)) with c4 | c4
  · exact dq_pos_piece hθ0 hθ1 (a := (19 / 10)) (b := (2)) (by norm_num) (by linarith) c4 (by norm_num)
  exact dq_pos_piece hθ0 hθ1 (a := (2)) (b := (21 / 10)) (by norm_num) (by linarith) h2 (by norm_num)

lemma q_pos_M {θ x : ℝ} (hθ0 : (1187001329 / 10000000000) ≤ θ) (hθ1 : θ ≤ (593500771 / 5000000000)) (h1 : (21 / 10) ≤ x) (h2 : x ≤ (11)) :
    0 < q θ x := by
  rcases le_or_gt x ((89 / 40)) with c1 | c1
  · exact q_pos_piece hθ0 hθ1 (a := (21 / 10)) (b := (89 / 40)) (by norm_num) (by linarith) c1 (by norm_num)
  rcases le_or_gt x ((47 / 20)) with c2 | c2
  · exact q_pos_piece hθ0 hθ1 (a := (89 / 40)) (b := (47 / 20)) (by norm_num) (by linarith) c2 (by norm_num)
  rcases le_or_gt x ((99 / 40)) with c3 | c3
  · exact q_pos_piece hθ0 hθ1 (a := (47 / 20)) (b := (99 / 40)) (by norm_num) (by linarith) c3 (by norm_num)
  rcases le_or_gt x ((109 / 40)) with c4 | c4
  · exact q_pos_piece hθ0 hθ1 (a := (99 / 40)) (b := (109 / 40)) (by norm_num) (by linarith) c4 (by norm_num)
  rcases le_or_gt x ((119 / 40)) with c5 | c5
  · exact q_pos_piece hθ0 hθ1 (a := (109 / 40)) (b := (119 / 40)) (by norm_num) (by linarith) c5 (by norm_num)
  rcases le_or_gt x ((129 / 40)) with c6 | c6
  · exact q_pos_piece hθ0 hθ1 (a := (119 / 40)) (b := (129 / 40)) (by norm_num) (by linarith) c6 (by norm_num)
  rcases le_or_gt x ((149 / 40)) with c7 | c7
  · exact q_pos_piece hθ0 hθ1 (a := (129 / 40)) (b := (149 / 40)) (by norm_num) (by linarith) c7 (by norm_num)
  rcases le_or_gt x ((169 / 40)) with c8 | c8
  · exact q_pos_piece hθ0 hθ1 (a := (149 / 40)) (b := (169 / 40)) (by norm_num) (by linarith) c8 (by norm_num)
  rcases le_or_gt x ((189 / 40)) with c9 | c9
  · exact q_pos_piece hθ0 hθ1 (a := (169 / 40)) (b := (189 / 40)) (by norm_num) (by linarith) c9 (by norm_num)
  rcases le_or_gt x ((209 / 40)) with c10 | c10
  · exact q_pos_piece hθ0 hθ1 (a := (189 / 40)) (b := (209 / 40)) (by norm_num) (by linarith) c10 (by norm_num)
  rcases le_or_gt x ((229 / 40)) with c11 | c11
  · exact q_pos_piece hθ0 hθ1 (a := (209 / 40)) (b := (229 / 40)) (by norm_num) (by linarith) c11 (by norm_num)
  rcases le_or_gt x ((249 / 40)) with c12 | c12
  · exact q_pos_piece hθ0 hθ1 (a := (229 / 40)) (b := (249 / 40)) (by norm_num) (by linarith) c12 (by norm_num)
  rcases le_or_gt x ((269 / 40)) with c13 | c13
  · exact q_pos_piece hθ0 hθ1 (a := (249 / 40)) (b := (269 / 40)) (by norm_num) (by linarith) c13 (by norm_num)
  rcases le_or_gt x ((289 / 40)) with c14 | c14
  · exact q_pos_piece hθ0 hθ1 (a := (269 / 40)) (b := (289 / 40)) (by norm_num) (by linarith) c14 (by norm_num)
  rcases le_or_gt x ((309 / 40)) with c15 | c15
  · exact q_pos_piece hθ0 hθ1 (a := (289 / 40)) (b := (309 / 40)) (by norm_num) (by linarith) c15 (by norm_num)
  rcases le_or_gt x ((329 / 40)) with c16 | c16
  · exact q_pos_piece hθ0 hθ1 (a := (309 / 40)) (b := (329 / 40)) (by norm_num) (by linarith) c16 (by norm_num)
  rcases le_or_gt x ((349 / 40)) with c17 | c17
  · exact q_pos_piece hθ0 hθ1 (a := (329 / 40)) (b := (349 / 40)) (by norm_num) (by linarith) c17 (by norm_num)
  rcases le_or_gt x ((369 / 40)) with c18 | c18
  · exact q_pos_piece hθ0 hθ1 (a := (349 / 40)) (b := (369 / 40)) (by norm_num) (by linarith) c18 (by norm_num)
  rcases le_or_gt x ((389 / 40)) with c19 | c19
  · exact q_pos_piece hθ0 hθ1 (a := (369 / 40)) (b := (389 / 40)) (by norm_num) (by linarith) c19 (by norm_num)
  rcases le_or_gt x ((399 / 40)) with c20 | c20
  · exact q_pos_piece hθ0 hθ1 (a := (389 / 40)) (b := (399 / 40)) (by norm_num) (by linarith) c20 (by norm_num)
  rcases le_or_gt x ((409 / 40)) with c21 | c21
  · exact q_pos_piece hθ0 hθ1 (a := (399 / 40)) (b := (409 / 40)) (by norm_num) (by linarith) c21 (by norm_num)
  rcases le_or_gt x ((419 / 40)) with c22 | c22
  · exact q_pos_piece hθ0 hθ1 (a := (409 / 40)) (b := (419 / 40)) (by norm_num) (by linarith) c22 (by norm_num)
  rcases le_or_gt x ((429 / 40)) with c23 | c23
  · exact q_pos_piece hθ0 hθ1 (a := (419 / 40)) (b := (429 / 40)) (by norm_num) (by linarith) c23 (by norm_num)
  exact q_pos_piece hθ0 hθ1 (a := (429 / 40)) (b := (11)) (by norm_num) (by linarith) h2 (by norm_num)

lemma dq_neg_W2 {θ x : ℝ} (hθ0 : (1187001329 / 10000000000) ≤ θ) (hθ1 : θ ≤ (593500771 / 5000000000)) (h1 : (11) ≤ x) (h2 : x ≤ (15)) :
    dq θ x < 0 := by
  rcases le_or_gt x ((45 / 4)) with c1 | c1
  · exact dq_neg_piece hθ0 hθ1 (a := (11)) (b := (45 / 4)) (by norm_num) (by linarith) c1 (by norm_num)
  rcases le_or_gt x ((47 / 4)) with c2 | c2
  · exact dq_neg_piece hθ0 hθ1 (a := (45 / 4)) (b := (47 / 4)) (by norm_num) (by linarith) c2 (by norm_num)
  rcases le_or_gt x ((49 / 4)) with c3 | c3
  · exact dq_neg_piece hθ0 hθ1 (a := (47 / 4)) (b := (49 / 4)) (by norm_num) (by linarith) c3 (by norm_num)
  rcases le_or_gt x ((53 / 4)) with c4 | c4
  · exact dq_neg_piece hθ0 hθ1 (a := (49 / 4)) (b := (53 / 4)) (by norm_num) (by linarith) c4 (by norm_num)
  rcases le_or_gt x ((57 / 4)) with c5 | c5
  · exact dq_neg_piece hθ0 hθ1 (a := (53 / 4)) (b := (57 / 4)) (by norm_num) (by linarith) c5 (by norm_num)
  exact dq_neg_piece hθ0 hθ1 (a := (57 / 4)) (b := (15)) (by norm_num) (by linarith) h2 (by norm_num)

lemma q_neg_R {θ x : ℝ} (hθ0 : (1187001329 / 10000000000) ≤ θ) (hθ1 : θ ≤ (593500771 / 5000000000)) (h1 : (15) ≤ x) (h2 : x ≤ (18)) :
    q θ x < 0 := by
  rcases le_or_gt x ((31 / 2)) with c1 | c1
  · exact q_neg_piece hθ0 hθ1 (a := (15)) (b := (31 / 2)) (by norm_num) (by linarith) c1 (by norm_num)
  rcases le_or_gt x ((16)) with c2 | c2
  · exact q_neg_piece hθ0 hθ1 (a := (31 / 2)) (b := (16)) (by norm_num) (by linarith) c2 (by norm_num)
  rcases le_or_gt x ((33 / 2)) with c3 | c3
  · exact q_neg_piece hθ0 hθ1 (a := (16)) (b := (33 / 2)) (by norm_num) (by linarith) c3 (by norm_num)
  rcases le_or_gt x ((35 / 2)) with c4 | c4
  · exact q_neg_piece hθ0 hθ1 (a := (33 / 2)) (b := (35 / 2)) (by norm_num) (by linarith) c4 (by norm_num)
  exact q_neg_piece hθ0 hθ1 (a := (35 / 2)) (b := (18)) (by norm_num) (by linarith) h2 (by norm_num)

/-! ## Structure of the roots of `q` -/

section
variable {θ : ℝ} (hθ0 : 1187001329 / 10000000000 ≤ θ) (hθ1 : θ ≤ 593500771 / 5000000000)
include hθ0 hθ1

lemma q_neg_far {x : ℝ} (h : 18 ≤ x) : q θ x < 0 := by
  have hx : 0 < x := by linarith
  have e1 : (2 * x + 1) * (x - 1) ^ 2 < (2 * x + 1) * x ^ 2 := by
    apply mul_lt_mul_of_pos_left _ (by linarith); nlinarith
  have e2 : (2 * x + 1) * x ^ 2 ≤ θ * x ^ 2 * x ^ 2 := by
    have : 2 * x + 1 ≤ θ * x ^ 2 := by nlinarith
    nlinarith [sq_nonneg x]
  have e3 : θ * x ^ 2 * x ^ 2 ≤ θ * (x ^ 2 + x) ^ 2 := by
    have : 0 ≤ θ := by linarith
    have : x ^ 2 * x ^ 2 ≤ (x ^ 2 + x) ^ 2 := by nlinarith
    nlinarith
  unfold q; linarith

lemma q_neg_right {x : ℝ} (h : 15 ≤ x) : q θ x < 0 := by
  rcases le_or_gt x 18 with c | c
  · exact q_neg_R hθ0 hθ1 h c
  · exact q_neg_far hθ0 hθ1 c.le

lemma q_strictMono_W1 : StrictMonoOn (q θ) (Icc (8 / 5) (21 / 10)) :=
  strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
    (fun x _ => (hasDerivAt_q θ x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_q θ x).hasDerivWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      exact dq_pos_W1 hθ0 hθ1 hx.1.le hx.2.le)

lemma q_strictAnti_W2 : StrictAntiOn (q θ) (Icc 11 15) :=
  strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
    (fun x _ => (hasDerivAt_q θ x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_q θ x).hasDerivWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      exact dq_neg_W2 hθ0 hθ1 hx.1.le hx.2.le)

lemma root_loc {η : ℝ} (h : 1 < η) (hq : q θ η = 0) :
    (8 / 5 ≤ η ∧ η ≤ 21 / 10) ∨ (11 ≤ η ∧ η ≤ 15) := by
  by_cases a : η ≤ 8 / 5
  · linarith [q_neg_L hθ0 hθ1 h a]
  by_cases b : η ≤ 21 / 10
  · left; constructor <;> linarith
  by_cases c : η ≤ 11
  · linarith [q_pos_M hθ0 hθ1 (by linarith : 21 / 10 ≤ η) c]
  by_cases d : η ≤ 15
  · right; constructor <;> linarith
  · linarith [q_neg_right hθ0 hθ1 (by linarith : 15 ≤ η)]

lemma roots_loc {η₁ η₂ : ℝ} (h1 : 1 < η₁) (h12 : η₁ < η₂) (hq1 : q θ η₁ = 0) (hq2 : q θ η₂ = 0) :
    (8 / 5 ≤ η₁ ∧ η₁ ≤ 21 / 10) ∧ (11 ≤ η₂ ∧ η₂ ≤ 15) := by
  rcases root_loc hθ0 hθ1 h1 hq1 with a | a <;>
    rcases root_loc hθ0 hθ1 (by linarith) hq2 with b | b
  · have := q_strictMono_W1 hθ0 hθ1 ⟨a.1, a.2⟩ ⟨b.1, b.2⟩ h12
    linarith
  · exact ⟨a, b⟩
  · linarith [a.1, b.2]
  · have := q_strictAnti_W2 hθ0 hθ1 ⟨a.1, a.2⟩ ⟨b.1, b.2⟩ h12
    linarith

lemma q_nonpos_left {η₁ x : ℝ} (hη : 8 / 5 ≤ η₁) (hη' : η₁ ≤ 21 / 10) (hq : q θ η₁ = 0)
    (h1 : 1 < x) (hx : x ≤ η₁) : q θ x ≤ 0 := by
  by_cases a : x ≤ 8 / 5
  · exact (q_neg_L hθ0 hθ1 h1 a).le
  · rw [← hq]
    exact (q_strictMono_W1 hθ0 hθ1).monotoneOn ⟨by linarith, by linarith⟩ ⟨hη, hη'⟩ hx

lemma q_nonpos_right {η₂ x : ℝ} (hη : 11 ≤ η₂) (hη' : η₂ ≤ 15) (hq : q θ η₂ = 0)
    (hx : η₂ ≤ x) : q θ x ≤ 0 := by
  by_cases a : 15 ≤ x
  · exact (q_neg_right hθ0 hθ1 a).le
  · rw [← hq]
    exact (q_strictAnti_W2 hθ0 hθ1).antitoneOn ⟨hη, hη'⟩ ⟨by linarith, by linarith⟩ hx

end

/-! ## Monotonicity of `g` and `ψ` -/

lemma ψ_mono {θ p s t : ℝ} (hs : 1 < s) (h : ∀ x ∈ Icc s t, p ≤ g θ x) :
    MonotoneOn (ψ θ p) (Icc s t) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s t) (continuousOn_ψ θ p hs)
    (fun x hx => (hasDerivAt_ψ θ p (by linarith [(interior_subset hx : x ∈ Icc s t).1])).hasDerivWithinAt)
    (fun x hx => by linarith [h x (interior_subset hx)])

lemma ψ_anti {θ p s t : ℝ} (hs : 1 < s) (h : ∀ x ∈ Icc s t, g θ x ≤ p) :
    AntitoneOn (ψ θ p) (Icc s t) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t) (continuousOn_ψ θ p hs)
    (fun x hx => (hasDerivAt_ψ θ p (by linarith [(interior_subset hx : x ∈ Icc s t).1])).hasDerivWithinAt)
    (fun x hx => by linarith [h x (interior_subset hx)])

lemma g_anti {θ s t : ℝ} (hs : 1 < s) (h : ∀ x ∈ Icc s t, q θ x ≤ 0) : AntitoneOn (g θ) (Icc s t) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t) (continuousOn_g θ hs)
    (fun x hx => (hasDerivAt_g θ (by linarith [(interior_subset hx : x ∈ Icc s t).1])).hasDerivWithinAt)
    (fun x hx => by
      have hx' : x ∈ Icc s t := interior_subset hx
      have h1 : 1 < x := by linarith [hx'.1]
      apply div_nonpos_of_nonpos_of_nonneg (h x hx')
      positivity)

lemma critical_points {θ x₁ x₂ p : ℝ} (h1 : 1 < x₁) (h12 : x₁ < x₂) (hg1 : g θ x₁ = p)
    (hg2 : g θ x₂ = p) (hψ : ψ θ p x₁ = ψ θ p x₂) :
    ∃ η₁ η₂, x₁ < η₁ ∧ η₁ < η₂ ∧ η₂ < x₂ ∧ q θ η₁ = 0 ∧ q θ η₂ = 0 := by
  obtain ⟨ξ, hξ, hξ0⟩ := exists_hasDerivAt_eq_zero h12 (continuousOn_ψ θ p h1) hψ
    (fun x hx => hasDerivAt_ψ θ p (by linarith [hx.1]))
  have hgξ : g θ ξ = p := by linarith
  have qz : ∀ η, 1 < η → q θ η / ((η - 1) ^ 2 * (η ^ 2 + η) ^ 2) = 0 → q θ η = 0 := by
    intro η h hz
    rcases div_eq_zero_iff.1 hz with h' | h'
    · exact h'
    · exfalso
      have : 0 < (η - 1) ^ 2 * (η ^ 2 + η) ^ 2 := by
        have : 0 < η - 1 := by linarith
        positivity
      linarith
  obtain ⟨η₁, hη₁, hz₁⟩ := exists_hasDerivAt_eq_zero hξ.1 (continuousOn_g θ h1) (by rw [hg1, hgξ])
    (fun x hx => hasDerivAt_g θ (by linarith [hx.1]))
  obtain ⟨η₂, hη₂, hz₂⟩ := exists_hasDerivAt_eq_zero hξ.2 (continuousOn_g θ (by linarith [hξ.1]))
    (by rw [hg2, hgξ]) (fun x hx => hasDerivAt_g θ (by linarith [hx.1, hξ.1]))
  exact ⟨η₁, η₂, hη₁.1, by linarith [hη₁.2, hη₂.1], hη₂.2,
    qz η₁ (by linarith [hη₁.1]) hz₁, qz η₂ (by linarith [hη₂.1, hξ.1]) hz₂⟩

lemma g_mono_θ {θ θ' x : ℝ} (h : θ ≤ θ') (hx : 1 < x) : g θ x ≤ g θ' x := by
  unfold g
  have : θ / (x - 1) ≤ θ' / (x - 1) := div_le_div_of_nonneg_right h (by linarith)
  linarith

lemma ψ_shift (θ p p' x : ℝ) : ψ θ p x = ψ θ p' x + (p' - p) * x := by unfold ψ; ring

/-! ## Brackets and the two area certificates -/

section
variable {θ : ℝ} (hθ0 : 1187001329 / 10000000000 ≤ θ) (hθ1 : θ ≤ 593500771 / 5000000000)
include hθ0 hθ1

lemma num_lo : 2569 / 2000000 < g θ (3486983 / 2500000) ∧ g θ (6973967 / 5000000) < 2569 / 2000000 ∧
    2569 / 2000000 < g θ (844017 / 10000) := by
  have a1 := g_mono_θ hθ0 (x := 3486983 / 2500000) (by norm_num)
  have a2 := g_mono_θ hθ1 (x := 6973967 / 5000000) (by norm_num)
  have a3 := g_mono_θ hθ0 (x := 844017 / 10000) (by norm_num)
  have b1 : (2569 / 2000000 : ℝ) < g (1187001329 / 10000000000) (3486983 / 2500000) := by norm_num [g]
  have b2 : g (593500771 / 5000000000) (6973967 / 5000000) < (2569 / 2000000 : ℝ) := by norm_num [g]
  have b3 : (2569 / 2000000 : ℝ) < g (1187001329 / 10000000000) (844017 / 10000) := by norm_num [g]
  exact ⟨by linarith, by linarith, by linarith⟩

lemma num_hi : g θ (3486981 / 2500000) < 12849 / 10000000 ∧ 12849 / 10000000 < g θ (843727 / 10000) ∧
    g θ (52733 / 625) < 12849 / 10000000 := by
  have a1 := g_mono_θ hθ1 (x := 3486981 / 2500000) (by norm_num)
  have a2 := g_mono_θ hθ0 (x := 843727 / 10000) (by norm_num)
  have a3 := g_mono_θ hθ1 (x := 52733 / 625) (by norm_num)
  have b1 : g (593500771 / 5000000000) (3486981 / 2500000) < (12849 / 10000000 : ℝ) := by norm_num [g]
  have b2 : (12849 / 10000000 : ℝ) < g (1187001329 / 10000000000) (843727 / 10000) := by norm_num [g]
  have b3 : g (593500771 / 5000000000) (52733 / 625) < (12849 / 10000000 : ℝ) := by norm_num [g]
  exact ⟨by linarith, by linarith, by linarith⟩

lemma K_lo : 0 < ψ θ (2569 / 2000000) (844017 / 10000) - ψ θ (2569 / 2000000) (6973967 / 5000000)
    - (6973967 / 5000000 - 3486983 / 2500000) * (2569 / 2000000 - g θ (6973967 / 5000000)) := by
  have hA := logA_lo
  have hB := logB_lo
  rw [Real.log_div (by norm_num) (by norm_num)] at hA
  rw [Real.log_div (x := (844017 / 10000 + 1) / (844017 / 10000))
      (y := (6973967 / 5000000 + 1) / (6973967 / 5000000)) (by norm_num) (by norm_num),
    Real.log_div (x := 844017 / 10000 + 1) (y := 844017 / 10000) (by norm_num) (by norm_num),
    Real.log_div (x := 6973967 / 5000000 + 1) (y := 6973967 / 5000000) (by norm_num) (by norm_num)] at hB
  set L1 := Real.log ((844017 / 10000 : ℝ) - 1) - Real.log ((6973967 / 5000000 : ℝ) - 1) with hL1
  set L2 := (Real.log ((844017 / 10000 : ℝ) + 1) - Real.log (844017 / 10000)) -
    (Real.log ((6973967 / 5000000 : ℝ) + 1) - Real.log (6973967 / 5000000)) with hL2
  have e : ψ θ (2569 / 2000000) (844017 / 10000) - ψ θ (2569 / 2000000) (6973967 / 5000000)
      - (6973967 / 5000000 - 3486983 / 2500000) * (2569 / 2000000 - g θ (6973967 / 5000000))
      = θ * (L1 + (6973967 / 5000000 - 3486983 / 2500000) / (6973967 / 5000000 - 1)) + L2
        - 2569 / 2000000 * (844017 / 10000 - 6973967 / 5000000)
        - (6973967 / 5000000 - 3486983 / 2500000) * (2569 / 2000000
          + 1 / ((6973967 / 5000000) ^ 2 + 6973967 / 5000000)) := by
    rw [hL1, hL2]; unfold ψ g; ring
  rw [e]
  have hm : 1187001329 / 10000000000 * (1338265344913 / 250000000000
      + (6973967 / 5000000 - 3486983 / 2500000) / (6973967 / 5000000 - 1))
      ≤ θ * (L1 + (6973967 / 5000000 - 3486983 / 2500000) / (6973967 / 5000000 - 1)) :=
    mul_le_mul hθ0 (by linarith) (by norm_num) (by linarith)
  have hn : (0:ℝ) < 1187001329 / 10000000000 * (1338265344913 / 250000000000
      + (6973967 / 5000000 - 3486983 / 2500000) / (6973967 / 5000000 - 1)) + (-26438609853 / 50000000000)
        - 2569 / 2000000 * (844017 / 10000 - 6973967 / 5000000)
        - (6973967 / 5000000 - 3486983 / 2500000) * (2569 / 2000000
          + 1 / ((6973967 / 5000000) ^ 2 + 6973967 / 5000000)) := by norm_num
  linarith

lemma K_hi : ψ θ (12849 / 10000000) (52733 / 625) - ψ θ (12849 / 10000000) (3486981 / 2500000)
    + (52733 / 625 - 843727 / 10000) * (12849 / 10000000 - g θ (52733 / 625)) < 0 := by
  have hC := logC_hi
  have hD := logD_hi
  have hC0 : 1 - ((52733 / 625 - 1) / (3486981 / 2500000 - 1) : ℝ)⁻¹
      ≤ Real.log ((52733 / 625 - 1) / (3486981 / 2500000 - 1)) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num)] at hC hC0
  rw [Real.log_div (x := (52733 / 625 + 1) / (52733 / 625))
      (y := (3486981 / 2500000 + 1) / (3486981 / 2500000)) (by norm_num) (by norm_num),
    Real.log_div (x := 52733 / 625 + 1) (y := 52733 / 625) (by norm_num) (by norm_num),
    Real.log_div (x := 3486981 / 2500000 + 1) (y := 3486981 / 2500000) (by norm_num) (by norm_num)] at hD
  set L1 := Real.log ((52733 / 625 : ℝ) - 1) - Real.log ((3486981 / 2500000 : ℝ) - 1) with hL1
  set L2 := (Real.log ((52733 / 625 : ℝ) + 1) - Real.log (52733 / 625)) -
    (Real.log ((3486981 / 2500000 : ℝ) + 1) - Real.log (3486981 / 2500000)) with hL2
  have e : ψ θ (12849 / 10000000) (52733 / 625) - ψ θ (12849 / 10000000) (3486981 / 2500000)
      + (52733 / 625 - 843727 / 10000) * (12849 / 10000000 - g θ (52733 / 625))
      = θ * (L1 - (52733 / 625 - 843727 / 10000) / (52733 / 625 - 1)) + L2
        - 12849 / 10000000 * (52733 / 625 - 3486981 / 2500000)
        + (52733 / 625 - 843727 / 10000) * (12849 / 10000000
          + 1 / ((52733 / 625) ^ 2 + 52733 / 625)) := by
    rw [hL1, hL2]; unfold ψ g; ring
  rw [e]
  norm_num at hC0
  have hm : θ * (L1 - (52733 / 625 - 843727 / 10000) / (52733 / 625 - 1))
      ≤ 593500771 / 5000000000 * (42821738727 / 8000000000
        - (52733 / 625 - 843727 / 10000) / (52733 / 625 - 1)) :=
    mul_le_mul hθ1 (by linarith) (by norm_num; linarith) (by norm_num)
  have hn : 593500771 / 5000000000 * (42821738727 / 8000000000
        - (52733 / 625 - 843727 / 10000) / (52733 / 625 - 1)) + (-528768485147 / 1000000000000)
        - 12849 / 10000000 * (52733 / 625 - 3486981 / 2500000)
        + (52733 / 625 - 843727 / 10000) * (12849 / 10000000
          + 1 / ((52733 / 625) ^ 2 + 52733 / 625)) < (0:ℝ) := by norm_num
  linarith

end

theorem reduced_window {θ x₁ x₂ p : ℝ} (hθ0 : 1187001329 / 10000000000 ≤ θ)
    (hθ1 : θ ≤ 593500771 / 5000000000) (h1 : 1 < x₁) (h12 : x₁ < x₂) (hg1 : g θ x₁ = p)
    (hg2 : g θ x₂ = p) (hψ : ψ θ p x₁ = ψ θ p x₂) : 2569 / 2000000 ≤ p ∧ p ≤ 12849 / 10000000 := by
  obtain ⟨η₁, η₂, hx1, h12', hx2, hq1, hq2⟩ := critical_points h1 h12 hg1 hg2 hψ
  obtain ⟨⟨l1, l2⟩, l3, l4⟩ := roots_loc hθ0 hθ1 (by linarith) h12' hq1 hq2
  have antiL : ∀ s t, 1 < s → t ≤ η₁ → AntitoneOn (g θ) (Icc s t) := fun s t hs ht =>
    g_anti hs (fun x hx => q_nonpos_left hθ0 hθ1 l1 l2 hq1 (by linarith [hx.1]) (by linarith [hx.2]))
  have antiR : ∀ s t, η₂ ≤ s → AntitoneOn (g θ) (Icc s t) := fun s t hs =>
    g_anti (by linarith) (fun x hx => q_nonpos_right hθ0 hθ1 l3 l4 hq2 (by linarith [hx.1]))
  constructor
  · by_contra hlt
    push Not at hlt
    obtain ⟨ga1, gb1, ga3⟩ := num_lo hθ0 hθ1
    have hxa1 : (3486983 / 2500000 : ℝ) ≤ x₁ := by
      by_contra h
      push Not at h
      have := antiL x₁ (3486983 / 2500000) h1 (by linarith) ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
      linarith
    have hxa3 : (844017 / 10000 : ℝ) ≤ x₂ := by
      by_contra h
      push Not at h
      have := antiR x₂ (844017 / 10000) hx2.le ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
      linarith
    have hA3 : ψ θ p (844017 / 10000) ≤ ψ θ p x₂ :=
      ψ_mono (by norm_num) (fun y hy => by
        have := antiR (844017 / 10000) x₂ (by linarith) hy ⟨hxa3, le_rfl⟩ hy.2
        linarith) ⟨le_rfl, hxa3⟩ ⟨hxa3, le_rfl⟩ hxa3
    have hB : ψ θ (2569 / 2000000) x₁ ≤ ψ θ (2569 / 2000000) (6973967 / 5000000)
        + (6973967 / 5000000 - 3486983 / 2500000) * (2569 / 2000000 - g θ (6973967 / 5000000)) := by
      rcases le_or_gt x₁ (6973967 / 5000000) with h | h
      · have m := ψ_mono (θ := θ) (p := g θ (6973967 / 5000000)) h1 (fun y hy =>
          antiL x₁ (6973967 / 5000000) h1 (by linarith) hy ⟨h, le_rfl⟩ hy.2) ⟨le_rfl, h⟩ ⟨h, le_rfl⟩ h
        have e1 := ψ_shift θ (2569 / 2000000) (g θ (6973967 / 5000000)) x₁
        have e2 := ψ_shift θ (2569 / 2000000) (g θ (6973967 / 5000000)) (6973967 / 5000000)
        have := mul_le_mul_of_nonneg_left (by linarith : (6973967 / 5000000 : ℝ) - x₁ ≤ 6973967 / 5000000 - 3486983 / 2500000)
          (by linarith : (0:ℝ) ≤ 2569 / 2000000 - g θ (6973967 / 5000000))
        nlinarith
      · have m := ψ_anti (θ := θ) (p := 2569 / 2000000) (by norm_num) (fun y hy => by
          have := antiL (6973967 / 5000000) x₁ (by norm_num) hx1.le ⟨le_rfl, h.le⟩ hy hy.1
          linarith) ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
        have : 0 ≤ (6973967 / 5000000 - 3486983 / 2500000 : ℝ) * (2569 / 2000000 - g θ (6973967 / 5000000)) :=
          mul_nonneg (by norm_num) (by linarith)
        linarith
    have e1 := ψ_shift θ p (2569 / 2000000) x₁
    have e2 := ψ_shift θ p (2569 / 2000000) (844017 / 10000)
    have hpos := mul_pos (sub_pos.2 hlt) (by linarith : (0:ℝ) < 844017 / 10000 - x₁)
    have := K_lo hθ0 hθ1
    nlinarith
  · by_contra hgt
    push Not at hgt
    obtain ⟨gb1, ga3, gb3⟩ := num_hi hθ0 hθ1
    have hxb1 : x₁ ≤ 3486981 / 2500000 := by
      by_contra h
      push Not at h
      have := antiL (3486981 / 2500000) x₁ (by norm_num) hx1.le ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
      linarith
    have hxb3 : x₂ ≤ 52733 / 625 := by
      by_contra h
      push Not at h
      have := antiR (52733 / 625) x₂ (by linarith) ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
      linarith
    have hL : ψ θ p (3486981 / 2500000) ≤ ψ θ p x₁ :=
      ψ_anti h1 (fun y hy => by
        have := antiL x₁ (3486981 / 2500000) h1 (by linarith) ⟨le_rfl, hxb1⟩ hy hy.1
        linarith) ⟨le_rfl, hxb1⟩ ⟨hxb1, le_rfl⟩ hxb1
    have hR : ψ θ (12849 / 10000000) x₂ ≤ ψ θ (12849 / 10000000) (52733 / 625)
        + (52733 / 625 - 843727 / 10000) * (12849 / 10000000 - g θ (52733 / 625)) := by
      have core : ∀ z, 843727 / 10000 ≤ z → z ≤ 52733 / 625 → η₂ ≤ z →
          ψ θ (12849 / 10000000) z ≤ ψ θ (12849 / 10000000) (52733 / 625)
            + (52733 / 625 - 843727 / 10000) * (12849 / 10000000 - g θ (52733 / 625)) := by
        intro z hz1 hz2 hz3
        have m := ψ_mono (θ := θ) (p := g θ (52733 / 625)) (by linarith) (fun y hy =>
          antiR z (52733 / 625) hz3 hy ⟨hz2, le_rfl⟩ hy.2) ⟨le_rfl, hz2⟩ ⟨hz2, le_rfl⟩ hz2
        have e1 := ψ_shift θ (12849 / 10000000) (g θ (52733 / 625)) z
        have e2 := ψ_shift θ (12849 / 10000000) (g θ (52733 / 625)) (52733 / 625)
        have := mul_le_mul_of_nonneg_left (by linarith : (52733 / 625 : ℝ) - z ≤ 52733 / 625 - 843727 / 10000)
          (by linarith : (0:ℝ) ≤ 12849 / 10000000 - g θ (52733 / 625))
        nlinarith
      rcases le_or_gt (843727 / 10000) x₂ with h | h
      · exact core x₂ h hxb3 hx2.le
      · have m := ψ_mono (θ := θ) (p := 12849 / 10000000) (by linarith) (fun y hy => by
          have := antiR x₂ (843727 / 10000) hx2.le hy ⟨h.le, le_rfl⟩ hy.2
          linarith) ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
        linarith [core (843727 / 10000) le_rfl (by norm_num) (by linarith)]
    have e1 := ψ_shift θ p (12849 / 10000000) x₂
    have e2 := ψ_shift θ p (12849 / 10000000) (3486981 / 2500000)
    have hpos := mul_pos (sub_pos.2 hgt) (by linarith : (0:ℝ) < x₂ - 3486981 / 2500000)
    have := K_hi hθ0 hθ1
    nlinarith


/-! ## Back to molar volumes: the Redlich–Kwong isotherm `cubicP R a b 1 0 T` -/

open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence

lemma cubicP_eq_g (R a b T : ℝ) (ha : 0 < a) (hb : 0 < b) {v : ℝ} (hv : b < v) :
    cubicP R a b 1 0 T v = a / b ^ 2 * g (R * T * b / a) (v / b) := by
  have hb0 : b ≠ 0 := hb.ne'
  have h1 : v - b ≠ 0 := by linarith
  have hv0 : 0 < v := by linarith
  have h3 : v / b - 1 ≠ 0 := by
    rw [div_sub_one hb0]; exact div_ne_zero h1 hb0
  have h4 : v ^ 2 + 1 * b * v + 0 * b ^ 2 ≠ 0 := by positivity
  have h5 : (v / b) ^ 2 + v / b ≠ 0 := by positivity
  unfold cubicP g
  rw [div_sub_one hb0]
  field_simp
  ring

lemma integral_cubicP (R a b T : ℝ) (ha : 0 < a) (hb : 0 < b) {vl vg : ℝ}
    (hl : b < vl) (hlg : vl < vg) :
    ∫ v in vl..vg, cubicP R a b 1 0 T v
      = a / b ^ 2 * (b * (ψ (R * T * b / a) 0 (vg / b) - ψ (R * T * b / a) 0 (vl / b))) := by
  have hb0 : b ≠ 0 := hb.ne'
  have h1 : 1 < vl / b := by rw [lt_div_iff₀ hb]; linarith
  have h12 : vl / b < vg / b := div_lt_div_of_pos_right hlg hb
  rw [intervalIntegral.integral_congr (g := fun v => a / b ^ 2 * g (R * T * b / a) (v / b))
    (fun v hv => by
      rw [Set.uIcc_of_le hlg.le] at hv
      exact cubicP_eq_g R a b T ha hb (by linarith [hv.1]))]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun x => g (R * T * b / a) x) hb0]
  congr 1
  rw [smul_eq_mul]
  congr 1
  have hd : ∀ x ∈ Set.uIcc (vl / b) (vg / b),
      HasDerivAt (ψ (R * T * b / a) 0) (g (R * T * b / a) x - 0) x := by
    intro x hx
    rw [Set.uIcc_of_le h12.le] at hx
    exact hasDerivAt_ψ _ 0 (by linarith [hx.1])
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuousOn_g (R * T * b / a) (t := vg / b) h1).sub continuousOn_const
      |>.intervalIntegrable_of_Icc h12.le)
  simpa using this

/-- Every Maxwell coexistence state of the RK isotherm (liquid volume above `b`) whose reduced
temperature `θ = RTb/a` lies in the certified interval has reduced pressure `p b²/a` in
`[0.0012845, 0.0012849]`. -/
theorem window_of_maxwell (R a b T vl vg ps : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hθ0 : 1187001329 / 10000000000 ≤ R * T * b / a) (hθ1 : R * T * b / a ≤ 593500771 / 5000000000)
    (hl : b < vl) (h : IsMaxwellCoexistence (cubicP R a b 1 0 T) vl vg ps) :
    2569 / 2000000 ≤ ps / (a / b ^ 2) ∧ ps / (a / b ^ 2) ≤ 12849 / 10000000 := by
  obtain ⟨hlg, hpl, hpg, hint⟩ := h
  have hb0 : b ≠ 0 := hb.ne'
  have hK : 0 < a / b ^ 2 := by positivity
  set θ := R * T * b / a with hθ
  have h1 : 1 < vl / b := by rw [lt_div_iff₀ hb]; linarith
  have h12 : vl / b < vg / b := div_lt_div_of_pos_right hlg hb
  have hgl : g θ (vl / b) = ps / (a / b ^ 2) := by
    rw [← hpl, cubicP_eq_g R a b T ha hb hl, mul_div_cancel_left₀ _ hK.ne']
  have hgg : g θ (vg / b) = ps / (a / b ^ 2) := by
    rw [← hpg, cubicP_eq_g R a b T ha hb (by linarith), mul_div_cancel_left₀ _ hK.ne']
  have hψ : ψ θ (ps / (a / b ^ 2)) (vl / b) = ψ θ (ps / (a / b ^ 2)) (vg / b) := by
    rw [integral_cubicP R a b T ha hb hl hlg] at hint
    have e1 := ψ_shift θ (ps / (a / b ^ 2)) 0 (vl / b)
    have e2 := ψ_shift θ (ps / (a / b ^ 2)) 0 (vg / b)
    have key : ψ θ 0 (vg / b) - ψ θ 0 (vl / b) = ps / (a / b ^ 2) * (vg / b - vl / b) := by
      have hne : a / b ^ 2 * b ≠ 0 := by positivity
      apply mul_left_cancel₀ hne
      rw [show a / b ^ 2 * b * (ψ θ 0 (vg / b) - ψ θ 0 (vl / b))
          = a / b ^ 2 * (b * (ψ θ 0 (vg / b) - ψ θ 0 (vl / b))) by ring, hint]
      field_simp
    linarith
  exact reduced_window hθ0 hθ1 h1 h12 hgl hgg hψ

/-! ## From the pressure ratio to the acentric factor -/

lemma logR_lo : -1218458289 / 500000000 < Real.log ((4371501 / 50000000)) := by
  have e : ((4371501 / 50000000) : ℝ) = (1 - (-2493 / 6250)) / (2:ℝ) ^ 4 * (4371501 / 4371500) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  have h := log_series' (-2493 / 6250) (by norm_num [abs_lt]) 28
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have u1 : Real.log (4371501 / 4371500 : ℝ) ≤ 4371501 / 4371500 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have u2 : 1 - (4371501 / 4371500 : ℝ)⁻¹ ≤ Real.log (4371501 / 4371500) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  push_cast
  norm_num at h u1 u2 ⊢
  linarith [h.1, h.2]

lemma logR_hi : Real.log ((8745729 / 100000000)) < -2436604718023 / 1000000000000 := by
  have e : ((8745729 / 100000000) : ℝ) = (1 - (-9983 / 25000)) / (2:ℝ) ^ 4 * (2915243 / 2915250) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  have h := log_series' (-9983 / 25000) (by norm_num [abs_lt]) 28
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have u1 : Real.log (2915243 / 2915250 : ℝ) ≤ 2915243 / 2915250 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have u2 : 1 - (2915243 / 2915250 : ℝ)⁻¹ ≤ Real.log (2915243 / 2915250) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  push_cast
  norm_num at h u1 u2 ⊢
  linarith [h.1, h.2]

lemma log1000_lo : 55262042211 / 8000000000 < Real.log ((1000 : ℝ)) := by
  have e : ((1000 : ℝ) : ℝ) = (2:ℝ) ^ 10 * (1 - (293 / 12500)) * (390625 / 390624) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have h := log_series' (293 / 12500) (by norm_num [abs_lt]) 6
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have u1 : Real.log (390625 / 390624 : ℝ) ≤ 390625 / 390624 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have u2 : 1 - (390625 / 390624 : ℝ)⁻¹ ≤ Real.log (390625 / 390624) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  push_cast
  norm_num at h u1 u2 ⊢
  linarith [h.1, h.2]

lemma log1000_hi : Real.log ((1000 : ℝ)) < 6907755281391 / 1000000000000 := by
  have e : ((1000 : ℝ) : ℝ) = (2:ℝ) ^ 10 * (1 - (293 / 12500)) * (390625 / 390624) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have h := log_series' (293 / 12500) (by norm_num [abs_lt]) 6
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have u1 : Real.log (390625 / 390624 : ℝ) ≤ 390625 / 390624 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have u2 : 1 - (390625 / 390624 : ℝ)⁻¹ ≤ Real.log (390625 / 390624) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  push_cast
  norm_num at h u1 u2 ⊢
  linarith [h.1, h.2]

lemma ratio_acentric {r : ℝ} (h1 : 4371501 / 50000000 ≤ r) (h2 : r ≤ 8745729 / 100000000) :
    RoundsTo r 0.087 3 ∧ RoundsTo (-Real.logb 10 r - 1) 0.058 3 := by
  have hr : 0 < r := by linarith
  refine ⟨?_, ?_⟩
  · unfold RoundsTo; rw [abs_le]; constructor <;> norm_num <;> linarith
  · have a1 := logR_lo
    have a2 := logR_hi
    have a3 := log1000_lo
    have a4 := log1000_hi
    have m1 : Real.log (4371501 / 50000000) ≤ Real.log r := Real.log_le_log (by norm_num) h1
    have m2 : Real.log r ≤ Real.log (8745729 / 100000000) := Real.log_le_log hr h2
    have e : Real.log (1000 : ℝ) = 3 * Real.log 10 := by
      rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow]; norm_num
    have hL0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
    have A : -10585 / 10000 * Real.log 10 ≤ Real.log r := by linarith
    have B : Real.log r ≤ -10575 / 10000 * Real.log 10 := by linarith
    have A' : -10585 / 10000 ≤ Real.log r / Real.log 10 := (le_div_iff₀ hL0).2 A
    have B' : Real.log r / Real.log 10 ≤ -10575 / 10000 := (div_le_iff₀ hL0).2 B
    unfold RoundsTo Real.logb
    generalize Real.log r / Real.log 10 = t at A' B' ⊢
    rw [abs_le]
    constructor <;> norm_num <;> linarith

/-! ## The main statement, in molar volumes and pressures -/

set_option maxHeartbeats 2000000 in
/-- Core of `Checked.Chemistry.RKAcentric.rk_coexistence_unique` (same statement). -/
theorem rk_unique_core (R A b Tc vc vl vg ps : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b)
    (hTc : 0 < Tc) (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R (A / Real.sqrt Tc) b 1 0 Tc) vc)
    (hl : b < vl)
    (h : IsMaxwellCoexistence
      (cubicP R (A / Real.sqrt (7 / 10 * Tc)) b 1 0 (7 / 10 * Tc)) vl vg ps) :
    RoundsTo (ps / cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc) 0.087 3 ∧
      RoundsTo (acentric ps (cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc)) 0.058 3 := by
  -- Proof (run 2026-11-04T1828Z): reduced variables `x = v/b`, `θ = RTb/a`, `pr = p b²/a`;
  -- `Checked.Chemistry.RKReduced.window_of_maxwell` (certified window of pr for θ in a rational
  -- interval), θ and P_c from the critical point (`reduced`, `root_bounds`), ω from
  -- `ratio_acentric`.
  have hsT : 0 < Real.sqrt Tc := Real.sqrt_pos.2 hTc
  have hac0 : 0 < A / Real.sqrt Tc := div_pos hA hsT
  have hD : 0 < vc ^ 2 + 1 * b * vc + 0 * b ^ 2 := by nlinarith
  obtain ⟨hf, hx1, -, h2, h3⟩ := reduced R (A / Real.sqrt Tc) b 1 0 Tc vc hac0 hb (by norm_num) hvc hD hc
  set ac := A / Real.sqrt Tc with hac
  set Pc := cubicP R ac b 1 0 Tc vc with hPc
  set x := vc / b with hx
  unfold critCubic at hf
  have hx1' : 0 < x - 1 := by linarith
  have hs2 : 0 < 2 * x + 1 := by linarith
  obtain ⟨lo, hi⟩ := root_bounds 1 x (38473221 / 10000000) (384732211 / 100000000) hx1
    (by linear_combination hf) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : ((x - 1) * (2 * x + 1) - (x ^ 2 + 1 * x + 0)) / ((x - 1) ^ 2 * (2 * x + 1))
      = x ^ 2 / 3 - x - 1 := by
    rw [div_eq_iff (by positivity)]; linear_combination (-2 * x ^ 2 / 3 + x) * hf
  have e3 : (x ^ 2 + 1 * x + 0) ^ 2 * ((x - 1) * (2 * x + 1) - (x ^ 2 + 1 * x + 0)) /
      ((x - 1) ^ 4 * (2 * x + 1) ^ 2) = x / 9 := by
    rw [div_eq_iff (by positivity)]
    linear_combination (-4 * x ^ 4 / 9 + x ^ 3 + 2 * x ^ 2 / 3 + x / 9) * hf
  rw [e2] at h2
  rw [e3] at h3
  have hRT : 0 < R * Tc := mul_pos hR hTc
  have hOb0 : 0 < x ^ 2 / 3 - x - 1 := by nlinarith
  have hOb1 : x ^ 2 / 3 - x - 1 ≤ (384732211 / 100000000) ^ 2 / 3 - 384732211 / 100000000 - 1 := by
    nlinarith
  have hOb2 : (38473221 / 10000000) ^ 2 / 3 - 38473221 / 10000000 - 1 ≤ x ^ 2 / 3 - x - 1 := by
    nlinarith
  have hPc0 : 0 < Pc := by
    have : b * Pc = (x ^ 2 / 3 - x - 1) * (R * Tc) := by
      rw [← h2]; field_simp
    nlinarith
  -- the coexistence isotherm
  have hsq : Real.sqrt (7 / 10 * Tc) = Real.sqrt (7 / 10) * Real.sqrt Tc :=
    Real.sqrt_mul (by norm_num) Tc
  have hS0 : (836660026 / 1000000000 : ℝ) < Real.sqrt (7 / 10) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hS1 : Real.sqrt (7 / 10) < 836660027 / 1000000000 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  set s := Real.sqrt (7 / 10) with hs
  have hs0 : 0 < s := by linarith
  have ha_eq : A / Real.sqrt (7 / 10 * Tc) = ac / s := by
    rw [hsq, hac, div_div, mul_comm]
  have ha0 : 0 < A / Real.sqrt (7 / 10 * Tc) := by rw [ha_eq]; positivity
  -- θ at 0.7 T_c
  have hK : R * Tc * b / ac = 9 * (x ^ 2 / 3 - x - 1) / x := by
    have hx0 : 0 < x := by linarith
    have e : R * Tc * b / ac = (b * Pc / (R * Tc)) / (ac * Pc / (R * Tc) ^ 2) := by
      field_simp
    rw [e, h2, h3]; field_simp
  have hθ : R * (7 / 10 * Tc) * b / (A / Real.sqrt (7 / 10 * Tc))
      = 7 / 10 * s * (9 * (x ^ 2 / 3 - x - 1) / x) := by
    rw [ha_eq, ← hK]; field_simp
  have hKe : 9 * (x ^ 2 / 3 - x - 1) / x = 3 * x - 9 - 9 / x := by
    field_simp; ring
  have hK0 : 3 * (38473221 / 10000000) - 9 - 9 / (38473221 / 10000000) ≤ 3 * x - 9 - 9 / x := by
    have : 9 / x ≤ 9 / (38473221 / 10000000) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) lo.le
    linarith
  have hK1 : 3 * x - 9 - 9 / x ≤ 3 * (384732211 / 100000000) - 9 - 9 / (384732211 / 100000000) := by
    have : 9 / (384732211 / 100000000) ≤ 9 / x :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) hi.le
    linarith
  have hθ0 : 1187001329 / 10000000000 ≤ R * (7 / 10 * Tc) * b / (A / Real.sqrt (7 / 10 * Tc)) := by
    rw [hθ, hKe]
    have m := mul_le_mul (le_of_lt hS0) hK0 (by norm_num) hs0.le
    have : (1187001329 / 10000000000 : ℝ) ≤ 7 / 10 * ((836660026 / 1000000000) *
        (3 * (38473221 / 10000000) - 9 - 9 / (38473221 / 10000000))) := by norm_num
    nlinarith
  have hθ1 : R * (7 / 10 * Tc) * b / (A / Real.sqrt (7 / 10 * Tc)) ≤ 593500771 / 5000000000 := by
    rw [hθ, hKe]
    have hK' : 0 ≤ 3 * x - 9 - 9 / x := by rw [← hKe]; positivity
    have m := mul_le_mul (le_of_lt hS1) hK1 hK' (by norm_num)
    have : 7 / 10 * ((836660027 / 1000000000) *
        (3 * (384732211 / 100000000) - 9 - 9 / (384732211 / 100000000))) ≤ (593500771 / 5000000000 : ℝ) := by
      norm_num
    nlinarith
  obtain ⟨wlo, whi⟩ := window_of_maxwell R (A / Real.sqrt (7 / 10 * Tc)) b (7 / 10 * Tc) vl vg ps ha0 hb hθ0 hθ1 hl h
  set pr := ps / (A / Real.sqrt (7 / 10 * Tc) / b ^ 2) with hpr
  -- the pressure ratio
  have hratio : ps / Pc = pr * (x / 9) / (s * (x ^ 2 / 3 - x - 1) ^ 2) := by
    have hb0 : b ≠ 0 := hb.ne'
    have hRT0 : R * Tc ≠ 0 := hRT.ne'
    have hObne : x ^ 2 / 3 - x - 1 ≠ 0 := hOb0.ne'
    have hPcne : Pc ≠ 0 := hPc0.ne'
    have hsne : s ≠ 0 := hs0.ne'
    have hab : A / Real.sqrt (7 / 10 * Tc) / b ^ 2 ≠ 0 := by positivity
    have hps : ps = pr * (A / Real.sqrt (7 / 10 * Tc) / b ^ 2) := by
      rw [hpr]; field_simp
    have e1 : ac = x / 9 * (R * Tc) ^ 2 / Pc := by rw [← h3]; field_simp
    have e2 : b = (x ^ 2 / 3 - x - 1) * (R * Tc) / Pc := by rw [← h2]; field_simp
    rw [hps, ha_eq, e1]
    have e3 : b ^ 2 = ((x ^ 2 / 3 - x - 1) * (R * Tc) / Pc) ^ 2 := by rw [← e2]
    rw [e3]
    field_simp
  have hN0 : 2569 / 2000000 * ((38473221 / 10000000) / 9) ≤ pr * (x / 9) :=
    mul_le_mul wlo (by linarith) (by norm_num) (by linarith)
  have hN1 : pr * (x / 9) ≤ 12849 / 10000000 * ((384732211 / 100000000) / 9) :=
    mul_le_mul whi (by linarith) (by linarith) (by norm_num)
  have hD1 : s * (x ^ 2 / 3 - x - 1) ^ 2 ≤ (836660027 / 1000000000) *
      ((384732211 / 100000000) ^ 2 / 3 - 384732211 / 100000000 - 1) ^ 2 :=
    mul_le_mul hS1.le (pow_le_pow_left₀ hOb0.le hOb1 2) (by positivity) (by norm_num)
  have hD0 : (836660026 / 1000000000) *
      ((38473221 / 10000000) ^ 2 / 3 - 38473221 / 10000000 - 1) ^ 2 ≤ s * (x ^ 2 / 3 - x - 1) ^ 2 :=
    mul_le_mul hS0.le (pow_le_pow_left₀ (by norm_num) hOb2 2) (by norm_num) hs0.le
  have hDpos : 0 < s * (x ^ 2 / 3 - x - 1) ^ 2 := by positivity
  have r1 : (4371501 / 50000000 : ℝ) ≤ ps / Pc := by
    rw [hratio]
    have := div_le_div₀ (by linarith) hN0 hDpos hD1
    have h' : (4371501 / 50000000 : ℝ) ≤ 2569 / 2000000 * ((38473221 / 10000000) / 9) /
        ((836660027 / 1000000000) *
          ((384732211 / 100000000) ^ 2 / 3 - 384732211 / 100000000 - 1) ^ 2) := by norm_num
    linarith
  have r2 : ps / Pc ≤ 8745729 / 100000000 := by
    rw [hratio]
    have := div_le_div₀ (by norm_num) hN1 (by norm_num) hD0
    have h' : 12849 / 10000000 * ((384732211 / 100000000) / 9) /
        ((836660026 / 1000000000) *
          ((38473221 / 10000000) ^ 2 / 3 - 38473221 / 10000000 - 1) ^ 2) ≤ (8745729 / 100000000 : ℝ) := by
      norm_num
    linarith
  obtain ⟨c1, c2⟩ := ratio_acentric r1 r2
  exact ⟨c1, by unfold acentric; exact c2⟩


end Checked.Chemistry.RKReduced
