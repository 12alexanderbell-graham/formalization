import Checked.Math.ThomasFermi
import Checked.Trust.NonVacuity

/-! Hypothesis necessity for `Checked.Math.ThomasFermi.tf_initial_slope` (run 2026-11-19T1228Z). The
positivity hypothesis and the limit at infinity are each REDUNDANT: either follows from the others.
Mathlib's real power with exponent three halves is zero for a negative base (the cosine of three halves of
pi is zero), so the second derivative of y is never negative and its derivative φ is nondecreasing.

Positivity (`tf_pos`): if φ were positive somewhere, y would grow at least linearly and could not tend to
zero; so y is nonincreasing, and a nonincreasing function tending to zero is never negative. If y vanished
at a point z, φ would vanish there (a minimum inside the half-line); on the half unit before z the second
derivative is at most M to the power three halves over the square root of the abscissa, M the value of y at
the left end, so φ is at least minus three halves of M to the power three halves there, and M is at most
three quarters of M to the power three halves, at most three quarters of M (M lies between zero and one),
so M is zero. Repeating the step half a unit at a time reaches the origin, where y is one.

Limit (`tf_lim`): if φ is never positive, y decreases to a limit, and a positive limit would make φ grow
like the square root of the abscissa. If φ is positive at b, then on a window from X to twice X (X large) the
energy φ squared minus K times y to the power five halves does not decrease, so φ is at least the square
root of K times (y minus y at X) to the power five quarters, and (y minus y at X) to the power minus one
quarter decreases at rate at least a quarter of the square root of K: it would become negative inside the
window, so a positive solution does not exist there. -/

namespace Checked.Trust.NecessityAZ
open Set Filter Topology

lemma rpow32_nonneg (x : ℝ) : 0 ≤ x ^ ((3 : ℝ) / 2) := by
  rcases le_or_gt 0 x with h | h
  · exact Real.rpow_nonneg h _
  · rw [Real.rpow_def_of_neg h]
    have hc : Real.cos (3 / 2 * Real.pi) = 0 := by
      rw [show 3 / 2 * Real.pi = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi, Real.cos_pi_div_two]
      simp
    rw [hc, mul_zero]

lemma sqrt_sub_le {s z : ℝ} (hs : 0 ≤ s) (hsz : s ≤ z) (hz : z ≤ s + 1 / 2) :
    Real.sqrt z - Real.sqrt s ≤ 3 / 4 := by
  have h1 := Real.sq_sqrt hs
  have h2 := Real.sq_sqrt (hs.trans hsz)
  have h3 : Real.sqrt s ≤ Real.sqrt z := Real.sqrt_le_sqrt hsz
  have h4 := Real.sqrt_nonneg s
  have h5 : (Real.sqrt z - Real.sqrt s) ^ 2 ≤ 1 / 2 := by nlinarith
  nlinarith

/-- The positivity of the Thomas–Fermi function follows from the other hypotheses of
`tf_initial_slope`. -/
theorem tf_pos (y φ : ℝ → ℝ)
    (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (h0 : y 0 = 1) (hlim : Tendsto y atTop (𝓝 0)) :
    ∀ x, 0 ≤ x → 0 < y x := by
  have hyA : ∀ x, 0 < x → HasDerivAt y (φ x) x := fun x hx =>
    (hy x hx.le).hasDerivAt (Ici_mem_nhds hx)
  have hyc : ContinuousOn y (Ici 0) := fun x hx => (hy x hx).continuousWithinAt
  have hφc : ContinuousOn φ (Ici 0) := by
    intro x hx
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ x from hx) with h | h
    · subst h; exact hφ0
    · exact (hφ x h).continuousAt.continuousWithinAt
  have hint : interior (Ici (0 : ℝ)) = Ioi 0 := interior_Ici
  -- φ is nondecreasing on the half-line
  have hφmono : MonotoneOn φ (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hφc ?_ ?_
    · rw [hint]; exact fun x hx => (hφ x hx).differentiableAt.differentiableWithinAt
    · rw [hint]; intro x hx
      rw [(hφ x hx).deriv]
      exact div_nonneg (rpow32_nonneg _) (Real.sqrt_nonneg _)
  -- φ ≤ 0
  have hφneg : ∀ x, 0 ≤ x → φ x ≤ 0 := by
    intro b hb
    by_contra hpos
    push Not at hpos
    have hg : MonotoneOn (fun x => y x - φ b * x) (Ici b) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici b) ?_ ?_ ?_
      · exact ((hyc.mono fun x hx => le_trans hb hx).sub (continuousOn_const.mul continuousOn_id))
      · rw [interior_Ici]; intro x hx
        exact ((hyA x (lt_of_le_of_lt hb hx)).sub
          ((hasDerivAt_id x).const_mul (φ b))).differentiableAt.differentiableWithinAt
      · rw [interior_Ici]; intro x hx
        have hx0 : 0 < x := lt_of_le_of_lt hb hx
        have hd : HasDerivAt (fun x => y x - φ b * x) (φ x - φ b * 1) x :=
          (hyA x hx0).sub ((hasDerivAt_id x).const_mul (φ b))
        rw [hd.deriv]
        have := hφmono (show b ∈ Ici (0 : ℝ) from hb) (show x ∈ Ici (0 : ℝ) from hx0.le) hx.le
        simp only [mul_one]
        linarith
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
    set x := max N (b + (1 + |y b|) / φ b) with hxdef
    have hx1 : b + (1 + |y b|) / φ b ≤ x := le_max_right _ _
    have hbx : b ≤ x := by
      have : 0 ≤ (1 + |y b|) / φ b := div_nonneg (by positivity) hpos.le
      linarith
    have hm := hg (show b ∈ Ici b from le_refl b) (show x ∈ Ici b from hbx) hbx
    simp only at hm
    have hlt := hN x (le_max_left _ _)
    have : φ b * (x - b) ≥ 1 + |y b| := by
      have h2 : (1 + |y b|) / φ b ≤ x - b := by linarith
      rw [div_le_iff₀ hpos] at h2
      linarith
    have := neg_abs_le (y b)
    nlinarith
  -- y is nonincreasing and nonnegative
  have hyanti : AntitoneOn y (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hyc ?_ ?_
    · rw [hint]; exact fun x hx => (hyA x hx).differentiableAt.differentiableWithinAt
    · rw [hint]; intro x hx
      rw [(hyA x hx).deriv]
      exact hφneg x hx.le
  have hynn : ∀ x, 0 ≤ x → 0 ≤ y x := by
    intro x hx
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨x, fun z hz => ?_⟩)
    exact hyanti (show x ∈ Ici (0 : ℝ) from hx) (show z ∈ Ici (0 : ℝ) from hx.trans hz) hz
  have hy1 : ∀ x, 0 ≤ x → y x ≤ 1 := fun x hx => by
    rw [← h0]; exact hyanti (Set.mem_Ici.2 (le_refl (0 : ℝ))) (show x ∈ Ici (0 : ℝ) from hx) hx
  -- the step: a zero at z > 0 gives a zero at max 0 (z - 1/2)
  have step : ∀ z, 0 < z → y z = 0 → y (max 0 (z - 1 / 2)) = 0 := by
    intro z hz hyz
    set w := max 0 (z - 1 / 2) with hwdef
    have hw0 : 0 ≤ w := le_max_left _ _
    have hwz : w ≤ z := max_le hz.le (by linarith)
    have hzw : z ≤ w + 1 / 2 := by have := le_max_right 0 (z - 1 / 2); linarith
    set M := y w with hMdef
    have hM0 : 0 ≤ M := hynn w hw0
    have hM1 : M ≤ 1 := hy1 w hw0
    -- φ z = 0 (a minimum inside the half-line)
    have hφz : φ z = 0 := by
      have hmin : IsLocalMin y z := by
        filter_upwards [Ioi_mem_nhds hz] with x hx
        rw [hyz]; exact hynn x (le_of_lt hx)
      exact hmin.hasDerivAt_eq_zero (hyA z hz)
    -- on [w, z], φ ≥ -(3/2) M^{3/2}
    have hyM : ∀ x, w ≤ x → y x ≤ M := fun x hx =>
      hyanti (show w ∈ Ici (0 : ℝ) from hw0) (show x ∈ Ici (0 : ℝ) from hw0.trans hx) hx
    have hP : ∀ x, w ≤ x → y x ^ ((3 : ℝ) / 2) ≤ M ^ ((3 : ℝ) / 2) := fun x hx =>
      Real.rpow_le_rpow (hynn x (hw0.trans hx)) (hyM x hx) (by norm_num)
    set c := M ^ ((3 : ℝ) / 2) with hcdef
    have hc0 : 0 ≤ c := rpow32_nonneg M
    have hφlow : ∀ s ∈ Icc w z, -(3 / 2 * c) ≤ φ s := by
      have hh : AntitoneOn (fun x => φ x - 2 * c * Real.sqrt x) (Icc w z) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc w z) ?_ ?_ ?_
        · exact (hφc.mono fun x hx => hw0.trans hx.1).sub
            (continuousOn_const.mul Real.continuous_sqrt.continuousOn)
        · rw [interior_Icc]; intro x hx
          have hx0 : 0 < x := lt_of_le_of_lt hw0 hx.1
          exact ((hφ x hx0).sub ((Real.hasDerivAt_sqrt hx0.ne').const_mul (2 * c))).differentiableAt.differentiableWithinAt
        · rw [interior_Icc]; intro x hx
          have hx0 : 0 < x := lt_of_le_of_lt hw0 hx.1
          have hd : HasDerivAt (fun x => φ x - 2 * c * Real.sqrt x)
              (y x ^ ((3 : ℝ) / 2) / Real.sqrt x - 2 * c * (1 / (2 * Real.sqrt x))) x :=
            (hφ x hx0).sub ((Real.hasDerivAt_sqrt hx0.ne').const_mul (2 * c))
          rw [hd.deriv]
          have hs := Real.sqrt_pos.2 hx0
          have := hP x hx.1.le
          rw [sub_nonpos, div_le_iff₀ hs]
          field_simp
          linarith
      intro s hs
      have := hh hs (show z ∈ Icc w z from ⟨hwz, le_refl z⟩) hs.2
      simp only at this
      rw [hφz] at this
      have hsq := sqrt_sub_le (hw0.trans hs.1) hs.2 (by linarith [hs.1])
      nlinarith
    -- y w ≤ (3/4) c
    have hk : MonotoneOn (fun x => y x + 3 / 2 * c * x) (Icc w z) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc w z) ?_ ?_ ?_
      · exact (hyc.mono fun x hx => hw0.trans hx.1).add (continuousOn_const.mul continuousOn_id)
      · rw [interior_Icc]; intro x hx
        have hx0 : 0 < x := lt_of_le_of_lt hw0 hx.1
        exact ((hyA x hx0).add ((hasDerivAt_id x).const_mul _)).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]; intro x hx
        have hx0 : 0 < x := lt_of_le_of_lt hw0 hx.1
        have hd : HasDerivAt (fun x => y x + 3 / 2 * c * x) (φ x + 3 / 2 * c * 1) x :=
          (hyA x hx0).add ((hasDerivAt_id x).const_mul _)
        rw [hd.deriv]
        have := hφlow x ⟨hx.1.le, hx.2.le⟩
        simp only [mul_one]
        linarith
    have hkw := hk (show w ∈ Icc w z from ⟨le_refl w, hwz⟩) (show z ∈ Icc w z from ⟨hwz, le_refl z⟩) hwz
    simp only at hkw
    rw [hyz] at hkw
    have hMc : M ≤ 3 / 4 * c := by nlinarith
    have hcM : c ≤ M := by
      rw [hcdef]
      rcases eq_or_lt_of_le hM0 with hM | hM
      · rw [← hM, Real.zero_rpow (by norm_num)]
      calc M ^ ((3 : ℝ) / 2) ≤ M ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hM hM1 (by norm_num)
        _ = M := Real.rpow_one M
    show M = 0
    linarith
  -- iterate down to the origin
  intro x hx
  rcases lt_or_eq_of_le (hynn x hx) with h | h
  · exact h
  exfalso
  have key : ∀ n : ℕ, y (max 0 (x - n / 2)) = 0 := by
    intro n
    induction n with
    | zero => simp only [Nat.cast_zero, zero_div, sub_zero]; rw [max_eq_right hx]; exact h.symm
    | succ n ih =>
      rcases le_or_gt (x - n / 2) 0 with hn | hn
      · have e1 : max 0 (x - (n + 1 : ℕ) / 2) = 0 := by push_cast; exact max_eq_left (by linarith)
        rw [e1]; rw [max_eq_left hn] at ih; exact ih
      · rw [max_eq_right hn.le] at ih
        have := step _ hn ih
        have e : x - n / 2 - 1 / 2 = x - ((n + 1 : ℕ) : ℝ) / 2 := by push_cast; ring
        rwa [e] at this
  obtain ⟨n, hn⟩ := exists_nat_ge (2 * x)
  have := key n
  rw [max_eq_left (by linarith)] at this
  rw [h0] at this
  exact one_ne_zero this

theorem tf_initial_slope_r5 : dropped% Checked.Math.ThomasFermi.tf_initial_slope 5 := by
  intro y φ hy hφ hφ0 h0 hlim
  exact Checked.Math.ThomasFermi.tf_initial_slope y φ hy hφ hφ0 h0 (tf_pos y φ hy hφ hφ0 h0 hlim) hlim

lemma pow52_sub {Y y : ℝ} (hY : 0 ≤ Y) (hYy : Y ≤ y) :
    (y - Y) ^ ((5 : ℝ) / 2) ≤ y ^ ((5 : ℝ) / 2) - Y ^ ((5 : ℝ) / 2) := by
  have hm : MonotoneOn (fun s => s ^ ((5 : ℝ) / 2) - (s - Y) ^ ((5 : ℝ) / 2)) (Ici Y) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici Y) ?_ ?_ ?_
    · refine ContinuousOn.sub ?_ ?_
      · exact fun s _ => (Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).continuousWithinAt
      · exact fun s _ => ((Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).comp
          (continuousAt_id.sub continuousAt_const)).continuousWithinAt
    · rw [interior_Ici]; intro s hs
      exact (((hasDerivAt_id s).rpow_const (p := (5 : ℝ) / 2) (Or.inr (by norm_num))).sub
        (((hasDerivAt_id s).sub_const Y).rpow_const (p := (5 : ℝ) / 2)
          (Or.inr (by norm_num)))).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]; intro s hs
      have hs' : Y < s := hs
      have hd : HasDerivAt (fun s => s ^ ((5 : ℝ) / 2) - (s - Y) ^ ((5 : ℝ) / 2))
          (1 * ((5 : ℝ) / 2) * s ^ ((5 : ℝ) / 2 - 1) - 1 * ((5 : ℝ) / 2) * (s - Y) ^ ((5 : ℝ) / 2 - 1)) s :=
        ((hasDerivAt_id s).rpow_const (Or.inr (by norm_num))).sub
          (((hasDerivAt_id s).sub_const Y).rpow_const (Or.inr (by norm_num)))
      rw [hd.deriv]
      have : (s - Y) ^ ((5 : ℝ) / 2 - 1) ≤ s ^ ((5 : ℝ) / 2 - 1) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      nlinarith
  have := hm (show Y ∈ Ici Y from le_refl Y) (show y ∈ Ici Y from hYy) hYy
  simp only [sub_self] at this
  rw [Real.zero_rpow (by norm_num)] at this
  linarith

lemma big_X {w X K : ℝ} (hw0 : 0 < w) (hX2 : 2 ≤ X) (hXw : 160 * w ^ 2 ≤ X)
    (hKdef : K = 4 / (5 * Real.sqrt (2 * X))) : w ≤ Real.sqrt K / 4 * (X - 1) := by
  have hX0 : 0 < X := by linarith
  have hK0 : 0 < K := by rw [hKdef]; have := Real.sqrt_pos.2 (show 0 < 2 * X by linarith); positivity
  have hs : Real.sqrt (2 * X) ≤ 2 * Real.sqrt X := by
    rw [Real.sqrt_mul (by norm_num)]
    have : Real.sqrt 2 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg X]
  have hsX : 1 ≤ Real.sqrt X := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hsX2 := Real.sq_sqrt hX0.le
  have hKlow : 2 / (5 * Real.sqrt X) ≤ K := by
    rw [hKdef, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hK2 : K * (X - 1) ^ 2 / 16 ≥ w ^ 2 := by
    have h1 : (X - 1) ^ 2 ≥ X ^ 2 / 4 := by nlinarith
    have h2 : 2 / (5 * Real.sqrt X) * (X ^ 2 / 4) = X * Real.sqrt X / 10 := by
      field_simp; nlinarith
    have h3 : K * (X - 1) ^ 2 ≥ X * Real.sqrt X / 10 := by
      rw [← h2]
      exact mul_le_mul hKlow h1 (by positivity) hK0.le
    nlinarith
  have hsK := Real.sq_sqrt hK0.le
  have hr : 0 ≤ Real.sqrt K / 4 * (X - 1) := by
    have := Real.sqrt_nonneg K; nlinarith
  nlinarith [sq_nonneg (w - Real.sqrt K / 4 * (X - 1))]

lemma tf_no_pos_slope (y φ : ℝ → ℝ)
    (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hpos : ∀ x, 0 ≤ x → 0 < y x)
    (b : ℝ) (hb : 0 ≤ b) (hv : 0 < φ b) : False := by
  have hyA : ∀ x, 0 < x → HasDerivAt y (φ x) x := fun x hx =>
    (hy x hx.le).hasDerivAt (Ici_mem_nhds hx)
  have hyc : ContinuousOn y (Ici 0) := fun x hx => (hy x hx).continuousWithinAt
  have hφc : ContinuousOn φ (Ici 0) := by
    intro x hx
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ x from hx) with h | h
    · subst h; exact hφ0
    · exact (hφ x h).continuousAt.continuousWithinAt
  have hint : interior (Ici (0 : ℝ)) = Ioi 0 := interior_Ici
  have hφmono : MonotoneOn φ (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hφc ?_ ?_
    · rw [hint]; exact fun x hx => (hφ x hx).differentiableAt.differentiableWithinAt
    · rw [hint]; intro x hx
      rw [(hφ x hx).deriv]
      exact div_nonneg (rpow32_nonneg _) (Real.sqrt_nonneg _)
  set v := φ b with hvdef
  have hφv : ∀ x, b ≤ x → v ≤ φ x := fun x hx =>
    hφmono (show b ∈ Ici (0 : ℝ) from hb) (show x ∈ Ici (0 : ℝ) from hb.trans hx) hx
  -- y grows at rate at least v after b
  have hlin : MonotoneOn (fun x => y x - v * x) (Ici b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici b) ?_ ?_ ?_
    · exact ((hyc.mono fun x hx => le_trans hb hx).sub (continuousOn_const.mul continuousOn_id))
    · rw [interior_Ici]; intro x hx
      exact ((hyA x (lt_of_le_of_lt hb hx)).sub
        ((hasDerivAt_id x).const_mul v)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]; intro x hx
      have hx0 : 0 < x := lt_of_le_of_lt hb hx
      have hd : HasDerivAt (fun x => y x - v * x) (φ x - v * 1) x :=
        (hyA x hx0).sub ((hasDerivAt_id x).const_mul v)
      rw [hd.deriv]
      have := hφv x hx.le
      linarith
  set w := v ^ (-(1 : ℝ) / 4) with hwdef
  have hw0 : 0 < w := Real.rpow_pos_of_pos hv _
  set X := max (max 2 (b + 1)) (160 * w ^ 2) with hXdef
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) (le_max_left _ _)
  have hXb : b + 1 ≤ X := le_trans (le_max_right _ _) (le_max_left _ _)
  have hXw : 160 * w ^ 2 ≤ X := le_max_right _ _
  have hX0 : 0 < X := by linarith
  set K := 4 / (5 * Real.sqrt (2 * X)) with hKdef
  have hs2X : 0 < Real.sqrt (2 * X) := Real.sqrt_pos.2 (by linarith)
  have hK0 : 0 < K := by positivity
  set Y := y X with hYdef
  have hY0 : 0 < Y := hpos X hX0.le
  -- energy on [X, 2X]
  have hE : MonotoneOn (fun x => φ x ^ 2 - K * y x ^ ((5 : ℝ) / 2)) (Icc X (2 * X)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc X (2 * X)) ?_ ?_ ?_
    · refine ContinuousOn.sub ?_ ?_
      · exact (hφc.mono fun x hx => hX0.le.trans hx.1).pow 2
      · refine ContinuousOn.mul continuousOn_const ?_
        exact ContinuousOn.rpow_const (hyc.mono fun x hx => hX0.le.trans hx.1)
          (fun _ _ => Or.inr (by norm_num))
    · rw [interior_Icc]; intro x hx
      have hx0 : 0 < x := lt_trans hX0 hx.1
      exact (((hφ x hx0).pow 2).sub (((hyA x hx0).rpow_const (p := (5 : ℝ) / 2)
        (Or.inl (hpos x hx0.le).ne')).const_mul K)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro x hx
      have hx0 : 0 < x := lt_trans hX0 hx.1
      have hd : HasDerivAt (fun x => φ x ^ 2 - K * y x ^ ((5 : ℝ) / 2))
          (((2 : ℕ) : ℝ) * φ x ^ (2 - 1) * (y x ^ ((3 : ℝ) / 2) / Real.sqrt x)
            - K * (φ x * ((5 : ℝ) / 2) * y x ^ ((5 : ℝ) / 2 - 1))) x :=
        ((hφ x hx0).pow 2).sub (((hyA x hx0).rpow_const (Or.inl (hpos x hx0.le).ne')).const_mul K)
      rw [hd.deriv]
      have e1 : (5 : ℝ) / 2 - 1 = 3 / 2 := by norm_num
      rw [e1]
      have hφx : 0 ≤ φ x := hv.le.trans (hφv x (by linarith [hx.1]))
      have hP := rpow32_nonneg (y x)
      have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
      have hsle : Real.sqrt x ≤ Real.sqrt (2 * X) := Real.sqrt_le_sqrt hx.2.le
      have hK : K * (5 / 2) = 2 / Real.sqrt (2 * X) := by rw [hKdef]; field_simp; ring
      have h1 : 2 / Real.sqrt (2 * X) ≤ 2 / Real.sqrt x := by
        apply div_le_div_of_nonneg_left (by norm_num) hsx hsle
      have : K * (φ x * (5 / 2) * y x ^ ((3 : ℝ) / 2)) = φ x * y x ^ ((3 : ℝ) / 2) * (2 / Real.sqrt (2 * X)) := by
        rw [← hK]; ring
      rw [this]
      have : ((2 : ℕ) : ℝ) * φ x ^ (2 - 1) * (y x ^ ((3 : ℝ) / 2) / Real.sqrt x)
          = φ x * y x ^ ((3 : ℝ) / 2) * (2 / Real.sqrt x) := by
        simp only [Nat.cast_ofNat]; ring
      rw [this, sub_nonneg]
      exact mul_le_mul_of_nonneg_left h1 (mul_nonneg hφx hP)
  -- φ ≥ √K (y - Y)^{5/4} on [X, 2X]
  have hφz : ∀ x ∈ Icc X (2 * X), Real.sqrt K * (y x - Y) ^ ((5 : ℝ) / 4) ≤ φ x := by
    intro x hx
    have hm := hE (show X ∈ Icc X (2 * X) from ⟨le_refl X, by linarith⟩) hx hx.1
    simp only at hm
    have hφx : 0 ≤ φ x := hv.le.trans (hφv x (by linarith [hx.1]))
    have hyY : Y ≤ y x := by
      have := hlin (show X ∈ Ici b from by simp only [mem_Ici]; linarith)
        (show x ∈ Ici b from by simp only [mem_Ici]; linarith [hx.1]) hx.1
      simp only at this
      nlinarith [hx.1]
    have hp := pow52_sub hY0.le hyY
    have hsq : (Real.sqrt K * (y x - Y) ^ ((5 : ℝ) / 4)) ^ 2 = K * (y x - Y) ^ ((5 : ℝ) / 2) := by
      rw [mul_pow, Real.sq_sqrt hK0.le, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    have hφ2 : K * (y x - Y) ^ ((5 : ℝ) / 2) ≤ φ x ^ 2 := by
      have := sq_nonneg (φ X)
      nlinarith [mul_le_mul_of_nonneg_left hp hK0.le]
    have hl0 : 0 ≤ Real.sqrt K * (y x - Y) ^ ((5 : ℝ) / 4) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by linarith) _)
    nlinarith [sq_nonneg (φ x - Real.sqrt K * (y x - Y) ^ ((5 : ℝ) / 4)),
      sq_nonneg (φ x + Real.sqrt K * (y x - Y) ^ ((5 : ℝ) / 4))]
  -- z = y - Y is at least v on [X + 1, 2X]
  have hzv : ∀ x, X + 1 ≤ x → v ≤ y x - Y := by
    intro x hx
    have := hlin (show X ∈ Ici b from by simp only [mem_Ici]; linarith)
      (show x ∈ Ici b from by simp only [mem_Ici]; linarith) (by linarith)
    simp only at this
    nlinarith
  -- g = z^{-1/4} decreases at rate √K/4
  have hG : AntitoneOn (fun x => (y x - Y) ^ (-(1 : ℝ) / 4) + Real.sqrt K / 4 * x) (Icc (X + 1) (2 * X)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc (X + 1) (2 * X)) ?_ ?_ ?_
    · refine ContinuousOn.add ?_ (continuousOn_const.mul continuousOn_id)
      refine ContinuousOn.rpow_const ((hyc.mono fun x hx => ?_).sub continuousOn_const) ?_
      · exact (show (0 : ℝ) ≤ x by linarith [hx.1])
      · intro x hx; left; linarith [hzv x hx.1]
    · rw [interior_Icc]; intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hz : y x - Y ≠ 0 := by linarith [hzv x hx.1.le]
      exact ((((hyA x hx0).sub_const Y).rpow_const (Or.inl hz)).add
        ((hasDerivAt_id x).const_mul _)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hzpos : 0 < y x - Y := by linarith [hzv x hx.1.le]
      have hd : HasDerivAt (fun x => (y x - Y) ^ (-(1 : ℝ) / 4) + Real.sqrt K / 4 * x)
          (φ x * (-(1 : ℝ) / 4) * (y x - Y) ^ (-(1 : ℝ) / 4 - 1) + Real.sqrt K / 4 * 1) x :=
        (((hyA x hx0).sub_const Y).rpow_const (Or.inl hzpos.ne')).add ((hasDerivAt_id x).const_mul _)
      rw [hd.deriv]
      have hb' := hφz x ⟨by linarith [hx.1], hx.2.le⟩
      have hq : (y x - Y) ^ ((5 : ℝ) / 4) * (y x - Y) ^ (-(1 : ℝ) / 4 - 1) = 1 := by
        rw [← Real.rpow_add hzpos]; norm_num
      have hpos' : 0 < (y x - Y) ^ (-(1 : ℝ) / 4 - 1) := Real.rpow_pos_of_pos hzpos _
      have := mul_le_mul_of_nonneg_right hb' hpos'.le
      rw [mul_assoc, hq, mul_one] at this
      nlinarith
  have hG2 := hG (show X + 1 ∈ Icc (X + 1) (2 * X) from ⟨le_refl _, by linarith⟩)
    (show 2 * X ∈ Icc (X + 1) (2 * X) from ⟨by linarith, le_refl _⟩) (by linarith)
  simp only at hG2
  have hg2 : 0 < (y (2 * X) - Y) ^ (-(1 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (by linarith [hzv (2 * X) (by linarith)]) _
  have hg1 : (y (X + 1) - Y) ^ (-(1 : ℝ) / 4) ≤ w :=
    Real.rpow_le_rpow_of_nonpos hv (hzv (X + 1) le_rfl) (by norm_num)
  -- √K (X - 1) / 4 ≥ w
  have hKX : w ≤ Real.sqrt K / 4 * (X - 1) := big_X hw0 hX2 hXw hKdef
  linarith

lemma tf_lim_of_nonpos (y φ : ℝ → ℝ)
    (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hpos : ∀ x, 0 ≤ x → 0 < y x)
    (hφneg : ∀ x, 0 ≤ x → φ x ≤ 0) : Tendsto y atTop (𝓝 0) := by
  have hyA : ∀ x, 0 < x → HasDerivAt y (φ x) x := fun x hx =>
    (hy x hx.le).hasDerivAt (Ici_mem_nhds hx)
  have hyc : ContinuousOn y (Ici 0) := fun x hx => (hy x hx).continuousWithinAt
  have hφc : ContinuousOn φ (Ici 0) := by
    intro x hx
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ x from hx) with h | h
    · subst h; exact hφ0
    · exact (hφ x h).continuousAt.continuousWithinAt
  have hint : interior (Ici (0 : ℝ)) = Ioi 0 := interior_Ici
  have hφmono : MonotoneOn φ (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hφc ?_ ?_
    · rw [hint]; exact fun x hx => (hφ x hx).differentiableAt.differentiableWithinAt
    · rw [hint]; intro x hx
      rw [(hφ x hx).deriv]
      exact div_nonneg (rpow32_nonneg _) (Real.sqrt_nonneg _)
  have hyanti : AntitoneOn y (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hyc ?_ ?_
    · rw [hint]; exact fun x hx => (hyA x hx).differentiableAt.differentiableWithinAt
    · rw [hint]; intro x hx
      rw [(hyA x hx).deriv]
      exact hφneg x hx.le
  rw [tendsto_order]
  refine ⟨fun a ha => eventually_atTop.2 ⟨0, fun x hx => lt_of_lt_of_le ha (hpos x hx).le⟩,
    fun a ha => ?_⟩
  -- some value of y is below a
  have hex : ∃ x0, 0 ≤ x0 ∧ y x0 < a := by
    by_contra hno
    push Not at hno
    set c := a ^ ((3 : ℝ) / 2) with hcdef
    have hc0 : 0 < c := Real.rpow_pos_of_pos ha _
    have hh : MonotoneOn (fun x => φ x - 2 * c * Real.sqrt x) (Ici 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 1) ?_ ?_ ?_
      · exact (hφc.mono fun x (hx : (1 : ℝ) ≤ x) => show x ∈ Ici (0 : ℝ) from le_trans zero_le_one hx).sub
          (continuousOn_const.mul Real.continuous_sqrt.continuousOn)
      · rw [interior_Ici]; intro x hx
        have hx0 : 0 < x := lt_trans one_pos hx
        exact ((hφ x hx0).sub ((Real.hasDerivAt_sqrt hx0.ne').const_mul (2 * c))).differentiableAt.differentiableWithinAt
      · rw [interior_Ici]; intro x hx
        have hx0 : 0 < x := lt_trans one_pos hx
        have hd : HasDerivAt (fun x => φ x - 2 * c * Real.sqrt x)
            (y x ^ ((3 : ℝ) / 2) / Real.sqrt x - 2 * c * (1 / (2 * Real.sqrt x))) x :=
          (hφ x hx0).sub ((Real.hasDerivAt_sqrt hx0.ne').const_mul (2 * c))
        rw [hd.deriv]
        have hs := Real.sqrt_pos.2 hx0
        have : c ≤ y x ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow ha.le (hno x hx0.le) (by norm_num)
        rw [sub_nonneg]
        field_simp
        linarith
    -- at a large x, φ x > 0
    set T := ((|φ 1| + 2 * c + 1) / (2 * c)) ^ 2 + 1 with hT
    have hT1 : 1 ≤ T := by have := sq_nonneg ((|φ 1| + 2 * c + 1) / (2 * c)); linarith
    have hm := hh (Set.mem_Ici.2 (le_refl (1 : ℝ))) (show T ∈ Ici (1 : ℝ) from hT1) hT1
    simp only [Real.sqrt_one, mul_one] at hm
    have hsT : (|φ 1| + 2 * c + 1) / (2 * c) ≤ Real.sqrt T := by
      rw [show (|φ 1| + 2 * c + 1) / (2 * c) = Real.sqrt (((|φ 1| + 2 * c + 1) / (2 * c)) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by linarith)
    have h2 : 2 * c * Real.sqrt T ≥ |φ 1| + 2 * c + 1 := by
      rw [div_le_iff₀ (by positivity)] at hsT; linarith
    have := hφneg T (by linarith)
    have := neg_abs_le (φ 1)
    linarith
  obtain ⟨x0, hx0, hya⟩ := hex
  exact eventually_atTop.2 ⟨x0, fun x hx =>
    lt_of_le_of_lt (hyanti (show x0 ∈ Ici (0 : ℝ) from hx0) (show x ∈ Ici (0 : ℝ) from hx0.trans hx) hx) hya⟩


/-- The limit at infinity of the Thomas–Fermi function follows from the other hypotheses of
`tf_initial_slope`. -/
theorem tf_lim (y φ : ℝ → ℝ)
    (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hpos : ∀ x, 0 ≤ x → 0 < y x) :
    Tendsto y atTop (𝓝 0) := by
  by_cases hB : ∃ b, 0 ≤ b ∧ 0 < φ b
  · obtain ⟨b, hb, hv⟩ := hB
    exact (tf_no_pos_slope y φ hy hφ hφ0 hpos b hb hv).elim
  · push Not at hB
    exact tf_lim_of_nonpos y φ hy hφ hφ0 hpos hB

theorem tf_initial_slope_r6 : dropped% Checked.Math.ThomasFermi.tf_initial_slope 6 := by
  intro y φ hy hφ hφ0 h0 hpos
  exact Checked.Math.ThomasFermi.tf_initial_slope y φ hy hφ hφ0 h0 hpos (tf_lim y φ hy hφ hφ0 hpos)

end Checked.Trust.NecessityAZ
