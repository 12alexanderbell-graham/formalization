import Checked.Math.GMaxPrinciple
import Checked.Math.GRadialPoisson
import Checked.Math.GelfandPDE

/-!
# The Gelfand bound without the radial-symmetry hypothesis

If `u` is a classical solution of `Δu + λ eᵘ = 0` in the unit ball of `ℝ³`, zero on the sphere,
then λ is at most the bound printed in the statement of
`Checked.Math.GelfandPDE.gelfand_pde_radial_bound`. We remove the symmetry hypothesis of
`Checked.Math.GelfandPDE.gelfand_pde_radial_bound` by the minimal-solution argument: the monotone
iteration `w₀ = 0`, `w_{n+1} = P(λ e^{w_n})` (radial Poisson solution operator) stays below `u`
by the maximum principle, converges to a radial solution `w∞ ≤ u`, and the radial bound applies
to `w∞`. Promoted from `Work/Math/GSymFree.lean`.
-/

namespace Checked.Math.GSymFree
open Set Filter Topology InnerProductSpace Laplacian Metric
open Checked.Math.GRadialPoisson
open scoped Interval

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)

/-- Clamp to `[0,1]`. -/
noncomputable def gsf_c (t : ℝ) : ℝ := max 0 (min t 1)

theorem gsf_c_mem (t : ℝ) : gsf_c t ∈ Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem gsf_c_eq {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : gsf_c t = t := by
  simp [gsf_c, min_eq_left ht.2, max_eq_right ht.1]

theorem gsf_c_cont : Continuous gsf_c :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The iterates `w₀ = 0`, `w_{n+1} = P (λ e^{w_n ∘ c})`. -/
noncomputable def gsf_w (lam : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => P (fun t => lam * Real.exp (gsf_w lam n (gsf_c t)))

theorem gsf_w_zero (lam r : ℝ) : gsf_w lam 0 r = 0 := rfl

theorem gsf_w_succ (lam : ℝ) (n : ℕ) :
    gsf_w lam (n + 1) = P (fun t => lam * Real.exp (gsf_w lam n (gsf_c t))) := rfl

theorem gsf_exp_lip_aux {a b M : ℝ} (hab : b ≤ a) (ha : a ≤ M) :
    Real.exp a - Real.exp b ≤ Real.exp M * (a - b) := by
  have h1 : Real.exp b = Real.exp a * Real.exp (b - a) := by rw [← Real.exp_add]; ring_nf
  have h2 := Real.add_one_le_exp (b - a)
  have h3 : Real.exp a ≤ Real.exp M := Real.exp_le_exp.2 ha
  have h4 := Real.exp_pos a
  rw [h1]
  nlinarith [mul_le_mul_of_nonneg_left h2 h4.le, mul_le_mul_of_nonneg_right h3 (sub_nonneg.2 hab)]

theorem gsf_exp_lip {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    |Real.exp a - Real.exp b| ≤ Real.exp M * |a - b| := by
  rcases le_total b a with hab | hab
  · rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 hab)), abs_of_nonneg (sub_nonneg.2 hab)]
    exact gsf_exp_lip_aux hab ha
  · rw [abs_sub_comm, abs_sub_comm a b,
      abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 hab)), abs_of_nonneg (sub_nonneg.2 hab)]
    exact gsf_exp_lip_aux hab hb

/-- `∫₀^r t² h ≤ B r³` for `|h| ≤ B`. -/
theorem gsf_I_bound {h : ℝ → ℝ} {B : ℝ} (hbd : ∀ t, |h t| ≤ B) {r : ℝ} (hr0 : 0 < r) :
    |∫ t in (0:ℝ)..r, t ^ 2 * h t| ≤ B * r ^ 3 := by
  have b : ∀ t ∈ Ι (0:ℝ) r, ‖t ^ 2 * h t‖ ≤ r ^ 2 * B := by
    intro t ht
    rw [uIoc_of_le hr0.le] at ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg t)]
    exact mul_le_mul (pow_le_pow_left₀ ht.1.le ht.2 2) (hbd t) (abs_nonneg _) (sq_nonneg r)
  have := intervalIntegral.norm_integral_le_of_norm_le_const b
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hr0] at this
  calc _ ≤ r ^ 2 * B * r := this
    _ = _ := by ring

/-- Quadratic estimate at the centre: `|P h r − P h 0| ≤ B r²`. -/
theorem gsf_quad {h : ℝ → ℝ} {B : ℝ} (hc : Continuous h) (hbd : ∀ t, |h t| ≤ B)
    {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) : |P h r - P h 0| ≤ B * r ^ 2 := by
  rcases eq_or_lt_of_le hr.1 with h0 | hr0
  · subst h0; simp
  rw [grp_diff hc hr0]
  have b : ∀ t ∈ Ι (0:ℝ) r, ‖(t ^ 2 * r⁻¹ - t) * h t‖ ≤ r * B := by
    intro t ht
    rw [uIoc_of_le hr0.le] at ht
    have q1 : t ^ 2 * r⁻¹ ≤ t := by
      rw [← div_eq_mul_inv, div_le_iff₀ hr0]; nlinarith [ht.1, ht.2]
    have q2 : 0 ≤ t ^ 2 * r⁻¹ := by positivity
    have ha : |t ^ 2 * r⁻¹ - t| ≤ r := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ha (hbd t) (abs_nonneg _) hr0.le
  have := intervalIntegral.norm_integral_le_of_norm_le_const b
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hr0] at this
  calc _ ≤ r * B * r := this
    _ = _ := by ring

/-- Lipschitz estimate on `[0,1]`: `|P h r − P h s| ≤ B |r − s|`. -/
theorem gsf_lip {h : ℝ → ℝ} {B : ℝ} (hc : Continuous h) (hbd : ∀ t, |h t| ≤ B)
    {r s : ℝ} (hr : r ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) :
    |P h r - P h s| ≤ B * |r - s| := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hbd 0)
  have key : ∀ s ∈ Icc (0:ℝ) 1, |P h s - P h 0| ≤ B * s := fun s hs => by
    calc _ ≤ B * s ^ 2 := gsf_quad hc hbd hs
      _ ≤ B * s := mul_le_mul_of_nonneg_left (by nlinarith [hs.1, hs.2]) hB
  rcases eq_or_lt_of_le hr.1 with h0 | hr0
  · subst h0
    rw [abs_sub_comm, zero_sub, abs_neg, abs_of_nonneg hs.1]; exact key s hs
  rcases eq_or_lt_of_le hs.1 with h0 | hs0
  · subst h0
    rw [sub_zero, abs_of_nonneg hr.1]; exact key r hr
  have hd : ∀ x ∈ Ioc (0:ℝ) 1,
      HasDerivWithinAt (P h) (-(∫ t in (0:ℝ)..x, t ^ 2 * h t) / x ^ 2) (Ioc 0 1) x :=
    fun x hx => (grp_hasDerivAt_P hc hx.1.ne').hasDerivWithinAt
  have hbound : ∀ x ∈ Ioc (0:ℝ) 1, ‖-(∫ t in (0:ℝ)..x, t ^ 2 * h t) / x ^ 2‖ ≤ B := by
    intro x hx
    have hx0 := hx.1
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < x ^ 2),
      div_le_iff₀ (by positivity)]
    calc _ ≤ B * x ^ 3 := gsf_I_bound hbd hx0
      _ ≤ B * x ^ 2 := mul_le_mul_of_nonneg_left
          (by nlinarith [mul_le_mul_of_nonneg_right hx.2 (sq_nonneg x)]) hB
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound (convex_Ioc 0 1)
    ⟨hs0, hs.2⟩ ⟨hr0, hr.2⟩
  simpa [Real.norm_eq_abs] using this

/-- Source term built from a profile `g` bounded by `M`, Lipschitz and quadratic at `0`. -/
theorem gsf_src {lam M B : ℝ} (hlam : 0 < lam) (hB : 0 ≤ B) {g : ℝ → ℝ}
    (hM : ∀ t ∈ Icc (0:ℝ) 1, g t ≤ M)
    (hlip : ∀ r ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, |g r - g s| ≤ B * |r - s|)
    (hq : ∀ r ∈ Icc (0:ℝ) 1, |g r - g 0| ≤ B * r ^ 2) :
    Continuous (fun t => lam * Real.exp (g (gsf_c t))) ∧
    (∀ t ∈ Icc (0:ℝ) 1, |lam * Real.exp (g (gsf_c t)) - lam * Real.exp (g (gsf_c 0))| ≤
      lam * Real.exp M * B * t) ∧
    (∀ t, |lam * Real.exp (g (gsf_c t))| ≤ lam * Real.exp M) := by
  have gc : ContinuousOn g (Icc 0 1) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := B.toNNReal) fun r hr s hs => ?_).continuousOn
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hB]; exact hlip r hr s hs
  refine ⟨continuous_const.mul (Real.continuous_exp.comp (gc.comp_continuous gsf_c_cont gsf_c_mem)),
    ?_, ?_⟩
  · intro t ht
    have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    rw [gsf_c_eq ht, gsf_c_eq h0, ← mul_sub, abs_mul, abs_of_pos hlam]
    have e1 := gsf_exp_lip (hM t ht) (hM 0 h0)
    have e2 := hq t ht
    have e3 : t ^ 2 ≤ t := by nlinarith [ht.1, ht.2]
    have hE := Real.exp_pos M
    calc lam * |Real.exp (g t) - Real.exp (g 0)| ≤ lam * (Real.exp M * (B * t ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hlam.le
          exact e1.trans (mul_le_mul_of_nonneg_left e2 hE.le)
      _ ≤ lam * Real.exp M * B * t := by
          have : B * t ^ 2 ≤ B * t := mul_le_mul_of_nonneg_left e3 hB
          nlinarith [mul_pos hlam hE]
  · intro t
    rw [abs_of_pos (mul_pos hlam (Real.exp_pos _))]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hM _ (gsf_c_mem t))) hlam.le

/-- A radial profile below `u` on the closed ball is below the maximum of `u` on `[0,1]`. -/
theorem gsf_le_of_ball {g : ℝ → ℝ} {u : 𝔼 → ℝ} {M : ℝ}
    (hg : ∀ x ∈ closedBall (0:𝔼) 1, g ‖x‖ ≤ u x)
    (huM : ∀ x ∈ closedBall (0:𝔼) 1, u x ≤ M) : ∀ t ∈ Icc (0:ℝ) 1, g t ≤ M := by
  intro t ht
  have hn : ‖t • (EuclideanSpace.single 0 1 : 𝔼)‖ = t := by
    have h1 : ‖(EuclideanSpace.single 0 1 : 𝔼)‖ = 1 := by simp
    rw [norm_smul, h1, mul_one, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have hmem : t • (EuclideanSpace.single 0 1 : 𝔼) ∈ closedBall (0:𝔼) 1 := by
    rw [mem_closedBall_zero_iff, hn]; exact ht.2
  have := hg _ hmem
  rw [hn] at this
  linarith [huM _ hmem]

/-- Comparison step: if `g ≤ u` then `P (λ e^{g ∘ c}) ≤ u` (maximum principle). -/
theorem gsf_compare {lam : ℝ} {u : 𝔼 → ℝ}
    (hu : ContDiffOn ℝ 2 u (ball 0 1)) (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : 𝔼, ‖x‖ = 1 → u x = 0)
    (hpde : ∀ x ∈ ball (0 : 𝔼) 1, Δ u x + lam * Real.exp (u x) = 0) (hlam : 0 ≤ lam)
    {g : ℝ → ℝ} {C : ℝ} (hcont : Continuous (fun t => lam * Real.exp (g (gsf_c t))))
    (hlip : ∀ t ∈ Icc (0:ℝ) 1,
      |lam * Real.exp (g (gsf_c t)) - lam * Real.exp (g (gsf_c 0))| ≤ C * t)
    (hle : ∀ x ∈ closedBall (0:𝔼) 1, g ‖x‖ ≤ u x) :
    ∀ x ∈ closedBall (0:𝔼) 1, P (fun t => lam * Real.exp (g (gsf_c t))) ‖x‖ ≤ u x := by
  obtain ⟨l1, l2, l3, l4⟩ := lift _ C hcont hlip
  have key := Checked.Math.GMaxPrinciple.superharmonic_nonneg
    (u - fun y => P (fun t => lam * Real.exp (g (gsf_c t))) ‖y‖) (hu.sub l1) (hc.sub l2) ?_ ?_
  · intro x hx
    have := key x hx
    simp only [Pi.sub_apply] at this
    linarith
  · intro x hx
    simp [hb x hx, l3 x hx]
  · intro x hx
    have hxb : ball (0:𝔼) 1 ∈ 𝓝 x := isOpen_ball.mem_nhds hx
    rw [(hu.contDiffAt hxb).laplacian_sub (l1.contDiffAt hxb), l4 x hx]
    have hp := hpde x hx
    have hn : ‖x‖ ∈ Icc (0:ℝ) 1 := ⟨norm_nonneg _, (mem_ball_zero_iff.1 hx).le⟩
    rw [gsf_c_eq hn]
    have h1 := hle x (ball_subset_closedBall hx)
    have h2 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hlam
    linarith

/-- The iterates are uniformly Lipschitz, quadratic at the centre, and below `u`. -/
theorem gsf_iter {lam M : ℝ} (hlam : 0 < lam) {u : 𝔼 → ℝ}
    (hu : ContDiffOn ℝ 2 u (ball 0 1)) (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : 𝔼, ‖x‖ = 1 → u x = 0)
    (hpde : ∀ x ∈ ball (0 : 𝔼) 1, Δ u x + lam * Real.exp (u x) = 0)
    (hu0 : ∀ x ∈ closedBall (0:𝔼) 1, 0 ≤ u x) (huM : ∀ x ∈ closedBall (0:𝔼) 1, u x ≤ M)
    (n : ℕ) :
    (∀ r ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1,
      |gsf_w lam n r - gsf_w lam n s| ≤ lam * Real.exp M * |r - s|) ∧
    (∀ r ∈ Icc (0:ℝ) 1, |gsf_w lam n r - gsf_w lam n 0| ≤ lam * Real.exp M * r ^ 2) ∧
    (∀ x ∈ closedBall (0:𝔼) 1, gsf_w lam n ‖x‖ ≤ u x) := by
  have hB : 0 ≤ lam * Real.exp M := (mul_pos hlam (Real.exp_pos M)).le
  induction n with
  | zero =>
    refine ⟨fun r _ s _ => ?_, fun r _ => ?_, fun x hx => ?_⟩
    · rw [gsf_w_zero, gsf_w_zero, sub_self, abs_zero]; exact mul_nonneg hB (abs_nonneg _)
    · rw [gsf_w_zero, gsf_w_zero, sub_self, abs_zero]; exact mul_nonneg hB (sq_nonneg _)
    · rw [gsf_w_zero]; exact hu0 x hx
  | succ n ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    obtain ⟨hcont, hl, hbd⟩ := gsf_src hlam hB (gsf_le_of_ball ih3 huM) ih1 ih2
    refine ⟨fun r hr s hs => ?_, fun r hr => ?_, ?_⟩
    · rw [gsf_w_succ]; exact gsf_lip hcont hbd hr hs
    · rw [gsf_w_succ]; exact gsf_quad hcont hbd hr
    · rw [gsf_w_succ]; exact gsf_compare hu hc hb hpde hlam.le hcont hl ih3

/-- The iterates increase. -/
theorem gsf_mono {lam : ℝ} (hlam : 0 < lam)
    (hcont : ∀ n, Continuous (fun t => lam * Real.exp (gsf_w lam n (gsf_c t)))) (n : ℕ) :
    ∀ r ∈ Icc (0:ℝ) 1, gsf_w lam n r ≤ gsf_w lam (n + 1) r := by
  induction n with
  | zero =>
    intro r hr
    rw [gsf_w_succ, gsf_w_zero]
    have := P_mono (h := fun _ => 0) continuous_const (hcont 0)
      (fun t _ => (mul_pos hlam (Real.exp_pos _)).le) hr
    simpa [P] using this
  | succ n ih =>
    intro r hr
    rw [gsf_w_succ lam (n + 1), gsf_w_succ lam n]
    apply P_mono (hcont n) (hcont (n + 1)) _ hr
    intro t ht
    apply mul_le_mul_of_nonneg_left _ hlam.le
    apply Real.exp_le_exp.2
    rw [gsf_c_eq ht]
    exact ih t ht

theorem gsf_int_tendsto {F : ℕ → ℝ → ℝ} {H f : ℝ → ℝ} {B : ℝ} (hf : Continuous f)
    (hF : ∀ n, Continuous (F n)) (hbd : ∀ n t, |F n t| ≤ B)
    (hlim : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (H t))) (a b : ℝ) :
    Tendsto (fun n => ∫ t in a..b, f t * F n t) atTop (𝓝 (∫ t in a..b, f t * H t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun t => |f t| * B)
  · exact Eventually.of_forall fun n => (hf.mul (hF n)).aestronglyMeasurable
  · exact Eventually.of_forall fun n => Eventually.of_forall fun t _ => by
      rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_left (hbd n t) (abs_nonneg _)
  · exact ((continuous_abs.comp hf).mul continuous_const).intervalIntegrable a b
  · exact Eventually.of_forall fun t _ => (hlim t).const_mul (f t)

theorem gsf_P_tendsto {F : ℕ → ℝ → ℝ} {H : ℝ → ℝ} {B : ℝ}
    (hF : ∀ n, Continuous (F n)) (hbd : ∀ n t, |F n t| ≤ B)
    (hlim : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (H t))) (r : ℝ) :
    Tendsto (fun n => P (F n) r) atTop (𝓝 (P H r)) := by
  unfold P
  exact ((gsf_int_tendsto (f := fun t : ℝ => t ^ 2) (continuous_pow 2) hF hbd hlim 0 r).const_mul _).add
    (gsf_int_tendsto (f := fun t : ℝ => t - t ^ 2) (continuous_id.sub (continuous_pow 2))
      hF hbd hlim r 1)

theorem bound_no_radial (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) :
    lam ≤ 3.321992119 := by
  rcases le_or_gt lam 0 with hl | hlam
  · linarith
  have hΔu : ∀ x ∈ ball (0:𝔼) 1, Δ u x ≤ 0 := fun x hx => by
    have := hpde x hx
    have := mul_pos hlam (Real.exp_pos (u x))
    linarith
  have hu0 := Checked.Math.GMaxPrinciple.superharmonic_nonneg u hu hc (fun x hx => (hb x hx).ge) hΔu
  obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_closedBall (0:𝔼) 1).exists_isMaxOn
    ⟨0, mem_closedBall_self zero_le_one⟩ hc
  have huM : ∀ x ∈ closedBall (0:𝔼) 1, u x ≤ u x₀ := fun x hx => hmax hx
  set M := u x₀ with hMdef
  set B := lam * Real.exp M with hBdef
  have hB : 0 < B := mul_pos hlam (Real.exp_pos M)
  have hit := gsf_iter hlam hu hc hb hpde hu0 huM
  have hMn : ∀ n, ∀ t ∈ Icc (0:ℝ) 1, gsf_w lam n t ≤ M := fun n => gsf_le_of_ball (hit n).2.2 huM
  have hsrc := fun n => gsf_src hlam hB.le (hMn n) (hit n).1 (hit n).2.1
  have hmono := gsf_mono hlam (fun n => (hsrc n).1)
  set W : ℝ → ℝ := fun r => ⨆ n, gsf_w lam n r with hWdef
  have hlim : ∀ r ∈ Icc (0:ℝ) 1, Tendsto (fun n => gsf_w lam n r) atTop (𝓝 (W r)) :=
    fun r hr => tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => hmono n r hr)
      ⟨M, by rintro _ ⟨n, rfl⟩; exact hMn n r hr⟩
  have h01 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hWM : ∀ r ∈ Icc (0:ℝ) 1, W r ≤ M := fun r hr =>
    le_of_tendsto' (hlim r hr) fun n => hMn n r hr
  have hWlip : ∀ r ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, |W r - W s| ≤ B * |r - s| :=
    fun r hr s hs => le_of_tendsto' (((hlim r hr).sub (hlim s hs)).abs) fun n => (hit n).1 r hr s hs
  have hWq : ∀ r ∈ Icc (0:ℝ) 1, |W r - W 0| ≤ B * r ^ 2 :=
    fun r hr => le_of_tendsto' (((hlim r hr).sub (hlim 0 h01)).abs) fun n => (hit n).2.1 r hr
  obtain ⟨hHc, hHl, -⟩ := gsf_src hlam hB.le hWM hWlip hWq
  set H : ℝ → ℝ := fun t => lam * Real.exp (W (gsf_c t)) with hHdef
  have hFlim : ∀ t, Tendsto (fun n => lam * Real.exp (gsf_w lam n (gsf_c t))) atTop (𝓝 (H t)) :=
    fun t => ((Real.continuous_exp.tendsto _).comp (hlim _ (gsf_c_mem t))).const_mul lam
  have heq : ∀ r ∈ Icc (0:ℝ) 1, W r = P H r := fun r hr => by
    have h1 : Tendsto (fun n => gsf_w lam (n + 1) r) atTop (𝓝 (W r)) :=
      (hlim r hr).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => gsf_w lam (n + 1) r) atTop (𝓝 (P H r)) := by
      simp only [gsf_w_succ]
      exact gsf_P_tendsto (F := fun n t => lam * Real.exp (gsf_w lam n (gsf_c t)))
        (fun n => (hsrc n).1) (fun n => (hsrc n).2.2) hFlim r
    exact tendsto_nhds_unique h1 h2
  obtain ⟨l1, l2, l3, l4⟩ := lift H _ hHc hHl
  apply Checked.Math.GelfandPDE.gelfand_pde_radial_bound lam (fun x => P H ‖x‖) l1 l2 l3
    ⟨P H, fun x _ => rfl⟩
  intro x hx
  have hn : ‖x‖ ∈ Icc (0:ℝ) 1 := ⟨norm_nonneg _, (mem_ball_zero_iff.1 hx).le⟩
  rw [l4 x hx]
  show -H ‖x‖ + lam * Real.exp (P H ‖x‖) = 0
  rw [← heq _ hn, hHdef]
  simp only [gsf_c_eq hn]
  ring

end Checked.Math.GSymFree
