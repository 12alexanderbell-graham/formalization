import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
/-! Townes ground state, `TStart`: the singular start of the Townes radial equation: every solution stays close to a truncated power series near the centre, by comparison and continuous induction. Promoted from `Work/Townes/TStart.lean`. -/

namespace Checked.Townes.TStart
open Set Filter Topology

/-- Comparison from the singular end: `f → 0` at `0⁺`, `|f'| ≤ B'` on `(0, t)`, `B(0) = 0`
give `|f t| ≤ B t`. -/
theorem bound_from_zero {f f' B B' : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hf0 : Tendsto f (𝓝[>] 0) (𝓝 0))
    (hfc : ContinuousOn f (Ioc 0 t))
    (hf' : ∀ x ∈ Ioo 0 t, HasDerivAt f (f' x) x)
    (hB : ∀ x, HasDerivAt B (B' x) x) (hB0 : B 0 = 0)
    (hbound : ∀ x ∈ Ioo 0 t, |f' x| ≤ B' x) : |f t| ≤ B t := by
  have key : ∀ a ∈ Ioo 0 t, |f t| ≤ |f a| + (B t - B a) := by
    intro a ha
    have hsub : Icc a t ⊆ Ioc 0 t := fun x hx => ⟨ha.1.trans_le hx.1, hx.2⟩
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := f) (a := a) (b := t)
      (f' := f') (B := fun x => |f a| + (B x - B a)) (B' := B')
      (hfc.mono hsub)
      (fun x hx => (hf' x ⟨ha.1.trans_le hx.1, hx.2⟩).hasDerivWithinAt)
      (by simp [Real.norm_eq_abs])
      (fun x => ((hB x).sub_const (B a)).const_add |f a|)
      (fun x hx => by
        rw [Real.norm_eq_abs]; exact hbound x ⟨ha.1.trans_le hx.1, hx.2⟩)
      ⟨ha.2.le, le_rfl⟩
    simpa [Real.norm_eq_abs] using this
  have hBc : Tendsto B (𝓝[>] 0) (𝓝 (B 0)) :=
    ((hB 0).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun a => |f a| + (B t - B a)) (𝓝[>] 0) (𝓝 (|0| + (B t - B 0))) :=
    ((continuous_abs.tendsto 0).comp hf0).add (tendsto_const_nhds.sub hBc)
  rw [abs_zero, hB0, sub_zero, zero_add] at hlim
  exact ge_of_tendsto hlim (by filter_upwards [Ioo_mem_nhdsGT ht] with a ha using key a ha)

theorem cube_sub_le {a b M η : ℝ} (hab : |a - b| ≤ η) (hb : |b| ≤ M) :
    |a ^ 3 - b ^ 3| ≤ 3 * (M + η) ^ 2 * |a - b| := by
  have ha : |a| ≤ M + η := by
    calc |a| = |(a - b) + b| := by rw [sub_add_cancel]
      _ ≤ |a - b| + |b| := abs_add_le _ _
      _ ≤ η + M := add_le_add hab hb
      _ = M + η := by ring
  have hb' : |b| ≤ M + η := by linarith [abs_nonneg (a - b)]
  have e : a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
  have hMη : 0 ≤ M + η := (abs_nonneg a).trans ha
  rw [e, abs_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc |a ^ 2 + a * b + b ^ 2| ≤ |a ^ 2 + a * b| + |b ^ 2| := abs_add_le _ _
    _ ≤ |a ^ 2| + |a * b| + |b ^ 2| := by gcongr; exact abs_add_le _ _
    _ = |a| ^ 2 + |a| * |b| + |b| ^ 2 := by rw [abs_pow, abs_mul, abs_pow]
    _ ≤ (M + η) ^ 2 + (M + η) * (M + η) + (M + η) ^ 2 := by gcongr
    _ = 3 * (M + η) ^ 2 := by ring

theorem g_sub_le {a b M η : ℝ} (hab : |a - b| ≤ η) (hb : |b| ≤ M) :
    |(a - a ^ 3) - (b - b ^ 3)| ≤ (1 + 3 * (M + η) ^ 2) * |a - b| := by
  have h3 := cube_sub_le hab hb
  have e : (a - a ^ 3) - (b - b ^ 3) = (a - b) - (a ^ 3 - b ^ 3) := by ring
  rw [e]
  calc |(a - b) - (a ^ 3 - b ^ 3)| ≤ |a - b| + |a ^ 3 - b ^ 3| := abs_sub _ _
    _ ≤ |a - b| + 3 * (M + η) ^ 2 * |a - b| := by linarith
    _ = (1 + 3 * (M + η) ^ 2) * |a - b| := by ring

theorem hasDerivAt_sq_half (C x : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 2 / 2 * C) (x * C) x := by
  have := ((hasDerivAt_pow 2 x).div_const 2).mul_const C
  convert this using 1
  rw [show (2 : ℕ) - 1 = 1 from rfl]
  push_cast
  ring

theorem hasDerivAt_sq_quarter (C x : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 2 / 4 * C) (x / 2 * C) x := by
  have := ((hasDerivAt_pow 2 x).div_const 4).mul_const C
  convert this using 1
  rw [show (2 : ℕ) - 1 = 1 from rfl]
  push_cast
  ring

/-- One improvement step: from `|θ − p| ≤ η` on `[0, c)` to the polynomial-in-ξ bounds on
`(0, c]`. -/
theorem core (θ φ p q w : ℝ → ℝ) {X ξ0 η R L Mp c c0 : ℝ} (hξ0X : ξ0 ≤ X)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) X, HasDerivWithinAt θ (φ ξ) (Icc 0 X) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 X) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) X, HasDerivWithinAt φ (-(1 / ξ * φ ξ) + θ ξ - θ ξ ^ 3) (Icc 0 X) ξ)
    (h0 : θ 0 = c0)
    (hp : ∀ ξ, HasDerivAt p (q ξ) ξ) (hp0 : p 0 = c0)
    (hq : ∀ ξ, HasDerivAt (fun t => t * q t) (w ξ) ξ)
    (hres : ∀ ξ ∈ Icc (0 : ℝ) ξ0, |w ξ - ξ * (p ξ - p ξ ^ 3)| ≤ ξ * R)
    (hpM : ∀ ξ ∈ Icc (0 : ℝ) ξ0, |p ξ| ≤ Mp)
    (hL : 1 + 3 * (Mp + η) ^ 2 ≤ L) (hη : 0 < η)
    (hc : c ≤ ξ0) (hb : ∀ s ∈ Ico 0 c, |θ s - p s| ≤ η) :
    ∀ t ∈ Ioc 0 c, |φ t - q t| ≤ t / 2 * (L * η + R) ∧
      |θ t - p t| ≤ t ^ 2 / 4 * (L * η + R) := by
  set C := L * η + R with hC
  intro t0 ht0
  have hcX : c ≤ X := hc.trans hξ0X
  have hX : 0 < X := ht0.1.trans_le (ht0.2.trans hcX)
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc 0 X] 0 := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hX]; exact nhdsWithin_mono _ Ioo_subset_Icc_self
  -- u = t φ − t q
  set u : ℝ → ℝ := fun t => t * φ t - t * q t with hu
  have uder : ∀ x ∈ Ioo 0 X, HasDerivAt u (x * (θ x - θ x ^ 3) - w x) x := by
    intro x hx
    have hφx := (hφ x ⟨hx.1, hx.2.le⟩).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
    have h : HasDerivAt u (1 * φ x + x * (-(1 / x * φ x) + θ x - θ x ^ 3) - w x) x :=
      ((hasDerivAt_id' x).mul hφx).sub (hq x)
    convert h using 1
    have hx0 : x ≠ 0 := hx.1.ne'
    field_simp
    ring
  have ubound : ∀ x ∈ Ioo 0 c, |x * (θ x - θ x ^ 3) - w x| ≤ x * C := by
    intro x hx
    have hxξ : x ∈ Icc (0 : ℝ) ξ0 := ⟨hx.1.le, hx.2.le.trans hc⟩
    have h1 := hb x ⟨hx.1.le, hx.2⟩
    have h2 := g_sub_le h1 (hpM x hxξ)
    have h3 := hres x hxξ
    have e : x * (θ x - θ x ^ 3) - w x =
        x * ((θ x - θ x ^ 3) - (p x - p x ^ 3)) - (w x - x * (p x - p x ^ 3)) := by ring
    have hx0 : 0 ≤ x := hx.1.le
    have h4 : |(θ x - θ x ^ 3) - (p x - p x ^ 3)| ≤ L * η := by
      calc _ ≤ (1 + 3 * (Mp + η) ^ 2) * |θ x - p x| := h2
        _ ≤ (1 + 3 * (Mp + η) ^ 2) * η := by gcongr
        _ ≤ L * η := by gcongr
    rw [e]
    calc |x * ((θ x - θ x ^ 3) - (p x - p x ^ 3)) - (w x - x * (p x - p x ^ 3))|
        ≤ |x * ((θ x - θ x ^ 3) - (p x - p x ^ 3))| + |w x - x * (p x - p x ^ 3)| :=
          abs_sub _ _
      _ = x * |(θ x - θ x ^ 3) - (p x - p x ^ 3)| + |w x - x * (p x - p x ^ 3)| := by
          rw [abs_mul, abs_of_nonneg hx0]
      _ ≤ x * (L * η) + x * R := by gcongr
      _ = x * C := by rw [hC]; ring
  have hq2c : Continuous (fun t => t * q t) :=
    continuous_iff_continuousAt.2 fun x => (hq x).continuousAt
  have u0 : Tendsto u (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t * φ t) (𝓝[>] 0) (𝓝 (0 * φ 0)) :=
      (continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
        (hφ0.tendsto.mono_left hle)
    have h2 : Tendsto (fun t : ℝ => t * q t) (𝓝[>] 0) (𝓝 (0 * q 0)) :=
      (hq2c.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have := h1.sub h2
    simpa using this
  have ucont : ContinuousOn u (Ioc 0 c) := by
    intro x hx
    have hxX : x ∈ Ioc (0 : ℝ) X := ⟨hx.1, hx.2.trans hcX⟩
    have h := ((continuous_id.continuousWithinAt).mul
      (hφ x hxX).continuousWithinAt).sub (hq2c.continuousWithinAt (s := Icc 0 X) (x := x))
    exact h.mono (fun y hy => ⟨hy.1.le, hy.2.trans hcX⟩)
  have phibd : ∀ t ∈ Ioc 0 c, |φ t - q t| ≤ t / 2 * C := by
    intro t ht
    have hub := bound_from_zero (f := u) (f' := fun x => x * (θ x - θ x ^ 3) - w x)
      (B := fun x => x ^ 2 / 2 * C) (B' := fun x => x * C) ht.1 u0
      (ucont.mono (Ioc_subset_Ioc_right ht.2))
      (fun x hx => uder x ⟨hx.1, hx.2.trans_le (ht.2.trans hcX)⟩)
      (hasDerivAt_sq_half C) (by simp)
      (fun x hx => ubound x ⟨hx.1, hx.2.trans_le ht.2⟩)
    have e : u t = t * (φ t - q t) := by simp only [hu]; ring
    rw [e, abs_mul, abs_of_pos ht.1] at hub
    refine le_of_mul_le_mul_left ?_ ht.1
    calc t * |φ t - q t| ≤ t ^ 2 / 2 * C := hub
      _ = t * (t / 2 * C) := by ring
  refine ⟨phibd t0 ht0, ?_⟩
  -- θ − p
  have f0 : Tendsto (fun x => θ x - p x) (𝓝[>] 0) (𝓝 0) := by
    have h := ((hθ 0 ⟨le_rfl, hX.le⟩).continuousWithinAt.tendsto.mono_left hle).sub
      ((hp 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    rw [h0, hp0, sub_self] at h
    exact h
  have fc : ContinuousOn (fun x => θ x - p x) (Ioc 0 t0) := by
    intro x hx
    have hxX : x ∈ Icc (0 : ℝ) X := ⟨hx.1.le, hx.2.trans (ht0.2.trans hcX)⟩
    exact (((hθ x hxX).continuousWithinAt).sub (hp x).continuousAt.continuousWithinAt).mono
      (fun y hy => ⟨hy.1.le, hy.2.trans (ht0.2.trans hcX)⟩)
  exact bound_from_zero (f := fun x => θ x - p x) (f' := fun x => φ x - q x)
    (B := fun x => x ^ 2 / 4 * C) (B' := fun x => x / 2 * C) ht0.1 f0 fc
    (fun x hx => ((hθ x ⟨hx.1.le, (hx.2.trans_le (ht0.2.trans hcX)).le⟩).hasDerivAt
      (Icc_mem_nhds hx.1 (hx.2.trans_le (ht0.2.trans hcX)))).sub (hp x))
    (hasDerivAt_sq_quarter C) (by simp)
    (fun x hx => phibd x ⟨hx.1, (hx.2.trans_le ht0.2).le⟩)

/-- The singular start: every solution stays near the reference on `[0, ξ0]`. -/
theorem start (θ φ p q w : ℝ → ℝ) {X ξ0 η R L Mp c0 : ℝ} (hξ0 : 0 < ξ0) (hξ0X : ξ0 ≤ X)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) X, HasDerivWithinAt θ (φ ξ) (Icc 0 X) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 X) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) X, HasDerivWithinAt φ (-(1 / ξ * φ ξ) + θ ξ - θ ξ ^ 3) (Icc 0 X) ξ)
    (h0 : θ 0 = c0)
    (hp : ∀ ξ, HasDerivAt p (q ξ) ξ) (hp0 : p 0 = c0)
    (hq : ∀ ξ, HasDerivAt (fun t => t * q t) (w ξ) ξ)
    (hres : ∀ ξ ∈ Icc (0 : ℝ) ξ0, |w ξ - ξ * (p ξ - p ξ ^ 3)| ≤ ξ * R)
    (hpM : ∀ ξ ∈ Icc (0 : ℝ) ξ0, |p ξ| ≤ Mp)
    (hL : 1 + 3 * (Mp + η) ^ 2 ≤ L) (hη : 0 < η) (hR : 0 ≤ R)
    (hcontr : ξ0 ^ 2 / 4 * (L * η + R) < η) :
    ∀ ξ ∈ Icc (0 : ℝ) ξ0, |θ ξ - p ξ| ≤ ξ0 ^ 2 / 4 * (L * η + R) ∧
      |φ ξ - q ξ| ≤ ξ / 2 * (L * η + R) := by
  set C := L * η + R with hC
  have hX : 0 < X := hξ0.trans_le hξ0X
  have hL0 : 0 ≤ L := (by positivity : (0 : ℝ) ≤ 1 + 3 * (Mp + η) ^ 2).trans hL
  have hC0 : 0 ≤ C := by rw [hC]; have := hη.le; positivity
  have cr : ∀ c, c ≤ ξ0 → (∀ s ∈ Ico 0 c, |θ s - p s| ≤ η) →
      ∀ t ∈ Ioc 0 c, |φ t - q t| ≤ t / 2 * C ∧ |θ t - p t| ≤ t ^ 2 / 4 * C :=
    fun c hc hb => core θ φ p q w (c := c) hξ0X hθ hφ0 hφ h0 hp hp0 hq hres hpM hL hη hc hb
  -- continuous induction on c ∈ [0, ξ0] for |θ − p| ≤ η on [0, c)
  set S : Set ℝ := {c | c ∈ Icc 0 ξ0 ∧ ∀ s ∈ Ico 0 c, |θ s - p s| ≤ η} with hS
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hξ0.le⟩, fun s hs => absurd hs.2 (not_lt.2 hs.1)⟩
  have hbdd : BddAbove S := ⟨ξ0, fun c hc => hc.1.2⟩
  set T := sSup S with hT
  have hT0 : 0 ≤ T := le_csSup hbdd h0S
  have hTξ : T ≤ ξ0 := csSup_le ⟨0, h0S⟩ fun c hc => hc.1.2
  have hTS : ∀ s ∈ Ico 0 T, |θ s - p s| ≤ η := by
    intro s hs
    obtain ⟨c, hcS, hsc⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩ hs.2
    exact hcS.2 s ⟨hs.1, hsc⟩
  -- strict bound on [0, T]
  have hstrict : ∀ s ∈ Icc 0 T, |θ s - p s| < η := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, h0, hp0, sub_self, abs_zero]; exact hη
    · have := (cr T hTξ hTS s ⟨h, hs.2⟩).2
      have hs2 : s ^ 2 ≤ ξ0 ^ 2 := by gcongr; exact hs.2.trans hTξ
      calc |θ s - p s| ≤ s ^ 2 / 4 * C := this
        _ ≤ ξ0 ^ 2 / 4 * C := by gcongr
        _ < η := hcontr
  have hTeq : T = ξ0 := by
    by_contra hne
    have hTlt : T < ξ0 := lt_of_le_of_ne hTξ hne
    have hTX : T ∈ Icc (0 : ℝ) X := ⟨hT0, hTξ.trans hξ0X⟩
    have hcont : ContinuousWithinAt (fun s => θ s - p s) (Icc 0 X) T :=
      (hθ T hTX).continuousWithinAt.sub (hp T).continuousAt.continuousWithinAt
    have hgap : 0 < η - |θ T - p T| := by linarith [hstrict T ⟨hT0, le_rfl⟩]
    obtain ⟨δ, hδ, hδb⟩ := Metric.continuousWithinAt_iff.1 hcont _ hgap
    set c := min (T + δ / 2) ξ0 with hc
    have hTc : T < c := lt_min (by linarith) hTlt
    have hcS : c ∈ S := by
      refine ⟨⟨by linarith, min_le_right _ _⟩, fun s hs => ?_⟩
      rcases le_or_gt s T with hsT | hsT
      · exact (hstrict s ⟨hs.1, hsT⟩).le
      · have hsX : s ∈ Icc (0 : ℝ) X :=
          ⟨hs.1, (hs.2.le.trans (min_le_right _ _)).trans hξ0X⟩
        have hd : dist s T < δ := by
          rw [Real.dist_eq, abs_of_nonneg (by linarith)]
          linarith [hs.2.trans_le (min_le_left (T + δ / 2) ξ0)]
        have h1 := hδb hsX hd
        rw [Real.dist_eq] at h1
        have := abs_sub_abs_le_abs_sub (θ s - p s) (θ T - p T)
        linarith
    have := le_csSup hbdd hcS
    linarith
  have hfin : ∀ s ∈ Ico 0 ξ0, |θ s - p s| ≤ η := by rw [← hTeq]; exact hTS
  have cr' := cr ξ0 le_rfl hfin
  -- φ 0 = q 0 from the derivative of θ − p at 0
  have hφq0 : φ 0 - q 0 = 0 := by
    have hd : HasDerivWithinAt (fun x => θ x - p x) (φ 0 - q 0) (Ioi 0) 0 :=
      ((hθ 0 ⟨le_rfl, hX.le⟩).mono_of_mem_nhdsWithin
        (mem_of_superset (Ioo_mem_nhdsGT hX) Ioo_subset_Icc_self)).sub (hp 0).hasDerivWithinAt
    have hs := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).1 hd
    have hz : Tendsto (slope (fun x => θ x - p x) 0) (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun t => t / 4 * C) ?_ ?_
      · filter_upwards [Ioo_mem_nhdsGT hξ0] with t ht
        rw [slope_def_field, h0, hp0, sub_self, sub_zero, sub_zero, Real.norm_eq_abs, abs_div,
          abs_of_pos ht.1]
        have hb := (cr' t ⟨ht.1, ht.2.le⟩).2
        rw [div_le_iff₀ ht.1]
        calc |θ t - p t| ≤ t ^ 2 / 4 * C := hb
          _ = t / 4 * C * t := by ring
      · have : Tendsto (fun t : ℝ => t / 4 * C) (𝓝 0) (𝓝 (0 / 4 * C)) :=
          ((continuous_id.div_const 4).mul_const C).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique hs hz
  intro ξ hξ
  rcases eq_or_lt_of_le hξ.1 with h | h
  · rw [← h, h0, hp0, sub_self, abs_zero, hφq0, abs_zero]
    exact ⟨by positivity, by simp⟩
  · have := cr' ξ ⟨h, hξ.2⟩
    refine ⟨this.2.trans ?_, this.1⟩
    have : ξ ^ 2 ≤ ξ0 ^ 2 := by gcongr; exact hξ.2
    gcongr

end Checked.Townes.TStart
