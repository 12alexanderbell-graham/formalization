import Checked.FalknerSkan.BoundedTools
import Checked.FalknerSkan.LimitCore
import Checked.FalknerSkan.FSScale
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Stagnation-point and Falkner–Skan equations written as a first-order system with a positive coefficient of the product term: every solution on the closed half-line that starts at zero with velocity profile zero and whose velocity profile is bounded by one in absolute value has velocity profile tending to one, so the far-field condition of the bounded-class boundary-value problems follows from the bound. Module `BoundedLimit`, written in run 2026-11-11T2028Z (scratch `runs/2026-11-11T2028Z/lean/BoundedLimit.lean`). -/

namespace Checked.FalknerSkan.BoundedLimit
open Set Filter Topology Checked.FalknerSkan.BoundedTools

/-- Fencing from a start point: if q has a right derivative on [0, ∞) that is negative at every zero of
q to the right of η₀, then q ≤ 0 at η₀ gives q ≤ 0 on [η₀, ∞). -/
theorem stays_nonpos_from {q q' : ℝ → ℝ}
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (q' η) (Ici 0) η)
    {η₀ : ℝ} (h0 : 0 ≤ η₀) (hz : ∀ η, η₀ ≤ η → q η = 0 → q' η < 0)
    (hle : q η₀ ≤ 0) : ∀ η, η₀ ≤ η → q η ≤ 0 := by
  intro η hη
  have hcont : ContinuousOn q (Icc η₀ η) := fun x hx =>
    ((hq x (h0.trans hx.1)).continuousWithinAt).mono (fun y hy => h0.trans hy.1)
  have hder : ∀ x ∈ Ico η₀ η, HasDerivWithinAt q (q' x) (Ici x) x := fun x hx =>
    (hq x (h0.trans hx.1)).mono (fun y hy => h0.trans (hx.1.trans hy))
  have := image_le_of_deriv_right_lt_deriv_boundary' (B := fun _ => (0 : ℝ))
    (B' := fun _ => (0 : ℝ)) hcont hder hle continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _)
    (fun x hx hqx => hz x hx.1 hqx)
  exact this ⟨hη, le_rfl⟩

/-- Monotonicity on [0, ∞) from a nonnegative right derivative. -/
theorem mono_le {g g' : ℝ → ℝ} (hg : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt g (g' η) (Ici 0) η)
    {a : ℝ} (ha : 0 ≤ a) (h : ∀ x, a ≤ x → 0 ≤ g' x) {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) :
    g x ≤ g y := by
  have := le_start (p := fun t => -g t) (q := fun t => -g' t) (fun η hη => (hg η hη).neg)
    (ha.trans hx) (fun η hη => by simpa using h η (hx.trans hη)) y hxy
  simpa using this

/-- Antitonicity on [a, ∞) from a nonpositive right derivative. -/
theorem anti_le {g g' : ℝ → ℝ} (hg : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt g (g' η) (Ici 0) η)
    {a : ℝ} (ha : 0 ≤ a) (h : ∀ x, a ≤ x → g' x ≤ 0) {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) :
    g y ≤ g x :=
  le_start hg (ha.trans hx) (fun η hη => h η (hx.trans hη)) y hxy

/-- Case q > 0 on [0, ∞): p → 1. -/
theorem tendsto_of_pos {k : ℝ} (hk : 0 ≤ k) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hle : ∀ η ∈ Ici (0 : ℝ), p η ≤ 1)
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η) : Tendsto p atTop (𝓝 1) := by
  have hpn : ∀ η, 0 ≤ η → 0 ≤ p η := fun η hη => by
    have := mono_le hp le_rfl (fun x hx => (hpos x hx).le) le_rfl hη
    rwa [hp0] at this
  have hfn : ∀ η, 0 ≤ η → 0 ≤ f η := fun η hη => by
    have := mono_le hf le_rfl (fun x hx => hpn x hx) le_rfl hη
    rwa [hf0] at this
  -- for every e ∈ (0, 1] some value of p exceeds 1 − e
  have hex : ∀ e, 0 < e → e ≤ 1 → ∃ N, 0 ≤ N ∧ 1 - e < p N := by
    intro e he he1
    by_contra H
    push Not at H
    set c := 1 - (1 - e) ^ 2 with hc
    have hcpos : 0 < c := by rw [hc]; nlinarith
    have hG : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => q t + c * t)
        ((-(k * f η * q η) - 1 + p η ^ 2) + c * 1) (Ici 0) η :=
      fun η hη => (hq η hη).add ((hasDerivWithinAt_id η _).const_mul c)
    have hd : ∀ x, 0 ≤ x → (-(k * f x * q x) - 1 + p x ^ 2) + c * 1 ≤ 0 := by
      intro x hx
      have h1 : 0 ≤ k * f x * q x := mul_nonneg (mul_nonneg hk (hfn x hx)) (hpos x hx).le
      have h2 : p x ^ 2 ≤ (1 - e) ^ 2 := by
        have := H x hx
        have := hpn x hx
        nlinarith
      rw [hc]; linarith
    set η₁ := q 0 / c + 1 with hη₁
    have hη₁0 : 0 ≤ η₁ := by
      rw [hη₁]; have := (hpos 0 (by simp)).le; positivity
    have := anti_le hG le_rfl hd le_rfl hη₁0
    simp only [mul_zero, add_zero] at this
    have hqη := hpos η₁ hη₁0
    have : c * η₁ = q 0 + c := by rw [hη₁]; field_simp
    linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN0, hN⟩ := hex (min ε 1) (lt_min hε one_pos) (min_le_right _ _)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : p N ≤ p n := mono_le hp le_rfl (fun x hx => (hpos x hx).le) hN0 hn
  have h2 : p n ≤ 1 := hle n (hN0.trans hn)
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  have := min_le_left ε 1
  linarith

/-- Case q(η') ≤ 0 somewhere: impossible under −1 ≤ p ≤ 1. -/
theorem false_of_nonpos {k : ℝ} (hk : 0 < k) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1)
    {η' : ℝ} (hη' : 0 ≤ η') (hq' : q η' ≤ 0) : False := by
  have hlt := abs_lt_of_abs_le hf hp hq hp0 hb
  have hz : ∀ η ∈ Ici (0 : ℝ), q η = 0 → -(k * f η * q η) - 1 + p η ^ 2 < 0 := by
    intro η hη h0
    rw [h0]; have := hlt η hη; nlinarith
  have hqn : ∀ η, η' ≤ η → q η ≤ 0 := stays_nonpos hq hz hη' hq'
  -- a point T ≥ η' with q T < 0
  obtain ⟨T, hT, hqT⟩ : ∃ T, η' ≤ T ∧ q T < 0 := by
    by_contra H
    push Not at H
    have h0 : q η' = 0 := le_antisymm hq' (H η' le_rfl)
    have hd := Checked.FalknerSkan.LimitCore.right_nonneg
      ((hq η' hη').mono (Ici_subset_Ici.2 hη'))
      (eventually_nhdsWithin_of_forall (fun y hy => by
        rw [h0]; exact H y (le_of_lt hy)))
    exact absurd hd (not_le.2 (hz η' hη' h0))
  have hT0 : 0 ≤ T := hη'.trans hT
  have hpanti : ∀ x y, T ≤ x → x ≤ y → p y ≤ p x := fun x y hx hxy =>
    anti_le hp hη' (fun t ht => hqn t ht) (hT.trans hx) hxy
  by_cases hneg : ∃ T₁, T ≤ T₁ ∧ p T₁ < 0
  · -- (2a) f ≤ −1 far out, so q' < 0 there
    obtain ⟨T₁, hT₁, hpT₁⟩ := hneg
    have hT₁0 : 0 ≤ T₁ := hT0.trans hT₁
    have hF : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => f t - p T₁ * t) (p η - p T₁ * 1)
        (Ici 0) η := fun η hη => (hf η hη).sub ((hasDerivWithinAt_id η _).const_mul (p T₁))
    have hfb : ∀ η, T₁ ≤ η → f η - p T₁ * η ≤ f T₁ - p T₁ * T₁ := fun η hη =>
      anti_le hF hT₁0 (fun x hx => by have := hpanti T₁ x hT₁ hx; linarith) le_rfl hη
    set T₂ := T₁ + (|f T₁| + 1) / (-p T₁) with hT₂
    have hT₁₂ : T₁ ≤ T₂ := by
      rw [hT₂]; have : 0 < (|f T₁| + 1) / (-p T₁) := by
        apply div_pos (by positivity) (by linarith)
      linarith
    have hfneg : ∀ η, T₂ ≤ η → f η ≤ -1 := by
      intro η hη
      have h1 := hfb η (hT₁₂.trans hη)
      have h2 : p T₁ * (η - T₁) ≤ p T₁ * (T₂ - T₁) :=
        mul_le_mul_of_nonpos_left (by linarith) hpT₁.le
      have h3 : p T₁ * (T₂ - T₁) = -(|f T₁| + 1) := by
        rw [hT₂, add_sub_cancel_left, mul_div_assoc', div_eq_iff (by linarith)]; ring
      have h4 := le_abs_self (f T₁)
      nlinarith
    have hT₂0 : 0 ≤ T₂ := hT₁0.trans hT₁₂
    have hqd : ∀ x, T₂ ≤ x → -(k * f x * q x) - 1 + p x ^ 2 < 0 := by
      intro x hx
      have hfx := hfneg x hx
      have hqx := hqn x (hT.trans (hT₁.trans (hT₁₂.trans hx)))
      have h1 : 0 ≤ k * f x * q x := by
        have : 0 ≤ f x * q x := mul_nonneg_of_nonpos_of_nonpos (by linarith) hqx
        nlinarith
      have := hlt x (hT₂0.trans hx)
      nlinarith
    have hsa := Checked.FalknerSkan.LimitCore.santi hq hT₂0 (a := T₂) (b := T₂ + 1)
      (fun x hx => hqd x hx.1.le)
    have hm : q (T₂ + 1) < q T₂ := hsa ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    set m := q (T₂ + 1) with hmdef
    have hqT₂ : q T₂ ≤ 0 := hqn T₂ (hT.trans (hT₁.trans hT₁₂))
    have hmneg : m < 0 := by linarith
    have hqle : ∀ x, T₂ + 1 ≤ x → q x ≤ m := fun x hx =>
      anti_le hq hT₂0 (fun t ht => (hqd t ht).le) (by linarith) hx
    have hP : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => p t - m * t) (q η - m * 1) (Ici 0) η :=
      fun η hη => (hp η hη).sub ((hasDerivWithinAt_id η _).const_mul m)
    set η₃ := T₂ + 1 + 3 / (-m) with hη₃
    have hη₃' : T₂ + 1 ≤ η₃ := by
      rw [hη₃]; have : 0 < 3 / (-m) := div_pos (by norm_num) (by linarith)
      linarith
    have h1 := anti_le hP (by linarith) (fun x hx => by have := hqle x hx; linarith) le_rfl hη₃'
    have h2 : m * (η₃ - (T₂ + 1)) = -3 := by
      rw [hη₃, add_sub_cancel_left, mul_div_assoc', div_eq_iff (by linarith)]; ring
    have h3 := (hlt (T₂ + 1) (by simp; linarith)).2
    have h4 := (hlt η₃ (by simp; linarith)).1
    nlinarith
  · -- (2b) 0 ≤ p ≤ p T < 1 after T
    push Not at hneg
    have hpT := (hlt T hT0).2
    set c := 1 - p T ^ 2 with hc
    have hcpos : 0 < c := by
      rw [hc]; have := hneg T le_rfl; nlinarith
    have hfle : ∀ η, 0 ≤ η → f η ≤ η := by
      intro η hη
      have hF : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => f t - t) (p x - 1) (Ici 0) x :=
        fun x hx => (hf x hx).sub (hasDerivWithinAt_id x _)
      have := anti_le hF le_rfl (fun x hx => by linarith [(hb x hx).2]) le_rfl hη
      simp only [hf0, sub_zero] at this
      linarith
    set B := c / (-2 * q T) + 1 with hB
    have hBpos : 0 < B := by
      rw [hB]; have : 0 < c / (-2 * q T) := div_pos hcpos (by linarith)
      linarith
    have hden : ∀ η, 0 ≤ η → 0 < k * η + B := fun η hη => by positivity
    -- z = q + c / (2 (k η + B))
    have hzd : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => q t + c / 2 * (k * t + B)⁻¹)
        ((-(k * f η * q η) - 1 + p η ^ 2) + c / 2 * (-(k * 1) / (k * η + B) ^ 2)) (Ici 0) η := by
      intro η hη
      have h1 : HasDerivAt (fun t => k * t + B) (k * 1) η :=
        ((hasDerivAt_id η).const_mul k).add_const B
      exact (hq η hη).add (((h1.inv (hden η hη).ne').const_mul (c / 2)).hasDerivWithinAt)
    have hzneg : ∀ η, T ≤ η → q η + c / 2 * (k * η + B)⁻¹ ≤ 0 := by
      refine stays_nonpos_from hzd hT0 ?_ ?_
      · intro η hη hz0
        have hη0 : 0 ≤ η := hT0.trans hη
        have hD := hden η hη0
        have hqeq : q η = -(c / 2 * (k * η + B)⁻¹) := by linarith
        have hp1 : p η ^ 2 ≤ p T ^ 2 := by
          have := hpanti T η le_rfl hη; have := hneg η hη; nlinarith
        have hfq : -(k * f η * q η) ≤ c / 2 * (k * η) * (k * η + B)⁻¹ := by
          rw [hqeq]
          have hinv : 0 < (k * η + B)⁻¹ := inv_pos.2 hD
          have := hfle η hη0
          have : k * f η ≤ k * η := mul_le_mul_of_nonneg_left this hk.le
          have hcp : 0 ≤ c / 2 * (k * η + B)⁻¹ := by positivity
          nlinarith
        have hfrac : c / 2 * (k * η) * (k * η + B)⁻¹ < c / 2 := by
          have hlt1 : k * η / (k * η + B) < 1 := (div_lt_one hD).2 (by linarith)
          calc c / 2 * (k * η) * (k * η + B)⁻¹ = c / 2 * (k * η / (k * η + B)) := by ring
            _ < c / 2 * 1 := mul_lt_mul_of_pos_left hlt1 (by positivity)
            _ = c / 2 := mul_one _
        have hg' : c / 2 * (-(k * 1) / (k * η + B) ^ 2) < 0 := by
          have : 0 < k * 1 / (k * η + B) ^ 2 := by positivity
          have : -(k * 1) / (k * η + B) ^ 2 = -(k * 1 / (k * η + B) ^ 2) := by ring
          rw [this]; nlinarith
        rw [hc] at hfrac hg' ⊢
        nlinarith
      · have hD := hden T hT0
        have hkT : 0 ≤ k * T := by positivity
        have hB1 : c / (-2 * q T) < k * T + B := by rw [hB]; linarith
        have hB2 : c < (k * T + B) * (-2 * q T) := (div_lt_iff₀ (by linarith)).1 hB1
        have : c / 2 * (k * T + B)⁻¹ ≤ -q T := by
          have e : c / 2 * (k * T + B)⁻¹ = c / (2 * (k * T + B)) := by
            rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_assoc]
          rw [e, div_le_iff₀ (by positivity)]
          nlinarith
        linarith
    -- G = p + (c / (2k)) log (k η + B) decreases after T
    have hGd : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => p t + c / (2 * k) * Real.log (k * t + B))
        (q η + c / (2 * k) * ((k * 1) / (k * η + B))) (Ici 0) η := by
      intro η hη
      have h1 : HasDerivAt (fun t => k * t + B) (k * 1) η :=
        ((hasDerivAt_id η).const_mul k).add_const B
      exact (hp η hη).add (((h1.log (hden η hη).ne').const_mul (c / (2 * k))).hasDerivWithinAt)
    have hGle : ∀ η, T ≤ η → p η + c / (2 * k) * Real.log (k * η + B) ≤
        p T + c / (2 * k) * Real.log (k * T + B) := fun η hη =>
      anti_le hGd hT0 (fun x hx => by
        have := hzneg x hx
        have hD := hden x (hT0.trans hx)
        have : c / (2 * k) * (k * 1 / (k * x + B)) = c / 2 * (k * x + B)⁻¹ := by
          have hk0 : k ≠ 0 := hk.ne'
          have hX : k * x + B ≠ 0 := hD.ne'
          field_simp
        linarith) le_rfl hη
    set G := p T + c / (2 * k) * Real.log (k * T + B) with hGdef
    set M := 2 * k / c * (G + 1) with hM
    set η₄ := T + Real.exp M / k with hη₄
    have hη₄T : T ≤ η₄ := by
      rw [hη₄]; have : 0 < Real.exp M / k := by positivity
      linarith
    have hlog : M < Real.log (k * η₄ + B) := by
      rw [Real.lt_log_iff_exp_lt (hden η₄ (hT0.trans hη₄T))]
      have : k * η₄ = k * T + Real.exp M := by
        rw [hη₄, mul_add, mul_div_cancel₀ _ hk.ne']
      have : 0 ≤ k * T := by positivity
      linarith
    have h1 := hGle η₄ hη₄T
    have h2 : c / (2 * k) * M = G + 1 := by
      have e : c / (2 * k) * (2 * k / c) = 1 := by
        rw [div_mul_div_comm, mul_comm c, div_self]; positivity
      rw [hM, ← mul_assoc, e, one_mul]
    have h3 : c / (2 * k) * M < c / (2 * k) * Real.log (k * η₄ + B) :=
      mul_lt_mul_of_pos_left hlog (by positivity)
    have h4 := hneg η₄ hη₄T
    linarith

/-- For k > 0: every solution of f' = p, p' = q, q' = −k f q − 1 + p² on [0, ∞) with f(0) = 0,
p(0) = 0 and −1 ≤ p ≤ 1 on [0, ∞) has p(η) → 1 as η → ∞. -/
theorem tendsto_of_bounded {k : ℝ} (hk : 0 < k) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) :
    Tendsto p atTop (𝓝 1) := by
  by_cases hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η
  · exact tendsto_of_pos hk.le hf hp hq hf0 hp0 (fun η hη => (hb η hη).2) hpos
  · push Not at hpos
    obtain ⟨η', hη', hq'⟩ := hpos
    exact (false_of_nonpos hk hf hp hq hf0 hp0 hb hη' hq').elim

/-- Falkner–Skan form, β > 0: every solution of f' = p, p' = q, q' = −f q − β (1 − p²) on [0, ∞) with
f(0) = 0, p(0) = 0 and −1 ≤ p ≤ 1 on [0, ∞) has p(η) → 1 as η → ∞ (rescale by √β to the form above). -/
theorem tendsto_of_bounded_beta {β : ℝ} (hβ : 0 < β) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) :
    Tendsto p atTop (𝓝 1) := by
  have hc : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hc2 : Real.sqrt β ^ 2 = β := Real.sq_sqrt hβ.le
  have hq1 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(1 * f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc hf hp hq1
  have C' : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => q (s / Real.sqrt β) / Real.sqrt β)
      (-(1 / β * (Real.sqrt β * f (s / Real.sqrt β)) * (q (s / Real.sqrt β) / Real.sqrt β)) - 1 +
        p (s / Real.sqrt β) ^ 2) (Ici 0) s := by
    intro s hs
    refine (C s hs).congr_deriv ?_
    rw [hc2]; field_simp; ring
  have hP := tendsto_of_bounded (one_div_pos.2 hβ) A B C' (by simp [hf0]) (by simp [hp0])
    (fun s hs => hb (s / Real.sqrt β) (div_nonneg (mem_Ici.1 hs) hc.le))
  refine (hP.comp (tendsto_id.atTop_mul_const hc)).congr (fun η => ?_)
  simp only [Function.comp_apply, id, mul_div_assoc, div_self hc.ne', mul_one]

end Checked.FalknerSkan.BoundedLimit
