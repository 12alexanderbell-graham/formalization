import Checked.FalknerSkan.LimitCore
/-! Scratch (run 2026-11-09T0828Z, fork B): Lemma R of the β < 0 research note (Riccati
upgrade) for f' = p, p' = q, q' = −K f q + 1 − p²: q ≥ μ(1 − p) on [a, ∞) and f → ∞ give
q ≥ M(1 − p) eventually, for every M. -/

namespace Scratch0828.Riccati
open Set Filter Topology Checked.FalknerSkan.LimitCore

/-- Monotonicity on [a, b] from interior derivatives and continuity. -/
theorem monoOn_of {g g' : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (h : ∀ x ∈ Ioo a b, 0 ≤ g' x) :
    MonotoneOn g (Icc a b) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hc
    (fun x hx => by rw [interior_Icc] at hx; exact (hd x hx).hasDerivWithinAt)
    (fun x hx => h x (by rwa [interior_Icc] at hx))

theorem no_touch_from_above {g : ℝ → ℝ} {d x a : ℝ} (hax : a < x) (h : HasDerivAt g d x)
    (hd : 0 < d) (h0 : g x = 0) (hpos : ∀ s ∈ Ioo a x, 0 < g s) : False := by
  have h1 := left_neg h hd h0
  have h2 : ∀ᶠ s in 𝓝[<] x, 0 < g s := by
    filter_upwards [Ioo_mem_nhdsLT hax] with s hs using hpos s hs
  obtain ⟨s, hs1, hs2⟩ := (h1.and h2).exists
  linarith

/-- First touch: a function positive at η₁ whose derivative is positive at each of its
zeros after η₁ stays positive. -/
theorem stay_pos {g g' : ℝ → ℝ} {η₁ : ℝ} (hd : ∀ x, η₁ < x → HasDerivAt g (g' x) x)
    (hc : ∀ T, ContinuousOn g (Icc η₁ T)) (h0 : 0 < g η₁)
    (hz : ∀ x, η₁ < x → g x = 0 → 0 < g' x) : ∀ x, η₁ ≤ x → 0 < g x := by
  intro T hT
  by_contra hneg
  push Not at hneg
  set S : Set ℝ := Icc η₁ T ∩ g ⁻¹' Iic 0 with hS
  have hSc : IsClosed S := (hc T).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hne : S.Nonempty := ⟨T, ⟨hT, le_rfl⟩, hneg⟩
  have hbdd : BddBelow S := ⟨η₁, fun s hs => hs.1.1⟩
  have hτS : sInf S ∈ S := hSc.csInf_mem hne hbdd
  set τ := sInf S
  have hτ1 : η₁ < τ := lt_of_le_of_ne hτS.1.1 (fun he => by
    have := hτS.2; rw [← he] at this; simp only [mem_preimage, mem_Iic] at this; linarith)
  have good : ∀ s ∈ Ioo η₁ τ, 0 < g s := by
    intro s hs
    have hsS : s ∉ S := notMem_of_lt_csInf hs.2 hbdd
    by_contra h'
    exact hsS ⟨⟨hs.1.le, hs.2.le.trans hτS.1.2⟩, not_lt.1 h'⟩
  have hA := hd τ hτ1
  have hge : 0 ≤ g τ := ge_of_tendsto (hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (by filter_upwards [Ioo_mem_nhdsLT hτ1] with s hs using (good s hs).le)
  have hle : g τ ≤ 0 := hτS.2
  have heq : g τ = 0 := le_antisymm hle hge
  exact no_touch_from_above hτ1 hA (hz τ hτ1 heq) heq good

/-- **Lemma R** (Riccati upgrade). -/
theorem riccati_up {K μ : ℝ} (hK : 0 < K) (hμ : 0 < μ) {f p q : ℝ → ℝ}
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) + 1 - p η ^ 2) (Ici 0) η)
    {a : ℝ} (ha : 0 ≤ a) (hp1 : ∀ η ∈ Ici a, p η < 1)
    (hflim : Tendsto f atTop atTop) (hlow : ∀ η ∈ Ici a, μ * (1 - p η) ≤ q η) :
    ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η := by
  intro M
  set M' := max M μ with hM'
  have hM'μ : μ ≤ M' := le_max_right _ _
  have hM'0 : 0 < M' := lt_of_lt_of_le hμ hM'μ
  obtain ⟨a₁, ha₁⟩ := eventually_atTop.1 (hflim.eventually_ge_atTop ((M' + 3 / μ) / K))
  set a₂ := max a₁ (a + 1) with ha₂
  have ha₂a : a < a₂ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hKf : ∀ η, a₂ ≤ η → M' + 3 / μ ≤ K * f η := by
    intro η hη
    have := ha₁ η ((le_max_left _ _).trans hη)
    have := mul_le_mul_of_nonneg_left this hK.le
    rwa [mul_div_cancel₀ _ hK.ne'] at this
  have claim : ∀ η₁, a₂ ≤ η₁ → M' * (1 - p η₁) ≤ q η₁ := by
    intro η₁ hη₁
    by_contra hcon
    push Not at hcon
    have hη₁a : a < η₁ := lt_of_lt_of_le ha₂a hη₁
    have hη₁0 : 0 < η₁ := lt_of_le_of_lt ha hη₁a
    -- Step 1: q < M'(1 − p) on [η₁, ∞)
    have step1 : ∀ x, η₁ ≤ x → 0 < M' * (1 - p x) - q x := by
      refine stay_pos (g := fun s => M' * (1 - p s) - q s)
        (g' := fun s => M' * (-q s) - (-(K * f s * q s) + 1 - p s ^ 2)) ?_ ?_ (by linarith) ?_
      · intro x hx
        have hx0 : 0 < x := hη₁0.trans hx
        exact (((at_of hp hx0).const_sub 1).const_mul M').sub (at_of hq hx0)
      · intro T
        exact (continuousOn_const.mul (continuousOn_const.sub
          (cont_of hp (a := η₁) (b := T) hη₁0.le))).sub (cont_of hq hη₁0.le)
      · intro x hx hz
        have hg : 0 < 1 - p x := by have := hp1 x (hη₁a.trans hx).le; linarith
        have hz' : M' * (1 - p x) - q x = 0 := hz
        have hqx : q x = M' * (1 - p x) := by linarith
        have hk := hKf x (hη₁.trans hx.le)
        have hk2 : M' * (M' + 3 / μ) ≤ M' * (K * f x) := mul_le_mul_of_nonneg_left hk hM'0.le
        have h3 : 3 ≤ M' * (3 / μ) := by
          rw [mul_div_assoc', le_div_iff₀ hμ]; nlinarith
        have e : M' * (-q x) - (-(K * f x * q x) + 1 - p x ^ 2) =
            (1 - p x) * (M' * (K * f x) - M' * M' - 2 + (1 - p x)) := by rw [hqx]; ring
        show 0 < M' * (-q x) - (-(K * f x * q x) + 1 - p x ^ 2)
        rw [e]
        apply mul_pos hg
        nlinarith
    -- Step 2: r = q/(1 − p) decreases at rate ≥ 1 on [η₁, ∞)
    set r : ℝ → ℝ := fun s => q s / (1 - p s) with hr
    have hgpos : ∀ x, a < x → 0 < 1 - p x := fun x hx => by
      have := hp1 x hx.le; linarith
    have hrμ : ∀ x, a < x → μ ≤ r x := fun x hx => by
      simp only [hr]; rw [le_div_iff₀ (hgpos x hx)]; exact hlow x hx.le
    set x := η₁ + M' + 1 with hx
    have hx1 : η₁ ≤ x := by linarith
    have hm := monoOn_of (g := fun s => -(r s) - s)
      (g' := fun s => -(((-(K * f s * q s) + 1 - p s ^ 2) * (1 - p s) - q s * (-q s)) /
        (1 - p s) ^ 2) - 1) (a := η₁) (b := x)
      ((((cont_of hq (a := η₁) (b := x) hη₁0.le).div (continuousOn_const.sub
        (cont_of hp (a := η₁) (b := x) hη₁0.le)) (fun z hz =>
          (hgpos z (hη₁a.trans_le hz.1)).ne')).neg).sub continuousOn_id)
      (fun z hz => by
        have hz0 : 0 < z := hη₁0.trans hz.1
        exact (((at_of hq hz0).div ((at_of hp hz0).const_sub 1)
          (hgpos z (hη₁a.trans hz.1)).ne').neg.sub (hasDerivAt_id z)))
      (fun z hz => by
        have hza : a < z := hη₁a.trans hz.1
        have hg := hgpos z hza
        set g := 1 - p z with hgdef
        have hpz : p z = 1 - g := by linarith
        set ρ := r z with hρ
        have hqz : q z = ρ * g := by
          show q z = q z / (1 - p z) * (1 - p z); rw [div_mul_cancel₀ _ (ne_of_gt hg)]
        have hρμ : μ ≤ ρ := hrμ z hza
        have hρM : ρ < M' := by
          have := step1 z hz.1.le
          simp only [hρ, hr]; rw [div_lt_iff₀ hg]; linarith
        have hk := hKf z (hη₁.trans hz.1.le)
        have hE : ((-(K * f z * q z) + 1 - p z ^ 2) * (1 - p z) - q z * (-q z)) / (1 - p z) ^ 2
            = ρ ^ 2 - K * f z * ρ + 2 - g := by
          rw [← hgdef, hqz, hpz]; field_simp; ring
        rw [hE]
        have h1 : ρ - K * f z ≤ -(3 / μ) := by linarith
        have h1' : ρ - K * f z ≤ 0 := h1.trans (neg_nonpos.2 (by positivity))
        have h2 : ρ * (ρ - K * f z) ≤ μ * (ρ - K * f z) := by
          nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hρμ) h1']
        have h3 : μ * (-(3 / μ)) = -3 := by field_simp
        have h4 : μ * (ρ - K * f z) ≤ -3 := (mul_le_mul_of_nonneg_left h1 hμ.le).trans h3.le
        nlinarith)
      ⟨le_rfl, hx1⟩ ⟨hx1, le_rfl⟩ hx1
    simp only at hm
    have hrx := hrμ x (by linarith)
    have hr1 : r η₁ < M' := by
      simp only [hr]; rw [div_lt_iff₀ (hgpos η₁ hη₁a)]; linarith
    linarith
  rw [eventually_atTop]
  refine ⟨a₂, fun η hη => ?_⟩
  have hg : 0 ≤ 1 - p η := by have := hp1 η (ha₂a.le.trans hη); linarith
  exact (mul_le_mul_of_nonneg_right (le_max_left M μ) hg).trans (claim η hη)

end Scratch0828.Riccati

#print axioms Scratch0828.Riccati.riccati_up
