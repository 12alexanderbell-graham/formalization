import Checked.FalknerSkan.LimitCore
/-! Scratch (run 2026-11-09T0828Z, fork B): Lemma L of the β < 0 research note —
for f' = p, p' = q, q' = −K f q + 1 − p² (K > 0): if q > 0 and p < 1 on [a, ∞) and
p(a) > −1, then p → 1; and p → 1 forces f → ∞. -/

namespace Scratch0828.NegLimit
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

/-- **Lemma L, core**: p exceeds every level below 1. -/
theorem exceeds {K : ℝ} (hK : 0 < K) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) + 1 - p η ^ 2) (Ici 0) η)
    {a : ℝ} (ha : 0 ≤ a) (hqpos : ∀ η ∈ Ici a, 0 < q η) (hpa : -1 < p a)
    (hp1 : ∀ η ∈ Ici a, p η < 1) {L : ℝ} (hL : L < 1) : ∃ η ∈ Ici a, L < p η := by
  by_contra hcon
  push Not at hcon
  have hpaL : p a ≤ L := hcon a self_mem_Ici
  have hpmono : ∀ x y, a ≤ x → x ≤ y → p x ≤ p y := fun x y hx hxy =>
    mono hp ha (b := y) (fun z hz => (hqpos z hz.1.le).le) ⟨hx, hxy⟩ ⟨hx.trans hxy, le_rfl⟩ hxy
  set c := min (1 - p a ^ 2) (1 - L ^ 2) with hc
  have hc0 : 0 < c := lt_min (by nlinarith) (by nlinarith)
  have hsq : ∀ η, a ≤ η → c ≤ 1 - p η ^ 2 := by
    intro η hη
    have h1 := hpmono a η le_rfl hη
    have h2 := hcon η hη
    rcases le_total 0 (p η) with h | h
    · exact (min_le_right _ _).trans (by nlinarith)
    · exact (min_le_left _ _).trans (by nlinarith)
  set B := |f a| + 1 with hB
  have hB1 : 1 ≤ B := by simp [hB]
  have hfB : ∀ η, a ≤ η → f η ≤ B + η := by
    intro η hη
    have hG : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => s - f s) (1 - p x) (Ici 0) x :=
      fun x hx => ((hasDerivWithinAt_id x _).sub (hf x hx))
    have := mono hG ha (b := η) (fun z hz => by
      have := hp1 z hz.1.le; linarith) ⟨le_rfl, hη⟩ ⟨hη, le_rfl⟩ hη
    simp only at this
    have := le_abs_self (f a)
    linarith
  -- φ = q − (c/2K)(B + η)⁻¹
  set κ := c / (2 * K) with hκ
  have hκ0 : 0 < κ := by positivity
  set φ : ℝ → ℝ := fun s => q s - κ * (B + s)⁻¹ with hφ
  set φ' : ℝ → ℝ := fun s => (-(K * f s * q s) + 1 - p s ^ 2) - κ * (-(1 : ℝ) / (B + s) ^ 2)
    with hφ'
  have hφd : ∀ x, a < x → HasDerivAt φ (φ' x) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt ha hx
    have hne : B + x ≠ 0 := by linarith
    have h1 := ((hasDerivAt_id x).const_add B).inv hne
    simp only [id] at h1
    exact (at_of hq hx0).sub (h1.const_mul κ)
  have hφc : ∀ b T, a ≤ b → ContinuousOn φ (Icc b T) := by
    intro b T hb
    have h1 := cont_of hq (a := b) (b := T) (ha.trans hb)
    have h2 : ContinuousOn (fun s : ℝ => (B + s)⁻¹) (Icc b T) :=
      (continuousOn_const.add continuousOn_id).inv₀ (fun x hx => by
        have : (0:ℝ) ≤ x := (ha.trans hb).trans hx.1
        have hB0 : 0 ≤ |f a| := abs_nonneg _
        simp only [Pi.add_apply, id_eq, ne_eq]; intro h; linarith)
    exact h1.sub (continuousOn_const.mul h2)
  have hkey : ∀ x, a < x → φ x ≤ 0 → c / 2 ≤ φ' x := by
    intro x hx hφx
    have hx0 : 0 < x := lt_of_le_of_lt ha hx
    have hBx : 0 < B + x := by linarith
    have hqx := hqpos x hx.le
    have hfx := hfB x hx.le
    have hsx := hsq x hx.le
    simp only [hφ] at hφx
    -- K (B + x) q ≤ c / 2
    have hq_le : K * (B + x) * q x ≤ c / 2 := by
      have : q x ≤ κ * (B + x)⁻¹ := by linarith
      calc K * (B + x) * q x ≤ K * (B + x) * (κ * (B + x)⁻¹) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = c / 2 := by rw [hκ]; field_simp
    have hKfq : K * f x * q x ≤ K * (B + x) * q x := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfx hK.le) hqx.le
      linarith
    have hsec : 0 ≤ -(κ * (-(1:ℝ) / (B + x) ^ 2)) := by
      have : 0 ≤ κ * (1 / (B + x) ^ 2) := by positivity
      have e : -(κ * (-(1:ℝ) / (B + x) ^ 2)) = κ * (1 / (B + x) ^ 2) := by ring
      rw [e]; exact this
    simp only [hφ']
    linarith
  -- Step A: φ becomes positive somewhere after a
  have stepA : ∃ η₁, a < η₁ ∧ 0 < φ η₁ := by
    by_contra hA
    push Not at hA
    set x := a + 1 + 2 * (|φ (a + 1)| + 1) / c with hxdef
    have ha1 : a < a + 1 := by linarith
    have hx1 : a + 1 ≤ x := by
      have : 0 ≤ 2 * (|φ (a + 1)| + 1) / c := by positivity
      linarith
    have hm := monoOn_of (g := fun s => φ s - c / 2 * s) (g' := fun s => φ' s - c / 2)
      (a := a + 1) (b := x)
      ((hφc (a + 1) x ha1.le).sub (continuousOn_const.mul continuousOn_id))
      (fun z hz => ((hφd z (by linarith [hz.1])).sub ((hasDerivAt_id z).const_mul (c / 2))).congr_deriv
        (by simp))
      (fun z hz => by
        have := hkey z (by linarith [hz.1]) (hA z (by linarith [hz.1]))
        linarith)
      ⟨le_rfl, hx1⟩ ⟨hx1, le_rfl⟩ hx1
    simp only at hm
    have hφx := hA x (by linarith)
    have : φ x ≥ φ (a + 1) + c / 2 * (x - (a + 1)) := by linarith
    have e : c / 2 * (x - (a + 1)) = |φ (a + 1)| + 1 := by
      rw [hxdef]; field_simp; ring
    have := neg_abs_le (φ (a + 1))
    linarith
  obtain ⟨η₁, hη₁a, hη₁⟩ := stepA
  -- Step B: φ > 0 on [η₁, ∞)
  have stepB : ∀ x, η₁ ≤ x → 0 < φ x :=
    stay_pos (fun x hx => hφd x (hη₁a.trans hx)) (fun T => hφc η₁ T hη₁a.le) hη₁
      (fun x hx h0 => by
        have := hkey x (hη₁a.trans hx) h0.le
        linarith)
  -- Step C: p − κ log(B + η) is nondecreasing on [η₁, ∞)
  have hpη₁ : -1 < p η₁ := lt_of_lt_of_le hpa (hpmono a η₁ le_rfl hη₁a.le)
  set X := Real.log (B + η₁) + 4 / κ + 1 with hX
  set x := max (η₁ + 1) (Real.exp X) with hxdef
  have hx1 : η₁ ≤ x := le_trans (by linarith) (le_max_left _ _)
  have hm := monoOn_of (g := fun s => p s - κ * Real.log (B + s)) (g' := fun s => φ s)
    (a := η₁) (b := x)
    ((cont_of hp (a := η₁) (b := x) (ha.trans hη₁a.le)).sub (continuousOn_const.mul
      ((continuousOn_const.add continuousOn_id).log (fun z hz => by
        have : (0:ℝ) ≤ z := ha.trans (hη₁a.le.trans hz.1)
        have hB0 : 0 ≤ |f a| := abs_nonneg _
        simp only [Pi.add_apply, id_eq, ne_eq]; intro h; linarith))))
    (fun z hz => by
      have hz0 : 0 < z := lt_of_le_of_lt (ha.trans hη₁a.le) hz.1
      have hne : B + z ≠ 0 := by linarith
      have h1 := ((hasDerivAt_id z).const_add B).log hne
      simp only [id] at h1
      exact ((at_of hp hz0).sub (h1.const_mul κ)).congr_deriv (by simp [hφ, div_eq_mul_inv]))
    (fun z hz => (stepB z hz.1.le).le)
    ⟨le_rfl, hx1⟩ ⟨hx1, le_rfl⟩ hx1
  simp only at hm
  have hpx : p x ≤ L := hcon x (hη₁a.le.trans hx1)
  have hlog1 : X ≤ Real.log (B + x) := by
    have hxpos : 0 < Real.exp X := Real.exp_pos X
    have : Real.exp X ≤ B + x := by
      have := le_max_right (η₁ + 1) (Real.exp X); linarith
    calc X = Real.log (Real.exp X) := (Real.log_exp X).symm
      _ ≤ Real.log (B + x) := Real.log_le_log hxpos this
  have : κ * X ≤ κ * Real.log (B + x) := mul_le_mul_of_nonneg_left hlog1 hκ0.le
  have e : κ * X = κ * Real.log (B + η₁) + 4 + κ := by
    rw [hX]; field_simp
  linarith

/-- **Lemma L**: q > 0 and p < 1 on [a, ∞) with p(a) > −1 force p → 1. -/
theorem neg_limit {K : ℝ} (hK : 0 < K) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) + 1 - p η ^ 2) (Ici 0) η)
    {a : ℝ} (ha : 0 ≤ a) (hqpos : ∀ η ∈ Ici a, 0 < q η) (hpa : -1 < p a)
    (hp1 : ∀ η ∈ Ici a, p η < 1) : Tendsto p atTop (𝓝 1) := by
  rw [tendsto_order]
  refine ⟨fun l hl => ?_, fun u hu => ?_⟩
  · obtain ⟨η₁, hη₁, hl1⟩ := exceeds hK hf hp hq ha hqpos hpa hp1 hl
    rw [eventually_atTop]
    refine ⟨η₁, fun η hη => lt_of_lt_of_le hl1 ?_⟩
    have hη₁' : a ≤ η₁ := hη₁
    exact mono hp ha (b := η) (fun z hz => (hqpos z hz.1.le).le) ⟨hη₁', hη⟩
      ⟨hη₁'.trans hη, le_rfl⟩ hη
  · rw [eventually_atTop]
    exact ⟨a, fun η hη => (hp1 η hη).trans hu⟩

/-- p → 1 forces f → ∞. -/
theorem f_tendsto {f p : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hlim : Tendsto p atTop (𝓝 1)) : Tendsto f atTop atTop := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (lt_mem_nhds (show (1:ℝ)/2 < 1 by norm_num)))
  set N' := max N 0 with hN'
  have hN0 : 0 ≤ N' := le_max_right _ _
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨N' + 2 * |b - f N'|, fun x hx => ?_⟩
  have hxN : N' ≤ x := by have := abs_nonneg (b - f N'); linarith
  have hG : ∀ y ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => f s - s / 2) (p y - 1 / 2) (Ici 0) y :=
    fun y hy => ((hf y hy).sub ((hasDerivWithinAt_id y _).div_const 2)).congr_deriv (by simp)
  have hm := mono hG hN0 (b := x) (fun z hz => by
    have := hN z ((le_max_left N 0).trans hz.1.le); linarith) ⟨le_rfl, hxN⟩ ⟨hxN, le_rfl⟩ hxN
  simp only at hm
  have := le_abs_self (b - f N')
  linarith

end Scratch0828.NegLimit

#print axioms Scratch0828.NegLimit.neg_limit
#print axioms Scratch0828.NegLimit.f_tendsto
