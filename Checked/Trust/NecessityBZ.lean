import Checked.Trust.NonVacuity
import Checked.FalknerSkan.NegDecay
import Checked.FalknerSkan.MonotoneExists
import Checked.FalknerSkan.FSScale

/-! Hypothesis necessity for the two Falkner–Skan decay headlines with adverse pressure gradient
(`Checked.FalknerSkan.NegDecay.fs_neg_decay_equal`, `Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear`;
run 2026-11-26T0028Z): hypothesis 1 (`β < 0`) of both is REDUNDANT. For `β ≥ 0` two solutions of the
boundary-value problem with positive second derivative have the same wall shear, with no condition on the decay:
for `β > 0` by the similarity scaling `s ↦ (c f(s/c), p(s/c), q(s/c)/c)` with `c = √β` to the coefficient-`1/β`
problem and the Crocco comparison `Checked.FalknerSkan.MonotoneExists.not_lt_wall`; for `β = 0` (Blasius) by
the amplitude scaling `η ↦ (μ f(μη), μ² p(μη), μ³ q(μη))`, which maps a solution to a solution and multiplies the
limit of the velocity by `μ²`: the scaled first solution with the second's wall shear equals the second solution
by forward uniqueness, so `μ² = 1`. Equal wall shears give equal solutions by
`Checked.FalknerSkan.NegCore.eq_of_startb`. Module `NecessityBZ`. -/

namespace Checked.Trust.NecessityBZ
open Set Filter Topology

/-- The amplitude scaling of the Blasius system (`β = 0`). -/
theorem blasius_scale {μ : ℝ} (hμ : 0 < μ) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 0 * (1 - p η ^ 2)) (Ici 0) η) :
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => μ * f (μ * s)) (μ ^ 2 * p (μ * η)) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => μ ^ 2 * p (μ * s)) (μ ^ 3 * q (μ * η)) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => μ ^ 3 * q (μ * s))
      (-((μ * f (μ * η)) * (μ ^ 3 * q (μ * η))) - 0 * (1 - (μ ^ 2 * p (μ * η)) ^ 2)) (Ici 0) η) := by
  have hm : MapsTo (fun s : ℝ => μ * s) (Ici 0) (Ici 0) :=
    fun s hs => mul_nonneg hμ.le (mem_Ici.mp hs)
  have hd : ∀ x : ℝ, HasDerivWithinAt (fun s : ℝ => μ * s) μ (Ici 0) x := fun x => by
    simpa using (hasDerivWithinAt_id x (Ici (0:ℝ))).const_mul μ
  refine ⟨fun η hη => ?_, fun η hη => ?_, fun η hη => ?_⟩
  · have h := ((hf (μ * η) (hm hη)).comp η (hd η) hm).const_mul μ
    exact h.congr_deriv (by ring)
  · have h := ((hp (μ * η) (hm hη)).comp η (hd η) hm).const_mul (μ ^ 2)
    exact h.congr_deriv (by ring)
  · have h := ((hq (μ * η) (hm hη)).comp η (hd η) hm).const_mul (μ ^ 3)
    exact h.congr_deriv (by ring)

/-- Blasius (`β = 0`): two solutions with `f(0) = 0`, `p(0) = 0`, `p → 1` and `q > 0` on the closed half-line
have the same wall shear. -/
theorem blasius_wall_eq {f p q f₂ p₂ q₂ : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 0 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - 0 * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hpos₂ : ∀ η ∈ Ici (0 : ℝ), 0 < q₂ η) :
    q 0 = q₂ 0 := by
  have ha : 0 < q 0 := hpos 0 (mem_Ici.2 le_rfl)
  have hb : 0 < q₂ 0 := hpos₂ 0 (mem_Ici.2 le_rfl)
  set r := q₂ 0 / q 0 with hr
  have hr0 : 0 < r := div_pos hb ha
  set μ := r ^ ((1 : ℝ) / 3) with hμdef
  have hμ : 0 < μ := Real.rpow_pos_of_pos hr0 _
  have hμ3 : μ ^ 3 = r := by
    rw [hμdef, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    norm_num
  obtain ⟨sf, sp, sq⟩ := blasius_scale hμ hf hp hq
  have hstart : μ ^ 3 * q (μ * 0) = q₂ 0 := by
    rw [mul_zero, hμ3, hr]; field_simp
  have heq := Checked.FalknerSkan.NegCore.eq_of_startb (β := 0) sf sp sq hf₂ hp₂ hq₂
    (by simp only [mul_zero, hf0, hf₂0]) (by simp only [mul_zero, hp0, hp₂0]) hstart
  -- the limits of the two velocities
  have hlimS : Tendsto (fun s => μ ^ 2 * p (μ * s)) atTop (𝓝 (μ ^ 2 * 1)) :=
    (hlim.comp (tendsto_id.const_mul_atTop hμ)).const_mul (μ ^ 2)
  have hlimS' : Tendsto (fun s => μ ^ 2 * p (μ * s)) atTop (𝓝 1) := by
    apply hlim₂.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    exact ((heq s hs).2.1).symm
  have hμ2 : μ ^ 2 * 1 = 1 := tendsto_nhds_unique hlimS hlimS'
  have hμ1 : μ = 1 := by
    have h2 : μ ^ 2 = 1 := by simpa using hμ2
    nlinarith [sq_nonneg (μ - 1), sq_nonneg (μ + 1)]
  have hr1 : r = 1 := by rw [← hμ3, hμ1]; norm_num
  rw [hr, div_eq_one_iff_eq ha.ne'] at hr1
  exact hr1.symm

/-- `β > 0`: two solutions with `f(0) = 0`, `p(0) = 0`, `p → 1` and `q > 0` on the closed half-line have the same
wall shear (scaling to the coefficient-`1/β` problem and the Crocco comparison). -/
theorem pos_wall_eq {β : ℝ} (hβ : 0 < β) {f p q f₂ p₂ q₂ : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - β * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hpos₂ : ∀ η ∈ Ici (0 : ℝ), 0 < q₂ η) :
    q 0 = q₂ 0 := by
  set c := Real.sqrt β with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 hβ
  have hc2 : c ^ 2 = β := Real.sq_sqrt hβ.le
  have hk : (0 : ℝ) ≤ 1 / c ^ 2 := by positivity
  have hq1 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(1 * f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  have hq₂1 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(1 * f₂ η * q₂ η) - β * (1 - p₂ η ^ 2)) (Ici 0) η :=
    fun η hη => (hq₂ η hη).congr_deriv (by ring)
  obtain ⟨sf, sp, sq⟩ := Checked.FalknerSkan.FSScale.scale hc0 hf hp hq1
  obtain ⟨sf₂, sp₂, sq₂⟩ := Checked.FalknerSkan.FSScale.scale hc0 hf₂ hp₂ hq₂1
  have sq' : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => q (s / c) / c)
      (-(1 / c ^ 2 * (c * f (s / c)) * (q (s / c) / c)) - 1 + p (s / c) ^ 2) (Ici 0) s := by
    intro s hs
    refine (sq s hs).congr_deriv ?_
    rw [← hc2, div_self (pow_pos hc0 2).ne']; ring
  have sq₂' : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => q₂ (s / c) / c)
      (-(1 / c ^ 2 * (c * f₂ (s / c)) * (q₂ (s / c) / c)) - 1 + p₂ (s / c) ^ 2) (Ici 0) s := by
    intro s hs
    refine (sq₂ s hs).congr_deriv ?_
    rw [← hc2, div_self (pow_pos hc0 2).ne']; ring
  have z0 : (0 : ℝ) / c = 0 := zero_div c
  have hsf0 : c * f (0 / c) = 0 := by rw [z0, hf0, mul_zero]
  have hsp0 : p (0 / c) = 0 := by rw [z0, hp0]
  have hsf₂0 : c * f₂ (0 / c) = 0 := by rw [z0, hf₂0, mul_zero]
  have hsp₂0 : p₂ (0 / c) = 0 := by rw [z0, hp₂0]
  have hspos : ∀ s ∈ Ici (0 : ℝ), 0 < q (s / c) / c := fun s hs =>
    div_pos (hpos _ (Checked.FalknerSkan.FSScale.mapsTo_div hc0 hs)) hc0
  have hspos₂ : ∀ s ∈ Ici (0 : ℝ), 0 < q₂ (s / c) / c := fun s hs =>
    div_pos (hpos₂ _ (Checked.FalknerSkan.FSScale.mapsTo_div hc0 hs)) hc0
  have l := Checked.FalknerSkan.FSScale.scale_lim hc0 hlim
  have l₂ := Checked.FalknerSkan.FSScale.scale_lim hc0 hlim₂
  have h1 := Checked.FalknerSkan.MonotoneExists.not_lt_wall hk sf sp sq' hsf0 hsp0 l hspos
    sf₂ sp₂ sq₂' hsf₂0 hsp₂0 l₂ hspos₂
  have h2 := Checked.FalknerSkan.MonotoneExists.not_lt_wall hk sf₂ sp₂ sq₂' hsf₂0 hsp₂0 l₂ hspos₂
    sf sp sq' hsf0 hsp0 l hspos
  have e : q (0 / c) / c = q₂ (0 / c) / c := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
  rw [z0] at e
  exact (div_left_inj' hc0.ne').1 e

/-- `β ≥ 0`: equal wall shears, with no condition on the decay. -/
theorem nonneg_wall_eq {β : ℝ} (hβ : 0 ≤ β) {f p q f₂ p₂ q₂ : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - β * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hpos₂ : ∀ η ∈ Ici (0 : ℝ), 0 < q₂ η) :
    q 0 = q₂ 0 := by
  rcases hβ.lt_or_eq with h | h
  · exact pos_wall_eq h hf hp hq hf0 hp0 hlim hpos hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂
  · subst h
    exact blasius_wall_eq hf hp hq hf0 hp0 hlim hpos hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂

theorem fs_neg_decay_equal_r1 : dropped% Checked.FalknerSkan.NegDecay.fs_neg_decay_equal 1 := by
  intro β f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hpos hdec hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂ hdec₂
  rcases lt_or_ge β 0 with hβ | hβ
  · exact Checked.FalknerSkan.NegDecay.fs_neg_decay_equal β hβ f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hpos
      hdec hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂ hdec₂
  · exact Checked.FalknerSkan.NegCore.eq_of_startb hf hp hq hf₂ hp₂ hq₂ (by rw [hf0, hf₂0])
      (by rw [hp0, hp₂0])
      (nonneg_wall_eq hβ hf hp hq hf0 hp0 hlim hpos hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂)

theorem fs_neg_decay_max_shear_r1 : dropped% Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear 1 := by
  intro β f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hpos hdec hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂
  rcases lt_or_ge β 0 with hβ | hβ
  · exact Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear β hβ f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim
      hpos hdec hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂
  · exact (nonneg_wall_eq hβ hf hp hq hf0 hp0 hlim hpos hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂).symm.le

end Checked.Trust.NecessityBZ
