import Mathlib
import Work.FalknerSkan.Separation

/-!
# Falkner–Skan separation: the blind restatement, closed (run 2026-11-11T0232Z)

The theorem below is the blind restater's text (Sonnet, from the claim in words only;
`runs/2026-11-11T0232Z/blind/SepBlind.lean`), copied verbatim with its placeholder proof replaced
by a proof from `Work.FalknerSkan.Separation.fs_separation_exists`. The blind version asks for a
globally C³ function with two-sided iterated `deriv`; the frozen theorem gives one-sided
derivatives on [0, ∞). The gap is closed by extending the solution to η < 0 by its third-order
Taylor polynomial at the wall, −β η³/6 (f(0) = f'(0) = f''(0) = 0, f'''(0⁺) = −β).

Blind file's own module comment:

Falkner–Skan separation profile.

Encoding choices:
* The unknown is `f : ℝ → ℝ`, required `ContDiff ℝ 3` globally (so `deriv` is meaningful);
  the ODE and all conditions are only imposed for `η ≥ 0`.
* Derivatives: `f' = deriv f`, `f'' = deriv (deriv f)`, `f''' = deriv (deriv (deriv f))`.
* "f'(η) → 1 as η → ∞": `Tendsto (deriv f) atTop (𝓝 1)`.
* "for all sufficiently large η": `∀ᶠ η in atTop`.
* Strict interval for β via two strict inequalities with exact rational literals.
-/

namespace Blind.Sep

open Set Filter Topology

/-- Gluing a function with one-sided derivatives on [0, ∞) to a function differentiable
everywhere, matching value and derivative at 0, gives a function differentiable everywhere. -/
theorem glue {u u' v v' : ℝ → ℝ}
    (hu : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt u (u' η) (Ici 0) η)
    (hv : ∀ η, HasDerivAt v (v' η) η) (h0 : u 0 = v 0) (h0' : u' 0 = v' 0) :
    ∀ η, HasDerivAt (fun x => if 0 ≤ x then u x else v x) (if 0 ≤ η then u' η else v' η) η := by
  intro η
  rcases lt_trichotomy η 0 with h | h | h
  · rw [ite_eq_right (not_le.2 h)]
    refine (hv η).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with x hx
    rw [ite_eq_right (not_le.2 hx)]
  · subst h
    rw [ite_eq_left le_rfl]
    have hR : HasDerivWithinAt (fun x => if 0 ≤ x then u x else v x) (u' 0) (Ici 0) 0 :=
      (hu 0 (mem_Ici.2 le_rfl)).congr (fun x hx => ite_eq_left hx) (ite_eq_left le_rfl)
    have hL : HasDerivWithinAt (fun x => if 0 ≤ x then u x else v x) (u' 0) (Iic 0) 0 := by
      rw [h0']
      refine (hv 0).hasDerivWithinAt.congr (fun x hx => ?_) (by rw [ite_eq_left le_rfl, h0])
      rcases eq_or_lt_of_le (show x ≤ 0 from hx) with e | e
      · rw [e, ite_eq_left le_rfl, h0]
      · rw [ite_eq_right (not_le.2 e)]
    have := hL.union hR
    rw [Iic_union_Ici] at this
    exact this.hasDerivAt univ_mem
  · rw [ite_eq_left h.le]
    have hd : HasDerivAt u (u' η) η := (hu η h.le).hasDerivAt (Ici_mem_nhds h)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds h] with x hx
    rw [ite_eq_left (le_of_lt hx)]

/-- Gluing continuity in the same way. -/
theorem glue_cont {u v : ℝ → ℝ}
    (hu : ∀ η ∈ Ici (0 : ℝ), ContinuousWithinAt u (Ici 0) η) (hv : Continuous v) (h0 : u 0 = v 0) :
    Continuous (fun x => if 0 ≤ x then u x else v x) := by
  rw [continuous_iff_continuousAt]
  intro η
  rcases lt_trichotomy η 0 with h | h | h
  · refine (hv.continuousAt (x := η)).congr ?_
    filter_upwards [Iio_mem_nhds h] with x hx
    rw [ite_eq_right (not_le.2 hx)]
  · subst h
    have hR : ContinuousWithinAt (fun x => if 0 ≤ x then u x else v x) (Ici 0) 0 :=
      (hu 0 (mem_Ici.2 le_rfl)).congr (fun x hx => ite_eq_left hx) (ite_eq_left le_rfl)
    have hL : ContinuousWithinAt (fun x => if 0 ≤ x then u x else v x) (Iic 0) 0 := by
      refine (hv.continuousWithinAt).congr (fun x hx => ?_) (by rw [ite_eq_left le_rfl, h0])
      rcases eq_or_lt_of_le (show x ≤ 0 from hx) with e | e
      · rw [e, ite_eq_left le_rfl, h0]
      · rw [ite_eq_right (not_le.2 e)]
    have := hL.union hR
    rw [Iic_union_Ici, continuousWithinAt_univ] at this
    exact this
  · refine ((hu η h.le).continuousAt (Ici_mem_nhds h)).congr ?_
    filter_upwards [Ioi_mem_nhds h] with x hx
    rw [ite_eq_left (le_of_lt hx)]

theorem blind_sep :
    ∃ β : ℝ, (-1988377351 / 10000000000 : ℝ) < β ∧ β < (-1988377350 / 10000000000 : ℝ) ∧
      ∃ f : ℝ → ℝ, ContDiff ℝ 3 f ∧
        (∀ η : ℝ, 0 ≤ η →
          deriv (deriv (deriv f)) η + f η * deriv (deriv f) η
            + β * (1 - (deriv f η) ^ 2) = 0) ∧
        f 0 = 0 ∧ deriv f 0 = 0 ∧
        Filter.Tendsto (deriv f) Filter.atTop (nhds 1) ∧
        deriv (deriv f) 0 = 0 ∧
        (∀ η : ℝ, 0 < η → 0 < deriv (deriv f) η) ∧
        (∀ M : ℝ, ∀ᶠ η in Filter.atTop, M * (1 - deriv f η) ≤ deriv (deriv f) η) := by
  obtain ⟨β, hβ, f, p, q, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec⟩ :=
    Work.FalknerSkan.Separation.fs_separation_exists
  set r : ℝ → ℝ := fun η => -(f η * q η) - β * (1 - p η ^ 2) with hr
  set g : ℝ → ℝ := fun x => if 0 ≤ x then f x else -β * x ^ 3 / 6 with hg
  set g1 : ℝ → ℝ := fun x => if 0 ≤ x then p x else -β * x ^ 2 / 2 with hg1
  set g2 : ℝ → ℝ := fun x => if 0 ≤ x then q x else -β * x with hg2
  set g3 : ℝ → ℝ := fun x => if 0 ≤ x then r x else -β with hg3
  have d0 : ∀ η, HasDerivAt g (g1 η) η :=
    glue (u := f) (u' := p) (v := fun x => -β * x ^ 3 / 6) (v' := fun x => -β * x ^ 2 / 2) hf
      (fun η => by
        have := ((hasDerivAt_pow 3 η).const_mul (-β)).div_const 6
        exact this.congr_deriv (by push_cast; ring))
      (by rw [hf0]; ring) (by rw [hp0]; ring)
  have d1 : ∀ η, HasDerivAt g1 (g2 η) η :=
    glue (u := p) (u' := q) (v := fun x => -β * x ^ 2 / 2) (v' := fun x => -β * x) hp
      (fun η => by
        have := ((hasDerivAt_pow 2 η).const_mul (-β)).div_const 2
        exact this.congr_deriv (by push_cast; ring))
      (by rw [hp0]; ring) (by rw [hq0]; ring)
  have d2 : ∀ η, HasDerivAt g2 (g3 η) η :=
    glue (u := q) (u' := r) (v := fun x => -β * x) (v' := fun _ => -β) hq
      (fun η => by
        have := (hasDerivAt_id η).const_mul (-β)
        exact this.congr_deriv (by simp))
      (by rw [hq0]; ring) (by simp only [hr, hf0, hp0, hq0]; ring)
  have cont_f : ∀ η ∈ Ici (0 : ℝ), ContinuousWithinAt f (Ici 0) η :=
    fun η hη => (hf η hη).continuousWithinAt
  have cont_p : ∀ η ∈ Ici (0 : ℝ), ContinuousWithinAt p (Ici 0) η :=
    fun η hη => (hp η hη).continuousWithinAt
  have cont_q : ∀ η ∈ Ici (0 : ℝ), ContinuousWithinAt q (Ici 0) η :=
    fun η hη => (hq η hη).continuousWithinAt
  have c3 : Continuous g3 :=
    glue_cont (u := r) (v := fun _ => -β)
      (fun η hη => (((cont_f η hη).mul (cont_q η hη)).neg).sub
        (continuousWithinAt_const.mul (continuousWithinAt_const.sub ((cont_p η hη).pow 2))))
      continuous_const (by simp only [hr, hf0, hp0, hq0]; ring)
  have e0 : deriv g = g1 := funext fun η => (d0 η).deriv
  have e1 : deriv g1 = g2 := funext fun η => (d1 η).deriv
  have e2 : deriv g2 = g3 := funext fun η => (d2 η).deriv
  have C2 : ContDiff ℝ 1 g2 := by
    rw [contDiff_one_iff_deriv]
    exact ⟨fun η => (d2 η).differentiableAt, by rw [e2]; exact c3⟩
  have C1 : ContDiff ℝ 2 g1 := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    exact ⟨fun η => (d1 η).differentiableAt, by simp, by rw [e1]; exact C2⟩
  have C0 : ContDiff ℝ 3 g := by
    rw [show (3 : WithTop ℕ∞) = 2 + 1 from rfl, contDiff_succ_iff_deriv]
    exact ⟨fun η => (d0 η).differentiableAt, by simp, by rw [e0]; exact C1⟩
  have hβ1 : (-1988377351 / 10000000000 : ℝ) < β := by
    have := hβ.1; norm_num at this ⊢; linarith
  have hβ2 : β < (-1988377350 / 10000000000 : ℝ) := by
    have := hβ.2; norm_num at this ⊢; linarith
  refine ⟨β, hβ1, hβ2, g, C0, fun η hη => ?_, ?_, ?_, ?_, ?_, fun η hη => ?_, fun M => ?_⟩
  · rw [e0, e1, e2]
    simp only [hg, hg1, hg2, hg3, hr, ite_eq_left hη]
    ring
  · simp only [hg, ite_eq_left le_rfl, hf0]
  · rw [e0]; simp only [hg1, ite_eq_left le_rfl, hp0]
  · rw [e0]
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with η hη
    simp only [hg1, ite_eq_left hη]
  · rw [e0, e1]; simp only [hg2, ite_eq_left le_rfl, hq0]
  · rw [e0, e1]; simp only [hg2, ite_eq_left hη.le]; exact hpos η hη
  · rw [e0, e1]
    filter_upwards [hdec M, eventually_ge_atTop 0] with η h1 h2
    simp only [hg1, hg2, ite_eq_left h2]
    exact h1

end Blind.Sep

#print axioms Blind.Sep.blind_sep
