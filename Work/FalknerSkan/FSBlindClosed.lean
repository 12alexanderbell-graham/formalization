import Mathlib
import Work.FalknerSkan.FSBlind
import Work.FalknerSkan.FalknerSkan

/-!
# Falkner–Skan rows: the blind restatement, closed

The blind restater's `Blind.FalknerSkan.claimA` (a solution of the β = 1/2 problem in its
iterated-`derivWithin` encoding, wall shear in the window) follows from the program's frozen
`Work.FalknerSkan.fs_half_exists`, and `claimB` (every β = 0 solution in that encoding has wall
shear in the window) from `Work.FalknerSkan.fs_zero_wall_shear`.
-/

namespace Work.FalknerSkan.BlindClosed
open Set Filter Topology

/-- Within `Ici 0`, a `HasDerivWithinAt` derivative is the `derivWithin`. -/
theorem dw_eq {f p : ℝ → ℝ} (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) :
    ∀ η ∈ Ici (0 : ℝ), derivWithin f (Ici 0) η = p η :=
  fun η hη => (hf η hη).derivWithin (uniqueDiffOn_Ici 0 η hη)

theorem claimA_closed : ∃ f : ℝ → ℝ, Blind.FalknerSkan.IsSolution (1/2) f ∧
    (0.927680039 : ℝ) < derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 ∧
    derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 < (0.927680040 : ℝ) := by
  obtain ⟨f, p, q, hf, hp, hq, f0, p0, lim, lo, hi⟩ := Work.FalknerSkan.fs_half_exists
  have e1 := dw_eq hf
  have hp' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (derivWithin f (Ici 0)) (q η) (Ici 0) η :=
    fun η hη => (hp η hη).congr (fun x hx => e1 x hx) (e1 η hη)
  have e2 := dw_eq hp'
  have hq' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (derivWithin (derivWithin f (Ici 0)) (Ici 0))
      (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η :=
    fun η hη => (hq η hη).congr (fun x hx => e2 x hx) (e2 η hη)
  have e3 := dw_eq hq'
  have z : (0 : ℝ) ∈ Ici (0 : ℝ) := mem_Ici.mpr le_rfl
  refine ⟨f, ⟨fun x hx => (hf x hx).differentiableWithinAt,
    fun x hx => (hp' x hx).differentiableWithinAt, fun x hx => (hq' x hx).differentiableWithinAt,
    fun x hx => ?_, f0, by rw [e1 0 z, p0], ?_⟩, by rw [e2 0 z]; exact lo, by rw [e2 0 z]; exact hi⟩
  · show derivWithin (derivWithin (derivWithin f (Ici 0)) (Ici 0)) (Ici 0) x +
        f x * derivWithin (derivWithin f (Ici 0)) (Ici 0) x +
        1 / 2 * (1 - derivWithin f (Ici 0) x ^ 2) = 0
    rw [e3 x hx, e2 x hx, e1 x hx]; ring
  · refine lim.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact (e1 x hx).symm

theorem claimB_closed : ∀ f : ℝ → ℝ, Blind.FalknerSkan.IsSolution 0 f →
    (0.4695999883610 : ℝ) ≤ derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 ∧
    derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 ≤ (0.4695999883611 : ℝ) := by
  intro f ⟨d0, d1, d2, he, f0, p0, lim⟩
  refine Work.FalknerSkan.fs_zero_wall_shear f (derivWithin f (Ici 0))
    (derivWithin (derivWithin f (Ici 0)) (Ici 0)) (fun x hx => (d0 x hx).hasDerivWithinAt)
    (fun x hx => (d1 x hx).hasDerivWithinAt) (fun x hx => ?_) f0 p0 lim
  have h := (d2 x hx).hasDerivWithinAt
  refine h.congr_deriv ?_
  have : derivWithin (derivWithin (derivWithin f (Ici 0)) (Ici 0)) (Ici 0) x +
      f x * derivWithin (derivWithin f (Ici 0)) (Ici 0) x +
      0 * (1 - derivWithin f (Ici 0) x ^ 2) = 0 := he x hx
  linarith

end Work.FalknerSkan.BlindClosed
