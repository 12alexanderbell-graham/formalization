import ComparatorChallenges.NavierStokes
import Readings.NS
import Closure.NSHelpers

/-! Target 1: closure of the blind reading of Clay's (C) and (D) (runs/2026-11-26T1529Z/T1/reading.lean)
against the frozen comparator statements of openai/NavierStokesAndEuler at f9e8bc5
(`NavierStokes.Comparator.navier_stokes_breakdown_R3`, `..._periodic`), taken with `type_of%`.
Direction: frozen ⟹ reading (what the outside proof establishes implies the Clay claim as read). -/

open scoped ContDiff Laplacian
open Set MeasureTheory

namespace ExternalT1

lemma slice_x {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → ℝ → F}
    (hg : ContDiffOn ℝ ∞ (fun z : E × ℝ => g z.1 z.2) (univ ×ˢ Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (fun y => g y t) :=
  hg.comp_contDiff (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)

lemma slice_t {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → ℝ → F}
    (hg : ContDiffOn ℝ ∞ (fun z : E × ℝ => g z.1 z.2) (univ ×ˢ Ici 0)) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableWithinAt ℝ (fun s => g x s) (Ici 0) t := by
  have h := hg.comp ((contDiff_const (c := x)).prodMk contDiff_id).contDiffOn (s := Ici 0)
    (fun s hs => ⟨mem_univ x, hs⟩)
  exact (h.differentiableOn (by simp)) t ht

lemma div_eq {v : E → E} {x : E} (hv : DifferentiableAt ℝ v x) :
    NavierStokes.Comparator.divergence v x = ∑ i, Reading.pd i (fun y => v y i) x := by
  unfold NavierStokes.Comparator.divergence Reading.pd
  rw [trace_eq]
  apply Finset.sum_congr rfl; intro i _
  rw [fderiv_coord hv]; rfl

lemma ns_coord {ν : ℝ} {u : E → ℝ → E} {p : E → ℝ → ℝ} {f : E → ℝ → E}
    (hu : Reading.SmoothOnS u) (hp : Reading.SmoothOnS p) (h1 : Reading.Eq1 ν u p f)
    (x : E) (t : ℝ) (ht : 0 ≤ t) :
    derivWithin (u x ·) (Set.Ici 0) t + fderiv ℝ (u · t) x (u x t) =
      ν • Δ (u · t) x - gradient (p · t) x + f x t := by
  have hux := slice_x hu ht
  have hpx := slice_x hp ht
  have hdx : Differentiable ℝ (fun y => u y t) := hux.differentiable (by simp)
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [derivWithin_coord ht (slice_t hu x ht), clm_apply_expand,
    laplacian_coord (hux.of_le (by simp)), gradient_coord]
  have e1 : ∀ j, (fderiv ℝ (fun y => u y t) x (ee j)) i = Reading.pd j (fun y => u y t i) x := by
    intro j; rw [← fderiv_coord (hdx x)]; rfl
  simp only [e1]
  have := h1 x t ht i
  unfold Reading.pd at this ⊢
  simp only [show ∀ j, ee j = Reading.e j from fun _ => rfl]
  convert this using 2


lemma decay_nat {g : ℝ} {w : ℝ} (hw : 0 < w) (K : ℕ) {C : ℝ} (h : g ≤ C / w ^ (K : ℝ)) :
    w ^ K * g ≤ C := by
  rw [Real.rpow_natCast, le_div_iff₀ (by positivity)] at h; linarith

lemma memLp_of_integrable_sq {v : E → E} (hv : Continuous v)
    (h : Integrable (fun x => ‖v x‖ ^ 2)) : MemLp (fun x => ‖v x‖) 2 :=
  (memLp_two_iff_integrable_sq (hv.norm.aestronglyMeasurable)).mpr h

theorem closure_C : (type_of% @NavierStokes.Comparator.navier_stokes_breakdown_R3) →
    (type_of% @Reading.reading_C) := by
  intro h ν hν
  obtain ⟨u0, f, hu0, hf, hno⟩ := h ν hν
  refine ⟨u0, f, ⟨hu0.smooth, fun x => ?_⟩, hf.smooth, fun k K => ?_, fun N K => ?_, ?_⟩
  · rw [← div_eq (hu0.smooth.differentiable (by simp) x)]; exact hu0.div_free x
  · obtain ⟨C, hC⟩ := hu0.decay k K
    exact ⟨C, fun x => decay_nat (by positivity) K (hC x)⟩
  · obtain ⟨C, hC⟩ := hf.decay N K
    refine ⟨C, fun x t ht => decay_nat (by positivity) K (hC x t ht)⟩
  · rintro ⟨p, u, hp, hu, h1, h2, h3, h7⟩
    apply hno
    obtain ⟨C, hC⟩ := h7
    exact ⟨u, p,
      { navier_stokes := fun x t ht => ns_coord hu hp h1 x t ht
        div_free := fun x t ht => by
          rw [div_eq ((slice_x hu ht).differentiable (by simp) x)]; exact h2 x t ht
        initial_condition := h3
        velocity_smooth := hu
        pressure_smooth := hp
        integrable := fun t ht => memLp_of_integrable_sq (slice_x hu ht).continuous (hC t ht).1
        globally_bounded_energy := ⟨C, fun t ht => (hC t ht).2⟩ }⟩

theorem closure_D : (type_of% @NavierStokes.Comparator.navier_stokes_breakdown_periodic) →
    (type_of% @Reading.reading_D) := by
  intro h ν hν
  obtain ⟨u0, f, hu0, hf, hno⟩ := h ν hν
  refine ⟨u0, f, ⟨hu0.smooth, fun x => ?_⟩, hf.smooth, fun x j => hu0.isOnePeriodic x j,
    fun x t ht j => hf.isOnePeriodic t ht x j, fun N K => ?_, ?_⟩
  · rw [← div_eq (hu0.smooth.differentiable (by simp) x)]; exact hu0.div_free x
  · obtain ⟨C, hC⟩ := hf.decay N K
    refine ⟨C, fun x t ht => ?_⟩
    rw [abs_of_nonneg ht]; exact decay_nat (by positivity) K (hC x t ht)
  · rintro ⟨p, u, hp, hu, h1, h2, h3, h10, hpp⟩
    apply hno
    exact ⟨u, p,
      { navier_stokes := fun x t ht => ns_coord hu hp h1 x t ht
        div_free := fun x t ht => by
          rw [div_eq ((slice_x hu ht).differentiable (by simp) x)]; exact h2 x t ht
        initial_condition := h3
        velocity_smooth := hu
        pressure_smooth := hp
        isOnePeriodic_velocity := fun t ht x j => (h10 x t ht j).symm
        isOnePeriodic_pressure := fun t ht x j => hpp x t ht j }⟩

end ExternalT1
#print axioms ExternalT1.closure_C
#print axioms ExternalT1.closure_D
