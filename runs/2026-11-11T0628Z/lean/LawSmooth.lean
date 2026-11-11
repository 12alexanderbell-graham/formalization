import Checked.Trust.NonVacuity
import Checked.Records.Findings

open Set Filter Topology Metric
open Checked.Cosmography Checked.Cosmography.Aviles

namespace Checked.Trust.NCD

/-- **Bootstrap.** If near `t₀` the function `a` is differentiable with `ȧ = Φ(a)`, and `Φ` is `Cⁿ`
near `a(t₀)`, then `a` is `Cⁿ` at `t₀`. -/
theorem contDiffAt_of_law (n : ℕ) (a Φ : ℝ → ℝ) (t₀ : ℝ)
    (hΦ : ∀ᶠ x in 𝓝 (a t₀), ContDiffAt ℝ n Φ x)
    (hd : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t ∧ deriv a t = Φ (a t)) :
    ContDiffAt ℝ n a t₀ := by
  have hac : ContinuousAt a t₀ := hd.self_of_nhds.1.continuousAt
  have hW : {t | DifferentiableAt ℝ a t ∧ deriv a t = Φ (a t)} ∩
      a ⁻¹' {x | ContDiffAt ℝ n Φ x} ∈ 𝓝 t₀ :=
    Filter.inter_mem hd (hac.preimage_mem_nhds hΦ)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hW
  set I := ball t₀ δ with hI
  have hIo : IsOpen I := isOpen_ball
  have hder : ∀ t ∈ I, HasDerivAt a (Φ (a t)) t := fun t ht => by
    rw [← (hball ht).1.2]; exact (hball ht).1.1.hasDerivAt
  have hgood : ∀ t ∈ I, ContDiffAt ℝ n Φ (a t) := fun t ht => (hball ht).2
  have key : ∀ k : ℕ, k ≤ n → ContDiffOn ℝ k a I := by
    intro k
    induction k with
    | zero =>
      intro _
      exact contDiffOn_zero.2 fun t ht => (hder t ht).continuousAt.continuousWithinAt
    | succ k ih =>
      intro hk
      have hk' : ContDiffOn ℝ k a I := ih (by omega)
      rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hIo]
      refine ⟨fun t ht => (hder t ht).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · intro h; exact absurd h (by simp)
      · have hc : ContDiffOn ℝ k (fun t => Φ (a t)) I := by
          intro t ht
          have h1 : ContDiffAt ℝ k a t := hk'.contDiffAt (hIo.mem_nhds ht)
          have h2 : ContDiffAt ℝ k Φ (a t) :=
            (hgood t ht).of_le (by exact_mod_cast (show k ≤ n by omega))
          exact (h2.comp t h1).contDiffWithinAt
        exact hc.congr fun t ht => (hder t ht).deriv
  exact (key n le_rfl).contDiffAt (hIo.mem_nhds (mem_ball_self hδ))

/-- A flat ΛCDM expansion law makes the scale factor smooth at `t₀` (every finite order). -/
theorem contDiffAt_of_flatLCDM {Ω : ℝ} {a : ℝ → ℝ} {t₀ : ℝ} (hL : IsFlatLCDM Ω a t₀) (n : ℕ) :
    ContDiffAt ℝ n a t₀ := by
  obtain ⟨-, hev⟩ := hL
  have ha0 : 0 < a t₀ := hev.self_of_nhds.1
  set H := hubble a t₀
  set g : ℝ → ℝ := fun x => Ω * (a t₀ / x) ^ 3 + 1 - Ω with hg
  refine contDiffAt_of_law n a (fun x => x * H * √(g x)) t₀ ?_ ?_
  · have hgc : ContinuousAt g (a t₀) := by
      simp only [hg]
      exact ((continuousAt_const.div continuousAt_id ha0.ne').pow 3 |>.const_mul Ω |>.add
        continuousAt_const).sub continuousAt_const
    have hg1 : g (a t₀) = 1 := by simp only [hg]; field_simp; ring
    have hne : ∀ᶠ x in 𝓝 (a t₀), g x ≠ 0 := hgc.eventually_ne (by rw [hg1]; norm_num)
    have hx0 : ∀ᶠ x in 𝓝 (a t₀), x ≠ 0 := continuousAt_id.eventually_ne ha0.ne'
    filter_upwards [hne, hx0] with x hx hx0
    have hgs : ContDiffAt ℝ n g x := by
      simp only [hg]
      exact ((contDiffAt_const.div contDiffAt_id hx0).pow 3 |>.const_smul Ω |>.add
        contDiffAt_const).sub contDiffAt_const
    exact (contDiffAt_id.mul contDiffAt_const).mul (hgs.sqrt hx)
  · filter_upwards [hev] with t ⟨hpos, hdt, hh⟩
    refine ⟨hdt, ?_⟩
    have h1 : 1 + redshift a t₀ t = a t₀ / a t := by simp [redshift]
    rw [h1] at hh
    have : deriv a t = hubble a t * a t := by
      simp only [hubble]; field_simp
    rw [this, hh]; simp only [hg]; ring

/-- Smoothness is redundant in `Aviles.flatLCDM_coeffs`: the flat ΛCDM law makes the scale factor
smooth (bootstrap `contDiffAt_of_law`). -/
theorem flatLCDM_coeffs_r2 : dropped% Checked.Cosmography.Aviles.flatLCDM_coeffs 2 := by
  intro Ω a t₀ hL
  exact flatLCDM_coeffs Ω a t₀ hL (by exact_mod_cast contDiffAt_of_flatLCDM hL 6)

theorem F1_l0_r2 : dropped% Checked.Records.F1_l0 2 := by
  intro a t₀ hL
  exact Checked.Records.F1_l0 a t₀ hL (by exact_mod_cast contDiffAt_of_flatLCDM hL 6)

theorem F3_D4_LCDM_r2 : dropped% Checked.Records.F3_D4_LCDM 2 := by
  intro a t₀ hL
  exact Checked.Records.F3_D4_LCDM a t₀ hL (by exact_mod_cast contDiffAt_of_flatLCDM hL 6)

/-- A flat CPL expansion law makes the scale factor smooth at `t₀` (every finite order). -/
theorem contDiffAt_of_flatCPL {Ω w₀ wₐ : ℝ} {a : ℝ → ℝ} {t₀ : ℝ} (hL : CPL.IsFlatCPL Ω w₀ wₐ a t₀)
    (n : ℕ) : ContDiffAt ℝ n a t₀ := by
  obtain ⟨-, hev⟩ := hL
  have ha0 : 0 < a t₀ := hev.self_of_nhds.1
  set H := hubble a t₀
  set g : ℝ → ℝ := fun x => Ω * (a t₀ / x) ^ 3 + (1 - Ω) * (a t₀ / x) ^ (3 * (1 + w₀ + wₐ)) *
    Real.exp (-(3 * wₐ * (a t₀ / x - 1)) / (a t₀ / x)) with hg
  refine contDiffAt_of_law n a (fun x => x * H * √(g x)) t₀ ?_ ?_
  · have hu : ContinuousAt (fun x : ℝ => a t₀ / x) (a t₀) :=
      continuousAt_const.div continuousAt_id ha0.ne'
    have hu1 : (fun x : ℝ => a t₀ / x) (a t₀) = 1 := div_self ha0.ne'
    have hgc : ContinuousAt g (a t₀) := by
      simp only [hg]
      refine ((hu.pow 3).const_mul Ω).add (((hu.rpow_const (Or.inl (div_self ha0.ne' ▸ one_ne_zero))).const_mul
        (1 - Ω)).mul (Real.continuous_exp.continuousAt.comp ?_))
      exact ((hu.sub continuousAt_const).const_mul (3 * wₐ)).neg.div hu (by rw [div_self ha0.ne']; norm_num)
    have hg1 : g (a t₀) = 1 := by
      simp only [hg, div_self ha0.ne']; norm_num
    have hne : ∀ᶠ x in 𝓝 (a t₀), g x ≠ 0 := hgc.eventually_ne (by rw [hg1]; norm_num)
    have hpos : ∀ᶠ x in 𝓝 (a t₀), 0 < x := lt_mem_nhds ha0
    filter_upwards [hne, hpos] with x hx hx0
    have hus : ContDiffAt ℝ n (fun x : ℝ => a t₀ / x) x := contDiffAt_const.div contDiffAt_id hx0.ne'
    have hupos : a t₀ / x ≠ 0 := (div_pos ha0 hx0).ne'
    have hgs : ContDiffAt ℝ n g x := by
      simp only [hg]
      exact ((hus.pow 3).const_smul Ω).add (((hus.rpow_const_of_ne hupos).const_smul (1 - Ω)).mul
        ((((hus.sub contDiffAt_const).const_smul (3 * wₐ)).neg.div hus hupos).exp))
    exact (contDiffAt_id.mul contDiffAt_const).mul (hgs.sqrt hx)
  · filter_upwards [hev] with t ⟨hpos, hdt, hh⟩
    refine ⟨hdt, ?_⟩
    have h1 : 1 + redshift a t₀ t = a t₀ / a t := by simp [redshift]
    have h2 : redshift a t₀ t = a t₀ / a t - 1 := by simp [redshift]
    rw [h1, h2] at hh
    have : deriv a t = hubble a t * a t := by
      simp only [hubble]; field_simp
    rw [this, hh]; simp only [hg]; ring

theorem flatCPL_coeffs_r2 : dropped% Checked.Cosmography.CPL.flatCPL_coeffs 2 := by
  intro Ω w₀ wₐ a t₀ hL
  exact CPL.flatCPL_coeffs Ω w₀ wₐ a t₀ hL (by exact_mod_cast contDiffAt_of_flatCPL hL 5)

theorem printedL0_ne_r2 : dropped% Checked.Cosmography.CPL.printedL0_ne 2 := by
  intro Ω w₀ wₐ a t₀ hL hne
  exact CPL.printedL0_ne Ω w₀ wₐ a t₀ hL (by exact_mod_cast contDiffAt_of_flatCPL hL 5) hne

theorem F2_toy_r2 : dropped% Checked.Records.F2_toy 2 := by
  intro a t₀ hL
  exact Checked.Records.F2_toy a t₀ hL (by exact_mod_cast contDiffAt_of_flatCPL hL 5)

theorem F2_error_r2 : dropped% Checked.Records.F2_error 2 := by
  intro w₀ a t₀ hL
  exact Checked.Records.F2_error w₀ a t₀ hL (by exact_mod_cast contDiffAt_of_flatCPL hL 5)

end Checked.Trust.NCD
