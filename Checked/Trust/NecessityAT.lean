import Checked.Trust.NecessityAJ
import Checked.Math.BonnorEbertCount

/-! Hypothesis necessity for the exact number of Bonnor–Ebert radii of a given mass
(`Checked.Math.BonnorEbertCount.bonnor_ebert_count`, run 2026-11-18T1628Z). The hypotheses are those of
`Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema` in the same order (1 the derivative of w, 2 continuity
of φ at the centre, 3 the equation, 4 the centre value). The count conclusion contains no strict-maximum clause,
but its first two count clauses give one (`glob_of_count`: no radius has a mass above the first extreme value and
exactly one radius has that value), so the witnesses of `Checked.Trust.NecessityAJ` carry over: the zero
function (3) has mass zero, below the window of the first extreme value; w = 0 with a linear φ (1) has a mass
that increases without bound; the rescaled regular solution (4) has its strict maximiser at half the true
critical radius. Continuity of φ at the centre is forced by the equation (2 REDUNDANT). -/

namespace Checked.Trust.NecessityAT
open Set Filter Topology

/-- The first two count clauses give the strict global maximum: if no radius has a value above f x and
exactly one radius has the value f x, then every other radius has a smaller value. -/
theorem glob_of_count (f : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x)
    (ha : ∀ μ : ℝ, f x < μ → {s ∈ Ici (0 : ℝ) | f s = μ} = ∅)
    (hb : {s ∈ Ici (0 : ℝ) | f s = f x}.encard = 1) :
    ∀ s ∈ Ici (0 : ℝ), s ≠ x → f s < f x := by
  intro s hs hne
  by_contra h
  rcases lt_or_eq_of_le (not_lt.1 h) with h' | h'
  · have h0 : {t ∈ Ici (0 : ℝ) | f t = f s} = ∅ := ha (f s) h'
    have hmem : s ∈ {t ∈ Ici (0 : ℝ) | f t = f s} := ⟨hs, rfl⟩
    rw [h0] at hmem
    exact hmem
  · obtain ⟨y, hy⟩ := Set.encard_eq_one.1 hb
    have hxm : x ∈ {s ∈ Ici (0 : ℝ) | f s = f x} := ⟨hx, rfl⟩
    have hsm : s ∈ {s ∈ Ici (0 : ℝ) | f s = f x} := ⟨hs, h'.symm⟩
    rw [hy, mem_singleton_iff] at hxm hsm
    exact hne (hsm.trans hxm.symm)

theorem bonnor_ebert_count_r2 :
    dropped% Checked.Math.BonnorEbertCount.bonnor_ebert_count 2 := by
  intro w φ h1 h3 h4
  exact Checked.Math.BonnorEbertCount.bonnor_ebert_count w φ h1
    (Checked.Trust.NecessityAJ.cont_at_zero_Ici w φ h1 h3) h3 h4

theorem bonnor_ebert_count_h3 :
    necessity% Checked.Math.BonnorEbertCount.bonnor_ebert_count 3 := by
  refine ⟨fun _ => 0, fun _ => 0, fun s _ => hasDerivWithinAt_const _ _ _,
    continuousWithinAt_const, rfl, ?_⟩
  rintro ⟨ξ, -, -, -, -, hm, -⟩
  simp at hm
  linarith

theorem bonnor_ebert_count_h1 :
    necessity% Checked.Math.BonnorEbertCount.bonnor_ebert_count 1 := by
  refine ⟨fun _ => 0, fun s => -(s / 3), (continuous_id.div_const 3).neg.continuousWithinAt,
    fun s hs => ?_, rfl, ?_⟩
  · have hs0 : s ≠ 0 := (mem_Ioi.mp hs).ne'
    exact (((hasDerivAt_id' s).div_const 3).neg.hasDerivWithinAt).congr_deriv
      (by rw [Real.exp_zero]; field_simp; ring)
  · rintro ⟨ξ, -, -, h0, -, -, -, -, -, -, -, -, -, -, -, -, ha, hb, -⟩
    have hmax := glob_of_count _ (ξ 0) (by linarith) ha hb
    have h := hmax (ξ 0 + 1) (by simp only [mem_Ici]; linarith) (by intro h; linarith)
    have hsq0 : 0 < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    simp only [neg_neg, zero_div, Real.exp_zero, mul_one] at h
    rw [div_lt_div_iff_of_pos_right hsq0] at h
    nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 0 + 1)]

theorem bonnor_ebert_count_h4 :
    necessity% Checked.Math.BonnorEbertCount.bonnor_ebert_count 4 := by
  obtain ⟨w, φ, hw, hφ0, hφ, h0⟩ := Checked.Math.BEGlobalExists.exists_global
  obtain ⟨hu, hψ0, hψ⟩ := Checked.Trust.NecessityAJ.scaled_hyps_Ici 2 (by norm_num) w φ hw hφ0 hφ
  refine ⟨fun s => w (2 * s) + 2 * Real.log 2, fun s => 2 * φ (2 * s), hu, hψ0, hψ, ?_⟩
  rintro ⟨η, -, -, hη1, -, -, -, -, -, -, -, -, -, -, -, -, ha, hb, -⟩
  have hglob := glob_of_count _ (η 0) (by linarith) ha hb
  obtain ⟨ξ, -, -, hξ1, hξ2, hmax, -⟩ :=
    Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema w φ hw hφ0 hφ h0
  have hm : ∀ s, (fun s => s ^ 2 * (-(fun s => 2 * φ (2 * s)) s) *
      Real.exp ((fun s => w (2 * s) + 2 * Real.log 2) s / 2) / Real.sqrt (4 * Real.pi)) s =
      Checked.Trust.NecessityM.mass w φ (2 * s) := by
    intro s
    simp only [Checked.Trust.NecessityM.mass]
    rw [show (w (2 * s) + 2 * Real.log 2) / 2 = w (2 * s) / 2 + Real.log 2 by ring, Real.exp_add,
      Real.exp_log (by norm_num)]
    ring
  have h1 := hglob (ξ 0 / 2) (by simp only [mem_Ici]; linarith) (by intro h; linarith)
  have h2 := hmax (2 * η 0) (by simp only [mem_Ici]; linarith) (by intro h; linarith)
  have e1 := hm (ξ 0 / 2)
  have e2 := hm (η 0)
  simp only at e1 e2 h1
  rw [e1, e2, show 2 * (ξ 0 / 2) = ξ 0 by ring] at h1
  simp only [Checked.Trust.NecessityM.mass] at h1
  linarith

end Checked.Trust.NecessityAT
