import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Checked.Cosmography.CPLCoefficients

/-!
# Flat matter + CPL models exist for every Ω, w₀, wₐ (closes the referee's caveat on C4)

General tool (`exists_local_model`): for any expansion law `H/H₀ = E(a/a₀)` with `E` five times
differentiable at 1 and `E 1 = 1`, Picard–Lindelöf (Mathlib) gives a positive scale factor with
`ȧ = a E(a)` near `t₀ = 0`, `a(0) = 1`, which is `C⁵` at 0 (bootstrapped from the ODE).

Instance: `E(x) = √(Ω x⁻³ + (1−Ω) x^{-3(1+w₀+wₐ)} e^{−3wₐ(1−x)})` (CLS Eq. (17) with
`1 + z = 1/x`). Consequence `printedL0_false_at`: the printed l₀ of Eq. (22) is false at **every**
parameter point with `(1 − Ω)(7 − Ω) wₐ ≠ 0`, not only at the boundary witness Ω = 0.
-/

namespace Work.Cosmography.CPLExistence

open Filter Topology Metric Set Checked.Cosmography Checked.Cosmography.Aviles
  Checked.Cosmography.CPL

/-- Local existence of a smooth expanding scale factor for a smooth expansion law. -/
theorem exists_local_model (E : ℝ → ℝ) (hE : ContDiffAt ℝ 5 E 1) :
    ∃ a : ℝ → ℝ, a 0 = 1 ∧ ContDiffAt ℝ 5 a 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), 0 < a t ∧ HasDerivAt a (a t * E (a t)) t := by
  set φ : ℝ → ℝ := fun x => x * E x with hφ
  have hφ5 : ContDiffAt ℝ 5 φ 1 := contDiffAt_id.mul hE
  obtain ⟨α, hα0, ε, hε, hα⟩ :=
    (hφ5.of_le (by norm_num) : ContDiffAt ℝ 1 φ 1).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (0 : ℝ)
  have hV : {y : ℝ | ContDiffAt ℝ 5 φ y ∧ 0 < y} ∈ 𝓝 (1 : ℝ) :=
    (hφ5.eventually (by simp)).and (lt_mem_nhds one_pos)
  have hαc : ContinuousAt α 0 :=
    (hα 0 ⟨by linarith, by linarith⟩).continuousAt
  have hW : Ioo (0 - ε) (0 + ε) ∩ α ⁻¹' {y : ℝ | ContDiffAt ℝ 5 φ y ∧ 0 < y} ∈ 𝓝 (0 : ℝ) :=
    Filter.inter_mem (Ioo_mem_nhds (by linarith) (by linarith))
      (hαc.preimage_mem_nhds (by rw [hα0]; exact hV))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hW
  set I := ball (0 : ℝ) δ with hI
  have hIo : IsOpen I := isOpen_ball
  have hder : ∀ t ∈ I, HasDerivAt α (φ (α t)) t := fun t ht => hα t (hball ht).1
  have hgood : ∀ t ∈ I, ContDiffAt ℝ 5 φ (α t) ∧ 0 < α t := fun t ht => (hball ht).2
  have hdα : ∀ t ∈ I, deriv α t = φ (α t) := fun t ht => (hder t ht).deriv
  have key : ∀ k : ℕ, k ≤ 5 → ContDiffOn ℝ k α I := by
    intro k
    induction k with
    | zero =>
      intro _
      exact contDiffOn_zero.2 fun t ht => (hder t ht).continuousAt.continuousWithinAt
    | succ k ih =>
      intro hk
      have hk' : ContDiffOn ℝ k α I := ih (by omega)
      rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hIo]
      refine ⟨fun t ht => (hder t ht).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · intro h; exact absurd h (by simp)
      · have hc : ContDiffOn ℝ k (fun t => φ (α t)) I := by
          intro t ht
          have h1 : ContDiffAt ℝ k α t := hk'.contDiffAt (hIo.mem_nhds ht)
          have h2 : ContDiffAt ℝ k φ (α t) :=
            (hgood t ht).1.of_le (by exact_mod_cast (show k ≤ 5 by omega))
          exact (h2.comp t h1).contDiffWithinAt
        exact hc.congr fun t ht => hdα t ht
  have h0I : (0 : ℝ) ∈ I := mem_ball_self hδ
  refine ⟨α, hα0, (key 5 le_rfl).contDiffAt (hIo.mem_nhds h0I), ?_⟩
  filter_upwards [hIo.mem_nhds h0I] with t ht
  exact ⟨(hgood t ht).2, hder t ht⟩

/-- The CPL expansion law as a function of `x = a/a₀ = 1/(1+z)`. -/
noncomputable def cplE (Ω w₀ wₐ : ℝ) (x : ℝ) : ℝ :=
  √(Ω * (1 / x) ^ 3 + (1 - Ω) * (1 / x) ^ (3 * (1 + w₀ + wₐ)) * Real.exp (-3 * wₐ * (1 - x)))

lemma cplE_one (Ω w₀ wₐ : ℝ) : cplE Ω w₀ wₐ 1 = 1 := by
  simp [cplE]

lemma contDiffAt_cplE (Ω w₀ wₐ : ℝ) : ContDiffAt ℝ 5 (cplE Ω w₀ wₐ) 1 := by
  have hinv : ContDiffAt ℝ 5 (fun x : ℝ => 1 / x) 1 :=
    contDiffAt_const.div contDiffAt_id one_ne_zero
  have hin : ContDiffAt ℝ 5 (fun x : ℝ => Ω * (1 / x) ^ 3 + (1 - Ω) * (1 / x) ^ (3 * (1 + w₀ + wₐ)) *
      Real.exp (-3 * wₐ * (1 - x))) 1 :=
    (contDiffAt_const.mul (hinv.pow 3)).add
      ((contDiffAt_const.mul (hinv.rpow_const_of_ne (by norm_num))).mul
        ((contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id)).exp))
  exact hin.sqrt (by simp)

/-- **Flat matter + CPL models exist for every Ω, w₀, wₐ** (at `t₀ = 0`, `C⁵` there). -/
theorem exists_flatCPL (Ω w₀ wₐ : ℝ) :
    ∃ a : ℝ → ℝ, IsFlatCPL Ω w₀ wₐ a 0 ∧ ContDiffAt ℝ 5 a 0 := by
  obtain ⟨a, ha0, hs, hev⟩ := exists_local_model (cplE Ω w₀ wₐ) (contDiffAt_cplE Ω w₀ wₐ)
  have hH : ∀ t, 0 < a t → HasDerivAt a (a t * cplE Ω w₀ wₐ (a t)) t →
      hubble a t = cplE Ω w₀ wₐ (a t) := by
    intro t hat hd
    rw [hubble, hd.deriv]
    field_simp
  have hH0 : hubble a 0 = 1 := by
    rw [hH 0 (by rw [ha0]; norm_num) hev.self_of_nhds.2, ha0, cplE_one]
  refine ⟨a, ⟨by rw [hH0]; norm_num, ?_⟩, hs⟩
  filter_upwards [hev] with t ⟨hat, hd⟩
  refine ⟨hat, hd.differentiableAt, ?_⟩
  rw [hH t hat hd, hH0, one_mul, cplE]
  have hz : 1 + redshift a 0 t = 1 / a t := by rw [redshift, ha0]; ring
  have hexp : -(3 * wₐ * redshift a 0 t) / (1 + redshift a 0 t) = -3 * wₐ * (1 - a t) := by
    rw [hz, redshift, ha0]; field_simp
  rw [hexp, hz]

/-- **The printed l₀ of CLS Eq. (22) is false at every parameter point with
`(1 − Ω)(7 − Ω) wₐ ≠ 0`**: there is a flat CPL model with those parameters whose l₀ differs. -/
theorem printedL0_false_at (Ω w₀ wₐ : ℝ) (hne : (1 - Ω) * (7 - Ω) * wₐ ≠ 0) :
    ∃ a : ℝ → ℝ, IsFlatCPL Ω w₀ wₐ a 0 ∧ ContDiffAt ℝ 5 a 0 ∧
      cosmoCoeff 5 a 0 ≠ 35 / 2 + (1 - Ω) / 4 * (213 + (7 - Ω) * wₐ) * wₐ
        + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀
        + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2
        + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3
        + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4 := by
  obtain ⟨a, hL, hs⟩ := exists_flatCPL Ω w₀ wₐ
  exact ⟨a, hL, hs, printedL0_ne Ω w₀ wₐ a 0 hL hs hne⟩

end Work.Cosmography.CPLExistence
