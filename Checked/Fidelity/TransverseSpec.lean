import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Checked.Cosmography.Transverse

/-!
# `transverse` pinned by the blind ODE law (trust track T1, run 2026-10-30T2228Z)

`TransverseSpec` is copied verbatim (by script) from the blind specification
`Work/Fidelity/BlindTransverse.lean` (written by a subagent that did not read the program's
definition). Its field `ode` says: for every `K`, `χ ↦ S K χ` solves `S'' = −K S`,
`S(0) = 0`, `S'(0) = 1` on all of `ℝ`.

* `transverse_meets_spec`: the program's `transverse` satisfies every field.
* `transverseSpec_pins`: any `S` satisfying **the `ode` field alone** equals `transverse`
  (uniqueness for the linear system `(S, S')' = (S', −K S)`, Mathlib's Grönwall-based
  `ODE_solution_unique_of_mem_Ioo`). The closed-form fields are anchors only.
-/

open Real

namespace Checked.Fidelity

open Checked.Cosmography.Transverse

/-- Textbook laws for the FLRW transverse-distance factor `S K χ`.
`ode` is determining by itself; the remaining fields are closed-form anchors. -/
structure TransverseSpec (S : ℝ → ℝ → ℝ) : Prop where
  /-- Determining law: `S K` is twice differentiable on all of `ℝ` and solves
  `S'' = -K S` with `S(0) = 0`, `S'(0) = 1`. -/
  ode : ∀ K : ℝ, ∃ S' : ℝ → ℝ,
    (∀ χ, HasDerivAt (S K) (S' χ) χ) ∧
    (∀ χ, HasDerivAt S' (-K * S K χ) χ) ∧
    S K 0 = 0 ∧ S' 0 = 1
  /-- Flat case. -/
  flat : ∀ χ, S 0 χ = χ
  /-- Closed spherical case. -/
  closed : ∀ K, 0 < K → ∀ χ, S K χ = Real.sin (Real.sqrt K * χ) / Real.sqrt K
  /-- Open hyperbolic case. -/
  open_ : ∀ K, K < 0 → ∀ χ, S K χ = Real.sinh (Real.sqrt (-K) * χ) / Real.sqrt (-K)
  /-- Unit sphere anchor. -/
  unit_closed : ∀ χ, S 1 χ = Real.sin χ
  /-- Unit hyperboloid anchor. -/
  unit_open : ∀ χ, S (-1) χ = Real.sinh χ
  /-- Oddness in `χ`. -/
  odd : ∀ K χ, S K (-χ) = -S K χ

/-! ## The blind reference formula (helper, verbatim from the blind file) -/

/-- Reference three-case formula. -/
noncomputable def refS (K χ : ℝ) : ℝ :=
  if 0 < K then Real.sin (Real.sqrt K * χ) / Real.sqrt K
  else if K = 0 then χ
  else Real.sinh (Real.sqrt (-K) * χ) / Real.sqrt (-K)

lemma refS_pos {K : ℝ} (hK : 0 < K) :
    refS K = fun χ => Real.sin (Real.sqrt K * χ) / Real.sqrt K := by
  funext χ; simp [refS, hK]

lemma refS_zero : refS 0 = fun χ => χ := by
  funext χ; simp [refS]

lemma refS_neg {K : ℝ} (hK : K < 0) :
    refS K = fun χ => Real.sinh (Real.sqrt (-K) * χ) / Real.sqrt (-K) := by
  funext χ; simp [refS, (not_lt.2 hK.le), hK.ne]

theorem refS_spec : TransverseSpec refS where
  ode K := by
    rcases lt_trichotomy K 0 with hK | rfl | hK
    · -- K < 0
      have hs : 0 < Real.sqrt (-K) := Real.sqrt_pos.2 (by linarith)
      have hss : Real.sqrt (-K) * Real.sqrt (-K) = -K := Real.mul_self_sqrt (by linarith)
      refine ⟨fun χ => Real.cosh (Real.sqrt (-K) * χ), ?_, ?_, ?_, ?_⟩
      · intro χ
        rw [refS_neg hK]
        have h := ((hasDerivAt_id' χ).const_mul (Real.sqrt (-K))).sinh.div_const (Real.sqrt (-K))
        convert h using 1
        field_simp
      · intro χ
        rw [refS_neg hK]
        have h := ((hasDerivAt_id' χ).const_mul (Real.sqrt (-K))).cosh
        convert h using 1
        field_simp
        linear_combination (-Real.sinh (Real.sqrt (-K) * χ)) * hss
      · simp [refS_neg hK]
      · simp
    · -- K = 0
      refine ⟨fun _ => 1, ?_, ?_, ?_, ?_⟩
      · intro χ; rw [refS_zero]; exact hasDerivAt_id χ
      · intro χ; simpa using hasDerivAt_const χ (1 : ℝ)
      · simp [refS_zero]
      · rfl
    · -- K > 0
      have hs : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
      have hss : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK.le
      refine ⟨fun χ => Real.cos (Real.sqrt K * χ), ?_, ?_, ?_, ?_⟩
      · intro χ
        rw [refS_pos hK]
        have h := ((hasDerivAt_id' χ).const_mul (Real.sqrt K)).sin.div_const (Real.sqrt K)
        convert h using 1
        field_simp
      · intro χ
        rw [refS_pos hK]
        have h := ((hasDerivAt_id' χ).const_mul (Real.sqrt K)).cos
        convert h using 1
        field_simp
        linear_combination (Real.sin (Real.sqrt K * χ)) * hss
      · simp [refS_pos hK]
      · simp
  flat χ := by simp [refS]
  closed K hK χ := by simp [refS, hK]
  open_ K hK χ := by simp [refS, (not_lt.2 hK.le), hK.ne]
  unit_closed χ := by simp [refS]
  unit_open χ := by
    have : ¬ (0 : ℝ) < -1 := by norm_num
    simp [refS, this]
  odd K χ := by
    unfold refS
    split_ifs <;> simp [mul_neg, Real.sin_neg, Real.sinh_neg, neg_div]


/-- The program's `transverse` is the blind three-case formula. -/
lemma transverse_eq_refS : transverse = refS := by
  funext K χ
  unfold transverse refS
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · simp [hK, not_lt.2 hK.le, hK.ne]
  · simp
  · simp [hK]

theorem transverse_meets_spec : TransverseSpec transverse := by
  rw [transverse_eq_refS]; exact refS_spec

/-- Uniqueness for `S'' = −K S`, `S(0) = 0`, `S'(0) = 1` on all of `ℝ`. -/
lemma ode_unique (K : ℝ) (S₁ S₁' S₂ S₂' : ℝ → ℝ)
    (h₁ : ∀ χ, HasDerivAt S₁ (S₁' χ) χ) (h₁' : ∀ χ, HasDerivAt S₁' (-K * S₁ χ) χ)
    (h₂ : ∀ χ, HasDerivAt S₂ (S₂' χ) χ) (h₂' : ∀ χ, HasDerivAt S₂' (-K * S₂ χ) χ)
    (i₁ : S₁ 0 = S₂ 0) (i₂ : S₁' 0 = S₂' 0) : S₁ = S₂ := by
  let L : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (-K • ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hL : ∀ x : ℝ × ℝ, L x = (x.2, -K * x.1) := fun x => by simp [L]
  have hf : ∀ (S S' : ℝ → ℝ), (∀ χ, HasDerivAt S (S' χ) χ) →
      (∀ χ, HasDerivAt S' (-K * S χ) χ) →
      ∀ χ, HasDerivAt (fun t => (S t, S' t)) (L (S χ, S' χ)) χ := by
    intro S S' hS hS' χ
    rw [hL]
    exact (hS χ).prodMk (hS' χ)
  funext χ
  have key := ODE_solution_unique_of_mem_Ioo (v := fun _ => L) (s := fun _ => Set.univ)
    (K := ‖L‖₊) (a := -(|χ| + 1)) (b := |χ| + 1) (t₀ := 0)
    (fun _ _ => L.lipschitz.lipschitzOnWith)
    (by constructor <;> linarith [abs_nonneg χ])
    (fun t _ => ⟨hf S₁ S₁' h₁ h₁' t, trivial⟩) (fun t _ => ⟨hf S₂ S₂' h₂ h₂' t, trivial⟩)
    (by simp [i₁, i₂])
    (show χ ∈ Set.Ioo (-(|χ| + 1)) (|χ| + 1) by
      constructor <;> linarith [neg_abs_le χ, le_abs_self χ])
  exact congrArg Prod.fst key

/-- **Pin.** Any `S` obeying the blind determining law `ode` is the program's `transverse`. -/
theorem transverseSpec_pins (S : ℝ → ℝ → ℝ) (h : TransverseSpec S) : S = transverse := by
  funext K
  obtain ⟨S', hd, hd', h0, h1⟩ := h.ode K
  obtain ⟨T', td, td', t0, t1⟩ := transverse_meets_spec.ode K
  exact ode_unique K (S K) S' (transverse K) T' hd hd' td td' (h0.trans t0.symm) (h1.trans t1.symm)

end Checked.Fidelity
