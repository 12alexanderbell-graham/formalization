/-!
# Sourced blind specification readings I, J and K against the three remaining pinned definitions
(run 2026-11-27T1028Z)

Same theorem names and shapes as `Checked/Trust/SpecAgreementGH.lean`: `meets_X_R : SpecR X` (the program's
definition is a model of reader R's specification) and `pins_X_R` (every function or condition meeting R's
specification equals / is equivalent to the program's, on R's domain). Readers I (Sonnet), J (Opus) and
K (Haiku) were handed a verbatim LaTeX excerpt of Bamba, Capozziello, Nojiri, Odintsov 2012 (the arXiv
e-print's §II, §VIII.C, §X and §XI up to its Ricci-scalar equation; `runs/2026-11-27T1028Z/sources/`) and, for each item,
only the quantity, its section and the Lean type; none saw the program's text.

Results: all nine readings AGREE.
* `rhoM` (dust density, §XI text after the curvature-fluid density): every reader generalised the source's
  `a⁻³` (written for a scale factor equal to one today) to the cube of the ratio of `a(t₀)` to `a(t)`, as the
  program does; determined where `a(t₀)`, `a(t)` are nonzero (I, K:
  positive; K also asks `a` differentiable at `t₀`).
* `FriedmannEq` (§XI expansion-rate equation) and `MasterEq` (§XI master equation): each reader wrote the equation in the source's
  divided form; the program's multiplied forms are equivalent wherever `F′(R) ≠ 0`, which every reader
  requires (K adds smoothness of `a` and `F`, the program's form holds without it).
* The convention question two readers raised (J: "§XI looks like a mix of conventions") is settled here
  in Lean: `friedmannEq_iff_standard`, `masterEq_iff_standard` prove that the program's §XI equations for
  `(a, F)` are exactly the common-sign metric F(R) equations (Ricci scalar `+6(Ḣ + 2H²)`, curvature-fluid
  term `R f′ − f` halved) for
  `f(x) = −F(−x)`, for every `a`, `F` and with no smoothness assumption: §XI is one consistent convention
  (the sign of `R` and of the Lagrangian flipped together), not a mix.
-/

namespace Checked.Trust.SpecAgreement

open Checked.Cosmography Checked.Cosmography.FRCosmo

/-! ## Algebra shared by every reader -/

private lemma alg_fr_half (h r f x y : ℝ) (hf : f ≠ 0) :
    3 * f * h ^ 2 = r + x / 2 - y ↔ h ^ 2 = 1 / 3 * (r / f + 1 / f * (x / 2 - y)) := by
  have e : 1 / 3 * (r / f + 1 / f * (x / 2 - y)) = (r + x / 2 - y) / (3 * f) := by
    field_simp; ring
  rw [e, eq_div_iff (mul_ne_zero (by norm_num) hf)]
  constructor <;> intro hh <;> linarith

private lemma alg_fr_mul (h r f x y : ℝ) (hf : f ≠ 0) :
    3 * f * h ^ 2 = r + x / 2 - y ↔ h ^ 2 = 1 / 3 * (r / f + 1 / f * (1 / 2 * x - y)) := by
  rw [alg_fr_half h r f x y hf]
  constructor <;> intro hh <;> rw [hh] <;> ring

private lemma alg_m (hd f z : ℝ) (hf : f ≠ 0) :
    -2 * f * hd = z ↔ hd = -(1 / (2 * f)) * z := by
  have e : -(1 / (2 * f)) * z = -z / (2 * f) := by field_simp
  rw [e, eq_div_iff (mul_ne_zero (by norm_num) hf)]
  constructor <;> intro hh <;> linarith

private lemma iter2 (F : ℝ → ℝ) : deriv^[2] F = deriv (deriv F) := rfl
private lemma iter3 (F : ℝ → ℝ) : deriv^[3] F = deriv (deriv (deriv F)) := rfl

/-- The program's dust density, written as every reader determines it. -/
private lemma rhoM_from (ρ : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ)
    (h0 : a t₀ ≠ 0) (h1 : a t ≠ 0)
    (hpres : ρ Ω a t₀ t₀ = 3 * (deriv a t₀ / a t₀) ^ 2 * Ω)
    (hsc : ρ Ω a t₀ t * a t ^ 3 = ρ Ω a t₀ t₀ * a t₀ ^ 3) :
    ρ Ω a t₀ t = rhoM Ω a t₀ t := by
  unfold rhoM hubble
  rw [hpres] at hsc
  have h3 : a t ^ 3 ≠ 0 := pow_ne_zero 3 h1
  rw [div_pow, ← eq_div_iff h3] at hsc
  rw [hsc]
  field_simp

private lemma rhoM_self (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (h0 : a t₀ ≠ 0) :
    rhoM Ω a t₀ t₀ = 3 * (deriv a t₀ / a t₀) ^ 2 * Ω := by
  unfold rhoM hubble
  rw [div_self h0]
  ring

private lemma rhoM_scale (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) (h0 : a t₀ ≠ 0) (h1 : a t ≠ 0) :
    rhoM Ω a t₀ t * a t ^ 3 = rhoM Ω a t₀ t₀ * a t₀ ^ 3 := by
  unfold rhoM
  rw [div_self h0]
  field_simp

/-! ## Reader I (Sonnet) -/

theorem meets_rhoM_I : SecondReadingSpecI.DustDensitySpecI rhoM :=
  ⟨fun Ω a t₀ h0 => rhoM_self Ω a t₀ h0.ne',
   fun Ω a t₀ t h0 h1 => rhoM_scale Ω a t₀ t h0.ne' h1.ne'⟩

theorem pins_rhoM_I (ρ : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : SecondReadingSpecI.DustDensitySpecI ρ)
    (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) (h0 : 0 < a t₀) (h1 : 0 < a t) :
    ρ Ω a t₀ t = rhoM Ω a t₀ t :=
  rhoM_from ρ Ω a t₀ t h0.ne' h1.ne' (h.present Ω a t₀ h0) (h.scaling Ω a t₀ t h0 h1)

theorem meets_FriedmannEq_I : SecondReadingSpecI.FRFriedmannSpecI FriedmannEq :=
  ⟨fun Ω a F t₀ t _ _ hF => by
    unfold FriedmannEq
    rw [iter2]
    exact alg_fr_half _ _ _ _ _ hF⟩

theorem pins_FriedmannEq_I (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop)
    (h : SecondReadingSpecI.FRFriedmannSpecI P) (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ)
    (h0 : 0 < a t₀) (h1 : 0 < a t) (hF : deriv F (curv a t) ≠ 0) :
    P Ω a F t₀ t ↔ FriedmannEq Ω a F t₀ t :=
  (h.iff_eq Ω a F t₀ t h0 h1 hF).trans (meets_FriedmannEq_I.iff_eq Ω a F t₀ t h0 h1 hF).symm

theorem meets_MasterEq_I : SecondReadingSpecI.FRMasterSpecI MasterEq :=
  ⟨fun Ω a F t₀ t _ _ hF => by
    unfold MasterEq
    rw [iter2, iter2, iter3]
    exact alg_m _ _ _ hF⟩

theorem pins_MasterEq_I (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop)
    (h : SecondReadingSpecI.FRMasterSpecI P) (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ)
    (h0 : 0 < a t₀) (h1 : 0 < a t) (hF : deriv F (curv a t) ≠ 0) :
    P Ω a F t₀ t ↔ MasterEq Ω a F t₀ t :=
  (h.iff_eq Ω a F t₀ t h0 h1 hF).trans (meets_MasterEq_I.iff_eq Ω a F t₀ t h0 h1 hF).symm

/-! ## Reader J (Opus) -/

theorem meets_rhoM_J : SecondReadingSpecJ.DustDensitySpecJ rhoM :=
  ⟨fun Ω a t₀ h0 => rhoM_self Ω a t₀ h0,
   fun Ω a t₀ t h1 h0 => rhoM_scale Ω a t₀ t h0 h1⟩

theorem pins_rhoM_J (ρ : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : SecondReadingSpecJ.DustDensitySpecJ ρ)
    (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) (h0 : a t₀ ≠ 0) (h1 : a t ≠ 0) :
    ρ Ω a t₀ t = rhoM Ω a t₀ t :=
  rhoM_from ρ Ω a t₀ t h0 h1 (h.present_value Ω a t₀ h0) (h.dust_scaling Ω a t₀ t h1 h0)

theorem meets_FriedmannEq_J : SecondReadingSpecJ.FRFriedmannSpecJ FriedmannEq :=
  ⟨fun Ω a F t₀ t _ _ hF => by
    unfold FriedmannEq
    rw [iter2]
    exact alg_fr_mul _ _ _ _ _ hF⟩

theorem pins_FriedmannEq_J (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop)
    (h : SecondReadingSpecJ.FRFriedmannSpecJ P) (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ)
    (h1 : a t ≠ 0) (h0 : a t₀ ≠ 0) (hF : deriv F (curv a t) ≠ 0) :
    P Ω a F t₀ t ↔ FriedmannEq Ω a F t₀ t :=
  (h.iff_friedmann Ω a F t₀ t h1 h0 hF).trans
    (meets_FriedmannEq_J.iff_friedmann Ω a F t₀ t h1 h0 hF).symm

theorem meets_MasterEq_J : SecondReadingSpecJ.FRMasterSpecJ MasterEq :=
  ⟨fun Ω a F t₀ t _ _ hF => by
    unfold MasterEq
    rw [iter2, iter2, iter3]
    exact alg_m _ _ _ hF⟩

theorem pins_MasterEq_J (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop)
    (h : SecondReadingSpecJ.FRMasterSpecJ P) (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ)
    (h1 : a t ≠ 0) (h0 : a t₀ ≠ 0) (hF : deriv F (curv a t) ≠ 0) :
    P Ω a F t₀ t ↔ MasterEq Ω a F t₀ t :=
  (h.iff_master Ω a F t₀ t h1 h0 hF).trans (meets_MasterEq_J.iff_master Ω a F t₀ t h1 h0 hF).symm

/-! ## Reader K (Haiku) -/

theorem meets_rhoM_K : SecondReadingSpecK.DustDensitySpecK rhoM :=
  ⟨fun Ω a t₀ t h0 h1 => by
    have := rhoM_scale Ω a t₀ t h0.ne' h1.ne'
    have h3 : a t ^ 3 ≠ 0 := pow_ne_zero 3 h1.ne'
    rw [div_pow, mul_div_assoc', eq_div_iff h3]
    exact this,
   fun Ω a t₀ h0 _ => rhoM_self Ω a t₀ h0.ne'⟩

theorem pins_rhoM_K (ρ : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : SecondReadingSpecK.DustDensitySpecK ρ)
    (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) (h0 : 0 < a t₀) (h1 : 0 < a t) (hd : DifferentiableAt ℝ a t₀) :
    ρ Ω a t₀ t = rhoM Ω a t₀ t := by
  apply rhoM_from ρ Ω a t₀ t h0.ne' h1.ne' (h.present Ω a t₀ h0 hd)
  rw [h.scaling Ω a t₀ t h0 h1, div_pow]
  field_simp

theorem meets_FriedmannEq_K : SecondReadingSpecK.FRFriedmannSpecK FriedmannEq :=
  ⟨fun Ω a F t₀ t _ _ _ _ hF => by
    unfold FriedmannEq
    rw [iter2]
    exact alg_fr_mul _ _ _ _ _ hF⟩

theorem pins_FriedmannEq_K (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop)
    (h : SecondReadingSpecK.FRFriedmannSpecK P) (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ)
    (h0 : 0 < a t₀) (hd : DifferentiableAt ℝ a t₀)
    (hn : ∀ᶠ s in nhds t, 0 < a s ∧ ContDiffAt ℝ 3 a s) (hFs : ContDiffAt ℝ 2 F (curv a t))
    (hF : deriv F (curv a t) ≠ 0) :
    P Ω a F t₀ t ↔ FriedmannEq Ω a F t₀ t :=
  (h.iff Ω a F t₀ t h0 hd hn hFs hF).trans (meets_FriedmannEq_K.iff Ω a F t₀ t h0 hd hn hFs hF).symm

theorem meets_MasterEq_K : SecondReadingSpecK.FRMasterSpecK MasterEq :=
  ⟨fun Ω a F t₀ t _ _ _ _ hF => by
    unfold MasterEq
    rw [iter2, iter2, iter3]
    exact alg_m _ _ _ hF⟩

theorem pins_MasterEq_K (P : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop)
    (h : SecondReadingSpecK.FRMasterSpecK P) (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ)
    (h0 : 0 < a t₀) (hd : DifferentiableAt ℝ a t₀)
    (hn : ∀ᶠ s in nhds t, 0 < a s ∧ ContDiffAt ℝ 4 a s)
    (hFs : ∀ᶠ y in nhds (curv a t), ContDiffAt ℝ 3 F y) (hF : deriv F (curv a t) ≠ 0) :
    P Ω a F t₀ t ↔ MasterEq Ω a F t₀ t :=
  (h.iff Ω a F t₀ t h0 hd hn hFs hF).trans (meets_MasterEq_K.iff Ω a F t₀ t h0 hd hn hFs hF).symm

/-! ## §XI is one convention: the common-sign F(R) equations for `f(x) = −F(−x)`

Readers I, J, K all flagged that §XI's `R = −6(Ḣ + 2H²)` is minus the usual Ricci scalar of the stated metric
(the source's §VIII.C has `+6`), and J asked whether its expansion-rate and master equations mix conventions. The two theorems below
answer it for every scale factor and every `F`, with no smoothness assumption (Mathlib's `deriv` of a
composition with negation needs none): the program's §XI equations for `(a, F)` are the textbook metric F(R)
equations, with Ricci scalar `+6(Ḣ + 2H²)` and curvature fluid `(R f′ − f)/2 − 3HṘf″`, for the Lagrangian
`f(x) = −F(−x)`. Flipping the sign of `R` and of the Lagrangian together is a convention, not an error; with
`F(R) = R` both describe general relativity. -/

private lemma deriv_negneg (G : ℝ → ℝ) : deriv (fun x => -G (-x)) = fun y => deriv G (-y) := by
  funext y
  have e : (fun x => -G (-x)) = -(fun x => G (-x)) := rfl
  rw [e, deriv.neg, deriv_comp_neg, neg_neg]

private lemma deriv_neg_arg (G : ℝ → ℝ) : deriv (fun x => G (-x)) = fun y => -deriv G (-y) := by
  funext y
  exact deriv_comp_neg G y

private lemma curv_std (a : ℝ → ℝ) :
    (fun s => 6 * (deriv (hubble a) s + 2 * hubble a s ^ 2)) = -curv a := by
  funext s
  simp only [Pi.neg_apply, curv]
  ring

/-- The program's §XI expansion-rate equation for `(a, F)` is the common-sign one for `f(x) = −F(−x)`:
`3 f′(Rₛ) H² = ρ_M + (Rₛ f′(Rₛ) − f(Rₛ))/2 − 3 H Ṙₛ f″(Rₛ)` with `Rₛ = 6(Ḣ + 2H²)`. -/
theorem friedmannEq_iff_standard (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) :
    FriedmannEq Ω a F t₀ t ↔
      3 * deriv (fun x => -F (-x)) (6 * (deriv (hubble a) t + 2 * hubble a t ^ 2)) * hubble a t ^ 2 =
        rhoM Ω a t₀ t
          + ((6 * (deriv (hubble a) t + 2 * hubble a t ^ 2))
                * deriv (fun x => -F (-x)) (6 * (deriv (hubble a) t + 2 * hubble a t ^ 2))
              - (fun x => -F (-x)) (6 * (deriv (hubble a) t + 2 * hubble a t ^ 2))) / 2
          - 3 * hubble a t * deriv (fun s => 6 * (deriv (hubble a) s + 2 * hubble a s ^ 2)) t
              * deriv^[2] (fun x => -F (-x)) (6 * (deriv (hubble a) t + 2 * hubble a t ^ 2)) := by
  have hR : 6 * (deriv (hubble a) t + 2 * hubble a t ^ 2) = -curv a t := by unfold curv; ring
  rw [curv_std, iter2, deriv_negneg, deriv_neg_arg, hR, deriv.neg]
  simp only [neg_neg]
  unfold FriedmannEq
  rw [iter2]
  constructor <;> intro h <;> linarith

/-- The program's §XI master equation for `(a, F)` is the common-sign one for `f(x) = −F(−x)`:
`−2 f′(Rₛ) Ḣ = ρ_M + R̈ₛ f″(Rₛ) + Ṙₛ (Ṙₛ f‴(Rₛ) − H f″(Rₛ))` with `Rₛ = 6(Ḣ + 2H²)`. -/
theorem masterEq_iff_standard (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) :
    MasterEq Ω a F t₀ t ↔
      -2 * deriv (fun x => -F (-x)) (6 * (deriv (hubble a) t + 2 * hubble a t ^ 2))
          * deriv (hubble a) t =
        rhoM Ω a t₀ t
          + deriv^[2] (fun s => 6 * (deriv (hubble a) s + 2 * hubble a s ^ 2)) t
              * deriv^[2] (fun x => -F (-x)) (6 * (deriv (hubble a) t + 2 * hubble a t ^ 2))
          + deriv (fun s => 6 * (deriv (hubble a) s + 2 * hubble a s ^ 2)) t
              * (deriv (fun s => 6 * (deriv (hubble a) s + 2 * hubble a s ^ 2)) t
                  * deriv^[3] (fun x => -F (-x)) (6 * (deriv (hubble a) t + 2 * hubble a t ^ 2))
                - hubble a t
                  * deriv^[2] (fun x => -F (-x)) (6 * (deriv (hubble a) t + 2 * hubble a t ^ 2))) := by
  have hR : 6 * (deriv (hubble a) t + 2 * hubble a t ^ 2) = -curv a t := by unfold curv; ring
  rw [curv_std, iter2, iter2, iter3, deriv_negneg, deriv_neg_arg, deriv_negneg, hR, deriv.neg',
    show deriv (fun x => -deriv (curv a) x) t = -deriv (deriv (curv a)) t from deriv.neg]
  simp only [neg_neg]
  unfold MasterEq
  rw [iter2, iter2, iter3]
  constructor <;> intro h <;> linarith

end Checked.Trust.SpecAgreement
