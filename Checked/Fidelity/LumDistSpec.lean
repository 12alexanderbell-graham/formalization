import Checked.Cosmography.BambaCurved
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Machine-checked fidelity: a specification for the luminosity distance (trust track T1)

The kernel checks proofs, not meaning. `Checked.Cosmography.BambaK.lumDist` is used by the
Checked distance theorems (F6–F8, F11); if it encoded the wrong physics, every one of those
theorems would be a correct proof about the wrong quantity. This file replaces the prose
fidelity note in `TRUSTED_DEFINITIONS.md` by Lean objects:

* `LumDistSpec D`: textbook anchors that any luminosity distance
  `D K a t₀ t` (curvature constant `K`, scale factor `a`, observer time `t₀`, emission time `t`,
  `c = 1`) must satisfy. The anchors are written from standard closed forms, independently of
  the definition: de Sitter `d_L = z(1+z)/H₀`; Milne `d_L = z(1 + z/2)/H₀`; the static closed
  universe `d_L = R sin χ`; invariance under the normalization of the scale factor.
* `lumDist_meets_spec`: the program's definition satisfies the specification.
* A mutation benchmark: ten plausible wrong definitions (the errors people and models make),
  each refuted against the specification in Lean (`reject_*`). Kill rate 10/10.

A definition that meets a specification which rejects every listed mutant is trusted at the
level of that specification, with no human or subagent judgement in the loop. Surviving
mutants, when found, name the gaps of the specification.

Conventions: `c = 1`; `t < t₀` is the past; `1 + z = a(t₀)/a(t)`.
-/

namespace Checked.Fidelity

open Real Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.Transverse
open Checked.Cosmography.BambaK

/-- Specification of a luminosity-distance function `D K a t₀ t`. -/
structure LumDistSpec (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- Flat de Sitter (`a = eᵗ`, `H₀ = 1`, `t₀ = 0`): `d_L = z(1+z)` with `1 + z = e^{−t}`. -/
  deSitter : ∀ t ≤ 0, D 0 Real.exp 0 t = (Real.exp (-t) - 1) * Real.exp (-t)
  /-- Milne (`a = t`, `K = −1`, `t₀ = 1`, `H₀ = 1`): `d_L = z(1 + z/2) = ((1+z)² − 1)/2`,
  `1 + z = 1/t`. -/
  milne : ∀ t, 0 < t → t ≤ 1 → D (-1) id 1 t = ((1 / t) ^ 2 - 1) / 2
  /-- Static closed universe (`a ≡ 1`, `K = 1`): `d_L = sin χ`, `χ = t₀ − t`. -/
  staticClosed : ∀ t₀ t, t ≤ t₀ → D 1 (fun _ => 1) t₀ t = Real.sin (t₀ - t)
  /-- The normalization of `a` is unphysical: `a ↦ c a`, `K ↦ c² K` leaves `d_L` unchanged. -/
  rescale : ∀ c : ℝ, 0 < c → ∀ K a t₀ t, D (c ^ 2 * K) (fun s => c * a s) t₀ t = D K a t₀ t

/-! ## The program's definition meets the specification -/

lemma transverse_rescale (c K χ : ℝ) (hc : 0 < c) :
    transverse (c ^ 2 * K) (χ / c) = transverse K χ / c := by
  have hc0 : c ≠ 0 := hc.ne'
  unfold transverse
  rcases lt_trichotomy K 0 with hK | hK | hK
  · have h1 : ¬ 0 < c ^ 2 * K := by nlinarith [sq_pos_of_pos hc]
    have h2 : c ^ 2 * K < 0 := by nlinarith [sq_pos_of_pos hc]
    have hs : Real.sqrt (-(c ^ 2 * K)) = c * Real.sqrt (-K) := by
      rw [show -(c ^ 2 * K) = c ^ 2 * (-K) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq hc.le]
    have hsK : 0 < Real.sqrt (-K) := Real.sqrt_pos.2 (by linarith)
    simp only [h1, h2, ite_false, ite_true, not_lt.2 hK.le, hK, hs]
    rw [show c * Real.sqrt (-K) * (χ / c) = Real.sqrt (-K) * χ by field_simp]
    field_simp
  · subst hK; simp
  · have h1 : 0 < c ^ 2 * K := by positivity
    have hs : Real.sqrt (c ^ 2 * K) = c * Real.sqrt K := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]
    have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
    simp only [h1, hK, ite_true, hs]
    rw [show c * Real.sqrt K * (χ / c) = Real.sqrt K * χ by field_simp]
    field_simp

lemma comoving_rescale (c : ℝ) (hc : 0 < c) (a : ℝ → ℝ) (t₀ t : ℝ) :
    comoving (fun s => c * a s) t₀ t = comoving a t₀ t / c := by
  unfold comoving
  have : (fun s => 1 / (c * a s)) = fun s => c⁻¹ * (1 / a s) := by
    funext s; rw [one_div, one_div, mul_inv]
  rw [this, intervalIntegral.integral_const_mul]; ring

lemma redshift_rescale (c : ℝ) (hc : 0 < c) (a : ℝ → ℝ) (t₀ t : ℝ) :
    redshift (fun s => c * a s) t₀ t = redshift a t₀ t := by
  unfold redshift; rw [mul_div_mul_left _ _ hc.ne']

lemma comoving_exp (t : ℝ) : comoving Real.exp 0 t = Real.exp (-t) - 1 := by
  unfold comoving
  have : (fun s => 1 / Real.exp s) = fun s => Real.exp (-s) := by
    funext s; rw [Real.exp_neg, one_div]
  rw [this, intervalIntegral.integral_comp_neg (fun s => Real.exp s), integral_exp]
  simp

lemma comoving_id (t : ℝ) (ht : 0 < t) : comoving id 1 t = Real.log (1 / t) := by
  unfold comoving; simpa using integral_one_div_of_pos ht one_pos

lemma comoving_one (t₀ t : ℝ) : comoving (fun _ => 1) t₀ t = t₀ - t := by
  unfold comoving; simp

lemma sinh_log (x : ℝ) (hx : 0 < x) : Real.sinh (Real.log x) = (x - 1 / x) / 2 := by
  rw [Real.sinh_eq, Real.exp_log hx, Real.exp_neg, Real.exp_log hx, one_div]

theorem lumDist_meets_spec : LumDistSpec lumDist where
  deSitter t _ := by
    simp only [lumDist, transverse, lt_irrefl, ite_false, comoving_exp, redshift,
      Real.exp_zero]
    rw [Real.exp_neg]; field_simp; ring
  milne t ht _ := by
    have hl : 0 < 1 / t := by positivity
    simp only [lumDist, transverse, comoving_id t ht, redshift, id]
    norm_num
    rw [sinh_log _ (by positivity)]
    field_simp; ring
  staticClosed t₀ t _ := by
    simp [lumDist, transverse, comoving_one, redshift]
  rescale c hc K a t₀ t := by
    simp only [lumDist]
    rw [redshift_rescale c hc, comoving_rescale c hc, transverse_rescale c K _ hc]
    field_simp [hc.ne']

/-! ## Mutation benchmark: plausible wrong definitions, each rejected by the specification -/

/-- M1: transverse comoving distance, no `(1+z)` (confuses d_M with d_L). -/
noncomputable def mComoving (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * transverse K (comoving a t₀ t)
/-- M2: angular-diameter distance (divides by `1+z` instead of multiplying). -/
noncomputable def mAngular (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * transverse K (comoving a t₀ t) / (1 + redshift a t₀ t)
/-- M3: `(1+z)²` (surface-brightness factor applied to the distance). -/
noncomputable def mDoubleZ (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t₀ t) ^ 2 * transverse K (comoving a t₀ t)
/-- M4: missing `a₀` (silently assumes `a(t₀) = 1`). -/
noncomputable def mNoA0 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  (1 + redshift a t₀ t) * transverse K (comoving a t₀ t)
/-- M5: `∫ a dt` instead of `∫ dt/a`. -/
noncomputable def mIntA (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t₀ t) * transverse K (∫ s in t..t₀, a s)
/-- M6: integration limits reversed (`∫_{t₀}^{t}`). -/
noncomputable def mReversed (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t₀ t) * transverse K (∫ s in t₀..t, 1 / a s)
/-- M7: curvature sign convention flipped (sin for open, sinh for closed). -/
noncomputable def mSignK (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t₀ t) * transverse (-K) (comoving a t₀ t)
/-- M8: flat formula used for every curvature. -/
noncomputable def mFlatOnly (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t₀ t) * comoving a t₀ t
/-- `S_K` without the `1/√|K|` prefactor. -/
noncomputable def transNoDiv (K χ : ℝ) : ℝ :=
  if 0 < K then Real.sin (Real.sqrt K * χ)
  else if K < 0 then Real.sinh (Real.sqrt (-K) * χ) else χ
/-- M9: `S_K` without the `1/√|K|` prefactor (correct only for `|K| = 1`). -/
noncomputable def mNoSqrtDiv (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t₀ t) * transNoDiv K (comoving a t₀ t)
/-- M10: redshift inverted (`1 + z = a/a₀`). -/
noncomputable def mInvRedshift (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (a t / a t₀) * transverse K (comoving a t₀ t)

/-- The de Sitter test point `t = −log 2` (`z = 1`). -/
lemma exp_neg_negLog2 : Real.exp (-(-Real.log 2)) = 2 := by
  rw [neg_neg, Real.exp_log two_pos]

lemma deSitter_at (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : LumDistSpec D) :
    D 0 Real.exp 0 (-Real.log 2) = 2 := by
  rw [h.deSitter _ (by linarith [Real.log_pos one_lt_two]), exp_neg_negLog2]; norm_num

lemma red_exp : redshift Real.exp 0 (-Real.log 2) = 1 := by
  simp only [redshift, Real.exp_zero, Real.exp_neg, Real.exp_log two_pos]; norm_num

lemma com_exp : comoving Real.exp 0 (-Real.log 2) = 1 := by
  rw [comoving_exp, exp_neg_negLog2]; norm_num

theorem reject_mComoving : ¬ LumDistSpec mComoving := fun h => by
  have := deSitter_at _ h
  simp [mComoving, transverse, com_exp] at this

theorem reject_mAngular : ¬ LumDistSpec mAngular := fun h => by
  have := deSitter_at _ h
  simp [mAngular, transverse, com_exp, red_exp] at this; norm_num at this

theorem reject_mDoubleZ : ¬ LumDistSpec mDoubleZ := fun h => by
  have := deSitter_at _ h
  simp [mDoubleZ, transverse, com_exp, red_exp] at this; norm_num at this

theorem reject_mIntA : ¬ LumDistSpec mIntA := fun h => by
  have := deSitter_at _ h
  simp only [mIntA, transverse, lt_irrefl, ite_false, red_exp, integral_exp, Real.exp_zero,
    Real.exp_neg, Real.exp_log two_pos] at this
  norm_num at this

theorem reject_mReversed : ¬ LumDistSpec mReversed := fun h => by
  have := deSitter_at _ h
  have hc : (∫ s in (0 : ℝ)..(-Real.log 2), 1 / Real.exp s) = -1 := by
    rw [intervalIntegral.integral_symm]
    have := com_exp; unfold comoving at this; rw [this]
  simp only [mReversed, transverse, lt_irrefl, ite_false, red_exp, hc] at this
  norm_num at this

theorem reject_mInvRedshift : ¬ LumDistSpec mInvRedshift := fun h => by
  have := deSitter_at _ h
  simp only [mInvRedshift, transverse, lt_irrefl, ite_false, com_exp, Real.exp_zero,
    Real.exp_neg, Real.exp_log two_pos] at this
  norm_num at this

/-! Milne test point `t = 1/2` (`z = 1`): `d_L = 3/2`. -/

lemma milne_at (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : LumDistSpec D) : D (-1) id 1 (1 / 2) = 3 / 2 := by
  rw [h.milne _ (by norm_num) (by norm_num)]; norm_num

lemma com_id_half : comoving id 1 (1 / 2) = Real.log 2 := by
  rw [comoving_id _ (by norm_num)]; norm_num

lemma red_id_half : redshift id 1 (1 / 2) = 1 := by
  simp [redshift]; norm_num

theorem reject_mFlatOnly : ¬ LumDistSpec mFlatOnly := fun h => by
  have := milne_at _ h
  simp only [mFlatOnly, com_id_half, red_id_half, id] at this
  have := Real.log_two_lt_d9
  norm_num at *; linarith

theorem reject_mSignK : ¬ LumDistSpec mSignK := fun h => by
  have := milne_at _ h
  simp only [mSignK, transverse, com_id_half, red_id_half, id, neg_neg, Real.sqrt_one,
    one_mul, div_one] at this
  norm_num at this
  have h1 := Real.sin_lt (Real.log_pos one_lt_two)
  have h2 := Real.log_two_lt_d9
  norm_num at h2; linarith

/-! Rescaled Milne (`a = 2t`, `K = −4`): the specification forces `d_L = 3/2` again. -/

lemma rescaled_milne_at (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : LumDistSpec D) :
    D (-4) (fun s => 2 * id s) 1 (1 / 2) = 3 / 2 := by
  have := h.rescale 2 two_pos (-1) id 1 (1 / 2)
  simp only [id] at this ⊢
  norm_num at this
  rw [this]; exact milne_at D h

lemma com_2id_half : comoving (fun s => 2 * id s) 1 (1 / 2) = Real.log 2 / 2 := by
  rw [comoving_rescale 2 two_pos, com_id_half]

lemma red_2id_half : redshift (fun s => 2 * id s) 1 (1 / 2) = 1 := by
  rw [redshift_rescale 2 two_pos, red_id_half]

lemma sinh_log2 : Real.sinh (Real.log 2) = 3 / 4 := by
  rw [sinh_log 2 two_pos]; norm_num

theorem reject_mNoA0 : ¬ LumDistSpec mNoA0 := fun h => by
  have := rescaled_milne_at _ h
  have hs : Real.sqrt (-(-4 : ℝ)) = 2 := by
    rw [neg_neg, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [mNoA0, transverse, com_2id_half, red_2id_half, hs] at this
  norm_num at this
  rw [show 2 * (Real.log 2 / 2) = Real.log 2 by ring, sinh_log2] at this
  norm_num at this

theorem reject_mNoSqrtDiv : ¬ LumDistSpec mNoSqrtDiv := fun h => by
  have := rescaled_milne_at _ h
  have hs : Real.sqrt (-(-4 : ℝ)) = 2 := by
    rw [neg_neg, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [mNoSqrtDiv, transNoDiv, com_2id_half, red_2id_half, hs] at this
  norm_num at this
  rw [show 2 * (Real.log 2 / 2) = Real.log 2 by ring, sinh_log2] at this
  norm_num at this

end Checked.Fidelity
