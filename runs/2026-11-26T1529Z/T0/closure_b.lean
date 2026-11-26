import Readings.T0

open Complex Matrix
namespace ExternalT0
open T0

lemma expect_eq (M : Matrix Fock Fock ℂ) : expect M = M 0 0 := by
  simp [expect, vac, dotProduct, Matrix.mulVec, Pi.single_apply]

lemma expect2_eq (M : Matrix Fock2 Fock2 ℂ) : expect2 M = M (0, 0) (0, 0) := by
  simp [expect2, vac2, dotProduct, Matrix.mulVec, Pi.single_apply]

/-- `𝔞 + 𝔞†` on the first rows/columns needed. -/
noncomputable def X : Matrix Fock Fock ℂ := ann + cre

lemma XX_row0 (m : Fock) : (X * X) 0 m = if m = 0 then 1 else if m = 2 then (Real.sqrt 2 : ℂ) else 0 := by
  fin_cases m <;>
  simp [X, Matrix.mul_apply, Fin.sum_univ_succ, ann, cre, Matrix.conjTranspose_apply]

lemma XX_col0 (m : Fock) : (X * X) m 0 = if m = 0 then 1 else if m = 2 then (Real.sqrt 2 : ℂ) else 0 := by
  fin_cases m <;>
  simp [X, Matrix.mul_apply, Fin.sum_univ_succ, ann, cre, Matrix.conjTranspose_apply]


lemma qq (σ : ℝ) : qop σ * qop σ = ((σ : ℂ) ^ 2) • (X * X) := by
  simp only [qop, X, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]

lemma single_eq (σ θ : ℝ) :
    conn1 (rot θ * qop σ * qop σ * (rot θ).conjTranspose) (qop σ * qop σ)
      = 2 * (σ : ℂ) ^ 4 * Complex.exp (-(2 * Complex.I * θ)) := by
  have hA : rot θ * qop σ * qop σ * (rot θ).conjTranspose
      = rot θ * (qop σ * qop σ) * (rot θ).conjTranspose := by simp [Matrix.mul_assoc]
  rw [hA, qq, conn1, expect_eq, expect_eq, expect_eq, Matrix.mul_apply]
  simp only [rot, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.smul_apply, XX_row0, XX_col0, Fin.sum_univ_succ]
  simp
  rw [← Complex.exp_conj]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have he : (starRingEnd ℂ) (Complex.I * θ * 2) = -(2 * Complex.I * θ) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]; ring
  rw [he]
  linear_combination ((σ : ℂ) ^ 4 * Complex.exp (-(2 * Complex.I * θ))) * h2

lemma conn2_zero (A B : Matrix Fock Fock ℂ) : conn2 (onFirst A) (onSecond B) = 0 := by
  have h : onFirst A * onSecond B = Matrix.kroneckerMap (· * ·) A B := by
    unfold onFirst onSecond
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [conn2, h, expect2_eq, expect2_eq, expect2_eq]
  simp [onFirst, onSecond, Matrix.kroneckerMap_apply]

theorem single_mode' : type_of% @T0.single_mode := by
  intro s hs
  refine ⟨fun k hk => ?_, fun j k _ _ _ => conn2_zero _ _⟩
  rw [single_eq]
  have hv : 0 ≤ variance s k := by unfold variance; positivity
  have hσ : ((Real.sqrt (variance s k) : ℝ) : ℂ) ^ 4 = (((variance s k) ^ 2 : ℝ) : ℂ) := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, ← Complex.ofReal_pow, Real.sq_sqrt hv]; push_cast; ring
  rw [hσ]; unfold pairPhase; congr 2; push_cast; ring

end ExternalT0
#print axioms ExternalT0.single_mode'
