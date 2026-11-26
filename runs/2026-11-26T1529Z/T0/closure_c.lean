import Readings.T0

open Complex Finset
namespace ExternalT0
open T0

/-- The family `G ↦ Σ_k b_k (p0_k + p1_k G + p2_k G²) e^{a_k G}` is closed under `d/dG`. -/
noncomputable def Φ (I : Finset ℕ) (a b p0 p1 p2 : ℕ → ℂ) (G : ℝ) : ℂ :=
  ∑ k ∈ I, b k * ((p0 k + p1 k * G + p2 k * (G : ℂ) ^ 2) * Complex.exp (a k * G))

lemma step (I : Finset ℕ) (a b p0 p1 p2 : ℕ → ℂ) :
    deriv (Φ I a b p0 p1 p2) =
      Φ I a b (fun k => p1 k + a k * p0 k) (fun k => 2 * p2 k + a k * p1 k) (fun k => a k * p2 k) := by
  funext G
  apply HasDerivAt.deriv
  unfold Φ
  apply HasDerivAt.fun_sum
  intro k _
  have hx : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 G := (hasDerivAt_id G).ofReal_comp
  have hpoly : HasDerivAt (fun x : ℝ => p0 k + p1 k * (x : ℂ) + p2 k * (x : ℂ) ^ 2)
      (p1 k * 1 + p2 k * (2 * (G : ℂ) ^ 1 * 1)) G := by
    have h2 := hx.pow 2
    have := ((hx.const_mul (p1 k)).const_add (p0 k)).add (h2.const_mul (p2 k))
    convert this using 1
  have hexp : HasDerivAt (fun x : ℝ => Complex.exp (a k * x)) (Complex.exp (a k * G) * (a k * 1)) G :=
    (hx.const_mul (a k)).cexp
  convert (hpoly.mul hexp).const_mul (b k) using 1
  ring

lemma Φ_zero (I : Finset ℕ) (a b p0 p1 p2 : ℕ → ℂ) : Φ I a b p0 p1 p2 0 = ∑ k ∈ I, b k * p0 k := by
  simp [Φ]

theorem eq_4_34' : type_of% @T0.eq_4_34 := by
  intro area hbar hA hh N
  intro c f
  have hc : c ≠ 0 := by simp only [c]; positivity
  set a : ℕ → ℂ := fun k => -(2 * Complex.I * k * c) with ha
  set b : ℕ → ℂ := fun k => (c : ℂ) ^ 2 / 2 / (k : ℂ) ^ 2 with hb
  have hf : f = Φ (Finset.Icc 1 N) a b (fun _ => 0) (fun _ => 0) (fun _ => 1) := by
    funext G; simp only [f, Φ, a, b]; apply Finset.sum_congr rfl; intro k _
    push_cast; ring_nf
  have h3 : iteratedDeriv 3 f 0 = ∑ k ∈ Finset.Icc 1 N, b k * (6 * a k) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero, hf,
      step, step, step, Φ_zero]
    apply Finset.sum_congr rfl; intro k _; ring
  have hmain : iteratedDeriv 3 f 0 / 6 = -(Complex.I * (c : ℂ) ^ 3) * ∑ k ∈ Finset.Icc 1 N, (1 : ℂ) / k := by
    rw [h3, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl; intro k hk
    have hk0 : (k : ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hk).1; exact_mod_cast (show k ≠ 0 by omega)
    simp only [a, b]; field_simp
  refine ⟨hmain, fun G hG => ?_⟩
  rw [hmain]
  have hs : ((sOf area G hbar : ℝ) : ℂ) = 1 / ((c : ℂ) * G) := by
    simp only [sOf, c]; push_cast
    have : (area : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
    have : (hbar : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    have : (G : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
    field_simp
  rw [hs]
  have : (G : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
  have : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  field_simp

end ExternalT0
#print axioms ExternalT0.eq_4_34'
