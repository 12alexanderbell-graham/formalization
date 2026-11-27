import Mathlib
import Readings.Henon
import ComparatorChallenges.HenonEmden

/-! # Target O, family O30 (the subcritical Hénon–Lane–Emden conjecture): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped: for n ≥ 2, p, q > 0 and (n+A)/(p+1) + (n+B)/(q+1) > n − 2, no
continuous, C² off the origin, positive u, v on `EuclideanSpace ℝ (Fin n)` with −Δu = |x|^A v^p, −Δv = |x|^B u^q at
every x ≠ 0 (Mathlib's `Laplacian.laplacian`). Closed (frozen ⇒ reading), every reader: Theorem 1.1 (the same
statement), and Corollary 1.2 from the frozen theorem at A = B = 0 (n ≥ 3; the hypothesis times n is the
subcritical one; a C² solution on ℝⁿ is one off the origin; |x|⁰ = 1). -/

namespace TargetO.Henon

open OAI.HenonLaneEmden

/-- The frozen theorem in unpacked form. -/
theorem unpacked (h : type_of% @OAI.HenonLaneEmden.main_nonexistence) (n : ℕ) (hn : 2 ≤ n) (p q A B : ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hsub : ((n : ℝ) + A) / (p + 1) + ((n : ℝ) + B) / (q + 1) > (n : ℝ) - 2)
    (u v : EuclideanSpace ℝ (Fin n) → ℝ) (hu : ContDiffOn ℝ 2 u {0}ᶜ) (hv : ContDiffOn ℝ 2 v {0}ᶜ)
    (hcu : Continuous u) (hcv : Continuous v) (pu : ∀ x, 0 < u x) (pv : ∀ x, 0 < v x)
    (eu : ∀ x, x ≠ 0 → -(Laplacian.laplacian u) x = ‖x‖ ^ A * (v x) ^ p)
    (ev : ∀ x, x ≠ 0 → -(Laplacian.laplacian v) x = ‖x‖ ^ B * (u x) ^ q) : False := by
  refine h n hn p q A B hp hq (by unfold Subcritical; norm_num; linarith) ⟨u, v, ?_⟩
  exact ⟨hcu, hcv, hu, hv, pu, pv, eu, ev⟩

/-- Corollary 1.2 from the frozen theorem. -/
theorem cor (h : type_of% @OAI.HenonLaneEmden.main_nonexistence) (n : ℕ) (hn : 3 ≤ n) (p q : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hsub : 1 / (p + 1) + 1 / (q + 1) > ((n : ℝ) - 2) / n)
    (u v : EuclideanSpace ℝ (Fin n) → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (pu : ∀ x, 0 < u x) (pv : ∀ x, 0 < v x)
    (eu : ∀ x, -(Laplacian.laplacian u) x = (v x) ^ p) (ev : ∀ x, -(Laplacian.laplacian v) x = (u x) ^ q) :
    False := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsub' : ((n : ℝ) + 0) / (p + 1) + ((n : ℝ) + 0) / (q + 1) > (n : ℝ) - 2 := by
    have := mul_lt_mul_of_pos_left hsub hn0
    rw [mul_div_cancel₀ _ hn0.ne'] at this
    simp only [add_zero]
    calc (n : ℝ) - 2 < n * (1 / (p + 1) + 1 / (q + 1)) := this
      _ = n / (p + 1) + n / (q + 1) := by ring
  exact unpacked h n (by omega) p q 0 0 hp hq hsub' u v hu.contDiffOn hv.contDiffOn hu.continuous
    hv.continuous pu pv (fun x _ => by rw [Real.rpow_zero, one_mul]; exact eu x)
    (fun x _ => by rw [Real.rpow_zero, one_mul]; exact ev x)

theorem A_thm : (type_of% @OAI.HenonLaneEmden.main_nonexistence) → (type_of% @ReaderA.reading_thm_1_1) := by
  rintro h n hn p q hp hq A B hsub ⟨u, v, ⟨hu, hcu⟩, ⟨hv, hcv⟩, pu, pv, he⟩
  exact unpacked h n hn p q A B hp hq hsub u v hu hv hcu hcv pu pv (fun x hx => (he x hx).1)
    (fun x hx => (he x hx).2)

theorem A_cor : (type_of% @OAI.HenonLaneEmden.main_nonexistence) → (type_of% @ReaderA.reading_cor_1_2) := by
  rintro h n hn p q hp hq hsub ⟨u, v, hu, hv, pu, pv, he⟩
  exact cor h n hn p q hp hq hsub u v hu hv pu pv (fun x => (he x).1) (fun x => (he x).2)

theorem B_thm : (type_of% @OAI.HenonLaneEmden.main_nonexistence) →
    (type_of% @ReaderB.reading_henon_theorem_1_1) := by
  rintro h n hn p q A B hp hq hsub ⟨u, v, hu, hv, hcu, hcv, pu, pv, he⟩
  exact unpacked h n hn p q A B hp hq hsub u v hu hv hcu hcv pu pv (fun x hx => (he x hx).1)
    (fun x hx => (he x hx).2)

theorem B_cor : (type_of% @OAI.HenonLaneEmden.main_nonexistence) →
    (type_of% @ReaderB.reading_henon_corollary_1_2) := by
  rintro h n hn p q hp hq hsub ⟨u, v, hu, hv, pu, pv, he⟩
  exact cor h n hn p q hp hq hsub u v hu hv pu pv (fun x => (he x).1) (fun x => (he x).2)

theorem C_thm : (type_of% @OAI.HenonLaneEmden.main_nonexistence) →
    (type_of% @ReaderC.reading_henon_thm11) := by
  rintro h n hn p q A B hp hq hsub ⟨u, v, hu, hcu, hv, hcv, pu, pv, he⟩
  exact unpacked h n hn p q A B hp hq hsub u v hu hv hcu hcv pu pv (fun x hx => (he x hx).1)
    (fun x hx => (he x hx).2)

theorem C_cor : (type_of% @OAI.HenonLaneEmden.main_nonexistence) →
    (type_of% @ReaderC.reading_henon_cor12) := by
  rintro h n hn p q hp hq hsub ⟨u, v, hu, hv, pu, pv, he⟩
  exact cor h n hn p q hp hq hsub u v hu hv pu pv (fun x => (he x).1) (fun x => (he x).2)

end TargetO.Henon

#print axioms TargetO.Henon.A_thm
#print axioms TargetO.Henon.A_cor
#print axioms TargetO.Henon.B_thm
#print axioms TargetO.Henon.B_cor
#print axioms TargetO.Henon.C_thm
#print axioms TargetO.Henon.C_cor
