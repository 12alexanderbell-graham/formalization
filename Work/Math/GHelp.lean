import Mathlib

/-!
# Gelfand problem: small helper lemmas for the certificates

Taylor bounds of the exponential (from `Real.exp_bound`), a crude bound `exp x ≤ 2`, and the
extension of the positivity of p(s) = 2 + s φ(s) from (0, c] to (0, a] when p is decreasing on
[c, b] (p' = −(φ + s e^w) < 0) and p(a) > 0.
-/

namespace Work.Math.GHelp
open Set

theorem exp_T4 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6)| ≤ |x| ^ 4 * (5 / 96) := by
  have h := Real.exp_bound hx (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  convert h using 2

theorem exp_T6 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120)| ≤
      |x| ^ 6 * (7 / 4320) := by
  have h := Real.exp_bound hx (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  convert h using 2

theorem exp_le_two {x : ℝ} (hx : |x| ≤ 1 / 2) : Real.exp x ≤ 2 := by
  have h := Real.exp_bound (x := x) (by linarith) (n := 1) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have := (abs_le.1 h).2
  linarith

theorem derivs_at' {S : ℝ} {w φ : ℝ → ℝ}
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    {s : ℝ} (hs : s ∈ Ioo 0 S) :
    HasDerivAt w (φ s) s ∧ HasDerivAt φ (-(2 / s * φ s) - Real.exp (w s)) s :=
  ⟨(hw s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2),
    (hφ s ⟨hs.1, hs.2.le⟩).hasDerivAt (Icc_mem_nhds hs.1 hs.2)⟩

theorem hasDerivAt_p' {w φ : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0)
    (hφ : HasDerivAt φ (-(2 / s * φ s) - Real.exp (w s)) s) :
    HasDerivAt (fun t => 2 + t * φ t) (-(φ s + s * Real.exp (w s))) s := by
  have h := ((hasDerivAt_id' s).mul hφ).const_add 2
  convert h using 1
  field_simp
  ring

theorem pos_extend {S c a b : ℝ} {w φ : ℝ → ℝ} (hc0 : 0 < c) (hca : c ≤ a) (hab : a ≤ b)
    (hbS : b < S)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S, HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (hpos : ∀ s ∈ Ioc (0 : ℝ) c, 0 < 2 + s * φ s)
    (hdec : ∀ s ∈ Icc c b, 0 < φ s + s * Real.exp (w s))
    (hpa : 0 < 2 + a * φ a) : ∀ s ∈ Ioc (0 : ℝ) a, 0 < 2 + s * φ s := by
  intro s hs
  rcases le_or_gt s c with h | h
  · exact hpos s ⟨hs.1, h⟩
  · -- p is strictly antitone on [c, b]
    have hcont : ContinuousOn (fun t => 2 + t * φ t) (Icc c b) := by
      intro t ht
      have htS : t ∈ Ioc (0 : ℝ) S := ⟨hc0.trans_le ht.1, ht.2.trans hbS.le⟩
      have hsub : Icc c b ⊆ Icc 0 S := Icc_subset_Icc hc0.le hbS.le
      have := ((continuousWithinAt_id (s := Icc c b) (x := t)).mul
        ((hφ t htS).continuousWithinAt.mono hsub)).const_add 2
      simpa using this
    have hanti : StrictAntiOn (fun t => 2 + t * φ t) (Icc c b) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc c b) hcont
      intro x hx
      rw [interior_Icc] at hx
      have hxS : x ∈ Ioo (0 : ℝ) S := ⟨hc0.trans hx.1, hx.2.trans hbS⟩
      have hd := hasDerivAt_p' (w := w) hxS.1.ne' (derivs_at' hw hφ hxS).2
      rw [hd.deriv]
      have := hdec x ⟨hx.1.le, hx.2.le⟩
      linarith
    rcases eq_or_lt_of_le hs.2 with he | hlt
    · rw [he]; exact hpa
    · have := hanti ⟨h.le, hs.2.trans hab⟩ ⟨hca, hab⟩ hlt
      simp only at this
      linarith

end Work.Math.GHelp
