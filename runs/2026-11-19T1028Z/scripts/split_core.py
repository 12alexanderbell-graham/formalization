"""One-off edit (run 2026-11-19T1028Z): move the proof of laneEmden32_constants into a helper `core`
on [0, 183/50] (the chain's range) so that a blind statement with the equation only on the open
interval can reuse it; the frozen statement is untouched."""
p = 'Work/Math/LaneEmden32.lean'
s = open(p).read()
i = s.index("/-- Lane–Emden equation of index 3/2: for every solution")
end = "      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 5.99070453 := by\n"
j = s.index(end, i) + len(end)
k = s.index("end Work.Math.LaneEmden32")
stmt, proof = s[i:j], s[j:k]
core_stmt = '''/-- The program's argument on [0, 183/50] (helper). -/
theorem core (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) (183 / 50), HasDerivWithinAt θ (φ ξ) (Icc 0 (183 / 50)) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 (183 / 50)) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) (183 / 50),
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ ((3 : ℝ) / 2)) (Icc 0 (183 / 50)) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 3.65375373 ≤ ξ₁ ∧ ξ₁ ≤ 3.65375374 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.71405511 ≤ -(ξ₁ ^ 2 * φ ξ₁) ∧ -(ξ₁ ^ 2 * φ ξ₁) ≤ 2.71405513 ∧
      5.99070450 ≤ ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ∧
      ξ₁ ^ 3 / (3 * -(ξ₁ ^ 2 * φ ξ₁)) ≤ 5.99070453 := by
'''
p2 = proof
for a, b in [("∀ ξ ∈ Ioc (0 : ℝ) 4,\n", "∀ ξ ∈ Ioc (0 : ℝ) (183 / 50),\n"),
             ("g32 (θ ξ)) (Icc 0 4) ξ", "g32 (θ ξ)) (Icc 0 (183 / 50)) ξ"),
             ("ContinuousOn θ (Icc 0 4)", "ContinuousOn θ (Icc 0 (183 / 50))"),
             ("x ∈ Ioo (0 : ℝ) 4 :=", "x ∈ Ioo (0 : ℝ) (183 / 50) :=")]:
    assert a in p2, a
    p2 = p2.replace(a, b)
main_proof = '''  have hsub : Icc (0 : ℝ) (183 / 50) ⊆ Icc 0 4 := Icc_subset_Icc le_rfl (by norm_num)
  exact core θ φ (fun ξ hξ => (hθ ξ (hsub hξ)).mono hsub) (hφ0.mono hsub)
    (fun ξ hξ => (hφ ξ ⟨hξ.1, by linarith [hξ.2]⟩).mono hsub) h0

'''
open(p, 'w').write(s[:i] + core_stmt + p2 + stmt + main_proof + s[k:])
