"""Emit the frozen statement of gelfand_pde_radial_count_turning (run 2026-11-18T2228Z).
Usage: python3 gen_count_all.py <namespace prefix Work|Checked> <proof term> > file"""
import sys
pre, proof = sys.argv[1], sys.argv[2]
E = "EuclideanSpace ℝ (Fin 3)"
def N(mu):
    return (f"{{g : closedBall (0 : {E}) 1 → ℝ | ∃ u : {E} → ℝ,\n"
            f"          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧\n"
            f"          (∀ x : {E}, ‖x‖ = 1 → u x = 0) ∧\n"
            f"          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : {E}) 1, u x = h ‖x‖) ∧\n"
            f"          (∀ x ∈ ball (0 : {E}) 1, Δ u x + {mu} * Real.exp (u x) = 0)) ∧\n"
            f"          ∀ x : closedBall (0 : {E}) 1, g x = u x}}.encard")
name = sys.argv[3] if len(sys.argv) > 3 else "gelfand_pde_radial_count_turning"
stmt = f"""theorem {name} :
    ∃ lamT : ℕ → ℝ,
      3.321992118 ≤ lamT 0 ∧ lamT 0 ≤ 3.321992119 ∧
      1.664155 ≤ lamT 1 ∧ lamT 1 ≤ 1.664157 ∧ 2.10852 ≤ lamT 2 ∧ lamT 2 ≤ 2.10858 ∧
      StrictAnti (fun k : ℕ => lamT (2 * k)) ∧ StrictMono (fun k : ℕ => lamT (2 * k + 1)) ∧
      (∀ k : ℕ, lamT (2 * k + 1) < 2 ∧ 2 < lamT (2 * k)) ∧
      Tendsto lamT atTop (𝓝 2) ∧
      (∀ lam : ℝ, lamT 0 < lam →
        {N('lam')} = 0) ∧
      {N('lamT 0')} = 1 ∧
      (∀ k : ℕ, ∀ lam : ℝ, lamT (2 * k + 2) < lam → lam < lamT (2 * k) →
        {N('lam')} = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ,
        {N('lamT (2 * k + 2)')} = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      (∀ lam : ℝ, 0 < lam → lam < lamT 1 →
        {N('lam')} = 1) ∧
      (∀ k : ℕ,
        {N('lamT (2 * k + 1)')} = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ, ∀ lam : ℝ, lamT (2 * k + 1) < lam → lam < lamT (2 * k + 3) →
        {N('lam')} = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      {N('2')} = ⊤ :=
  {proof}"""
print(stmt)
