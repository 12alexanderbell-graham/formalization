"""Necessity witnesses for the Lane-Emden, Townes and Thomas-Fermi headlines (run 2026-11-09T0628Z)."""
import sys
LE = [("Checked.Math.LaneEmden2.laneEmden2_constants", "5", "2"),
      ("Checked.Math.LaneEmden.laneEmden3_constants", "7", "3")]
TW = [("Checked.Townes.Shooting.townes_under", "2.2062008646"),
      ("Checked.Townes.Shooting.townes_over", "2.2062008647")]

def wits():
    out = []
    for full, L, n in LE:
        s = full.rsplit(".", 1)[1]
        # equation for φ dropped: θ = 1, φ = 0 never vanishes
        out.append(f"""theorem {s}_h3 : necessity% {full} 3 := by
  refine ⟨fun _ => 1, fun _ => 0, fun ξ _ => hasDerivWithinAt_const _ _ _, continuousWithinAt_const, rfl, ?_⟩
  rintro ⟨ξ₁, -, -, h, -⟩
  norm_num at h
""")
        # θ' = φ dropped: θ = 1, φ = −ξ/3 solves the φ equation
        out.append(f"""theorem {s}_h1 : necessity% {full} 1 := by
  refine ⟨fun _ => 1, fun ξ => -(ξ / 3), (continuous_id.div_const 3).neg.continuousWithinAt,
    fun ξ hξ => ?_, rfl, ?_⟩
  · have hξ0 : ξ ≠ 0 := (mem_Ioc.mp hξ).1.ne'
    exact (((hasDerivAt_id' ξ).div_const 3).neg.hasDerivWithinAt).congr_deriv (by field_simp; ring)
  · rintro ⟨ξ₁, -, -, h, -⟩
    norm_num at h
""")
        # θ 0 = 1 dropped: the zero solution
        out.append(f"""theorem {s}_h4 : necessity% {full} 4 := by
  refine ⟨fun _ => 0, fun _ => 0, fun ξ _ => hasDerivWithinAt_const _ _ _, continuousWithinAt_const,
    fun ξ _ => (hasDerivWithinAt_const _ _ _).congr_deriv (by ring), ?_⟩
  rintro ⟨ξ₁, h1, -, -, hpos, -⟩
  exact lt_irrefl _ (hpos 0 ⟨le_rfl, by linarith⟩)
""")
    for full, c in TW:
        s = full.rsplit(".", 1)[1]
        concl_under = "under" in s
        kill = ("rintro ⟨r, -, h, -⟩\n  norm_num at h" if concl_under else "rintro ⟨r, -, h, -⟩\n  norm_num at h")
        # domain length dropped: S = 0, constant solution with φ = 0
        out.append(f"""theorem {s}_h1 : necessity% {full} 1 := by
  refine ⟨0, fun _ => {c}, fun _ => 0, fun r _ => hasDerivWithinAt_const _ _ _, continuousWithinAt_const,
    fun r hr => absurd hr (by simp), rfl, ?_⟩
  {kill}
""")
        # equation for φ dropped: constant θ, φ = 0
        out.append(f"""theorem {s}_h4 : necessity% {full} 4 := by
  refine ⟨68 / 5, le_rfl, fun _ => {c}, fun _ => 0, fun r _ => hasDerivWithinAt_const _ _ _,
    continuousWithinAt_const, rfl, ?_⟩
  {kill}
""")
        # θ' = φ dropped: constant θ = c, φ = (c − c³) r / 2 solves the φ equation
        k = f"({c} - {c} ^ 3)"
        kill2 = ("rintro ⟨r, hr, h, -⟩\n    have := (mem_Ioc.mp hr).1\n    nlinarith" if concl_under else
                 "rintro ⟨r, -, h, -⟩\n    norm_num at h")
        out.append(f"""theorem {s}_h2 : necessity% {full} 2 := by
  refine ⟨68 / 5, le_rfl, fun _ => {c}, fun r => {k} * r / 2,
    ((continuous_const.mul continuous_id).div_const 2).continuousWithinAt, fun r hr => ?_, rfl, ?_⟩
  · have hr0 : r ≠ 0 := (mem_Ioc.mp hr).1.ne'
    exact ((((hasDerivAt_id' r).const_mul {k}).div_const 2).hasDerivWithinAt).congr_deriv
      (by field_simp; ring)
  · {kill2}
""")
        # θ 0 = c dropped: the zero solution
        kill3 = ("rintro ⟨r, hr, h, -⟩\n  norm_num at h" if concl_under else "rintro ⟨r, -, h, -⟩\n  norm_num at h")
        out.append(f"""theorem {s}_h5 : necessity% {full} 5 := by
  refine ⟨68 / 5, le_rfl, fun _ => 0, fun _ => 0, fun r _ => hasDerivWithinAt_const _ _ _,
    continuousWithinAt_const, fun r _ => (hasDerivWithinAt_const _ _ _).congr_deriv (by ring), ?_⟩
  {kill3}
""")
    # Thomas-Fermi: equation dropped, y = e^{-x}, φ = -e^{-x}
    out.append("""theorem tf_initial_slope_h2 : necessity% Checked.Math.ThomasFermi.tf_initial_slope 2 := by
  refine ⟨fun x => Real.exp (-x), fun x => -Real.exp (-x), fun x _ => ?_,
    (Real.continuous_exp.comp continuous_neg).neg.continuousWithinAt, by simp,
    fun x _ => Real.exp_pos _, Real.tendsto_exp_neg_atTop_nhds_zero, ?_⟩
  · exact ((hasDerivAt_neg x).exp.congr_deriv (by ring)).hasDerivWithinAt
  · norm_num
""")
    return "\n".join(out)

def stubs():
    out = []
    for full, L, n in LE:
        ns, nm = full.rsplit(".", 1)
        out.append(f"""namespace {ns}
theorem {nm} (θ φ : ℝ → ℝ)
    (hθ : ∀ ξ ∈ Icc (0 : ℝ) {L}, HasDerivWithinAt θ (φ ξ) (Icc 0 {L}) ξ)
    (hφ0 : ContinuousWithinAt φ (Icc 0 {L}) 0)
    (hφ : ∀ ξ ∈ Ioc (0 : ℝ) {L}, HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ {n}) (Icc 0 {L}) ξ)
    (h0 : θ 0 = 1) :
    ∃ ξ₁ : ℝ, 4.3528745959 ≤ ξ₁ ∧ ξ₁ ≤ 4.3528745960 ∧ θ ξ₁ = 0 ∧ (∀ ξ ∈ Ico 0 ξ₁, 0 < θ ξ) ∧
      2.4110460120 ≤ -(ξ₁ ^ 2 * φ ξ₁) := by
  sorry
end {ns}
""")
    for full, c in TW:
        ns, nm = full.rsplit(".", 1)
        concl = ("∃ r ∈ Ioc (0 : ℝ) (68 / 5), 0 < φ r ∧ ∀ s ∈ Icc 0 r, 0 < θ s" if "under" in nm else
                 "∃ r ∈ Ioc (0 : ℝ) (68 / 5), θ r < 0 ∧ ∀ s ∈ Ioc 0 r, φ s < 0")
        out.append(f"""namespace {ns}
theorem {nm} (S : ℝ) (hS : 68 / 5 ≤ S) (θ φ : ℝ → ℝ)
    (hθ : ∀ r ∈ Icc (0 : ℝ) S, HasDerivWithinAt θ (φ r) (Icc 0 S) r)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ r ∈ Ioc (0 : ℝ) S, HasDerivWithinAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) (Icc 0 S) r)
    (h0 : θ 0 = {c}) :
    {concl} := by
  sorry
end {ns}
""")
    out.append("""namespace Checked.Math.ThomasFermi
theorem tf_initial_slope (y φ : ℝ → ℝ)
    (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (h0 : y 0 = 1) (hpos : ∀ x, 0 ≤ x → 0 < y x)
    (hlim : Tendsto y atTop (𝓝 0)) :
    -1.58807103 ≤ φ 0 ∧ φ 0 ≤ -1.58807102 := by
  sorry
end Checked.Math.ThomasFermi
""")
    return "\n".join(out)

print(stubs() if sys.argv[1] == "stubs" else wits())
