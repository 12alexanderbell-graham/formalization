/-! Check on the reading (run 2026-11-26T0828Z): `decidedParts` on the honest bench readings and on the readings of
the closure forgeries of red team BB and of this run. -/
/-! Bench of honest parametric closures (run 2026-11-26T0828Z, part 3): the bridges of run 2026-11-26T0228Z's bench
(`runs/2026-11-26T0228Z/t5/bench_body.lean`, same blind readings) restated as `∀ c, X ↔ H[c]` with every real
literal of the headline other than 0 and 1 a variable, and a `.bite` theorem `¬ ∀ c, H[c]` each. Run with
`runs/2026-11-26T0828Z/scripts/run_pclosure.sh <rule> runs/2026-11-26T0828Z/t5/pbench_body.lean`. -/

open Set Filter Topology Metric InnerProductSpace Laplacian

namespace PBench

namespace SecondReading
/-- Blind reader, Hiemenz (`Work/Hiemenz/HiemenzBlind.lean`). -/
def HiemenzODE (S : Set ℝ) (f f1 f2 f3 : ℝ → ℝ) : Prop :=
  (∀ t ∈ S, HasDerivWithinAt f (f1 t) S t) ∧
  (∀ t ∈ S, HasDerivWithinAt f1 (f2 t) S t) ∧
  (∀ t ∈ S, HasDerivWithinAt f2 (f3 t) S t) ∧
  (∀ t ∈ S, f3 t + f t * f2 t + 1 - (f1 t) ^ 2 = 0)

def hiemenzExists : Prop :=
  ∃ f f1 f2 f3 : ℝ → ℝ, HiemenzODE (Ici 0) f f1 f2 f3 ∧
    f 0 = 0 ∧ f1 0 = 0 ∧ Tendsto f1 atTop (𝓝 1) ∧
    (1.2325876568 : ℝ) < f2 0 ∧ f2 0 < 1.2325876569

def hiemenzUnder : Prop :=
  ∀ f f1 f2 f3 : ℝ → ℝ, HiemenzODE (Icc 0 7.5) f f1 f2 f3 →
    f 0 = 0 → f1 0 = 0 → f2 0 = 1.2325876568 →
    ∃ η : ℝ, 0 < η ∧ η ≤ 7.5 ∧ f2 η < 0 ∧ ∀ s ∈ Icc 0 η, f1 s < 1

/-- Blind reader, Homann (`Work/Homann/HomannBlind.lean`). -/
def HomannSol (S : Set ℝ) (f f1 f2 f3 : ℝ → ℝ) : Prop :=
  (∀ x ∈ S, HasDerivWithinAt f (f1 x) S x) ∧
  (∀ x ∈ S, HasDerivWithinAt f1 (f2 x) S x) ∧
  (∀ x ∈ S, HasDerivWithinAt f2 (f3 x) S x) ∧
  (∀ x ∈ S, f3 x + 2 * f x * f2 x + 1 - (f1 x) ^ 2 = 0)

def homannExists : Prop :=
  ∃ f f1 f2 f3 : ℝ → ℝ, HomannSol (Set.Ici 0) f f1 f2 f3 ∧
    f 0 = 0 ∧ f1 0 = 0 ∧ Filter.Tendsto f1 Filter.atTop (nhds 1) ∧
    1.3119376938 < f2 0 ∧ f2 0 < 1.3119376939

/-- Blind reader, Gelfand bound (`Work/Math/GelfandPDEBoundBlind.lean`). -/
def IsClassicalGelfandSolution (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
  ContinuousOn u (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
  (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Laplacian.laplacian u x + lam * Real.exp (u x) = 0) ∧
  (∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = 0)

def gelfandBound : Prop :=
  ∀ lam : ℝ, (∃ u : EuclideanSpace ℝ (Fin 3) → ℝ, IsClassicalGelfandSolution lam u) → lam ≤ 3.321992119

end SecondReading

/-! ## B1: Hiemenz existence -/
theorem c_hiemenz_exists : ∀ a b : ℝ, (∃ f f1 f2 f3 : ℝ → ℝ, SecondReading.HiemenzODE (Ici 0) f f1 f2 f3 ∧
    f 0 = 0 ∧ f1 0 = 0 ∧ Tendsto f1 atTop (𝓝 1) ∧ a < f2 0 ∧ f2 0 < b) ↔ ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    a < q 0 ∧ q 0 < b := by
  intro a b
  constructor
  · rintro ⟨f, f1, f2, f3, ⟨hf, hp, hq, he⟩, h0, h1, hl, hlo, hhi⟩
    exact ⟨f, f1, f2, hf, hp, fun t ht => (hq t ht).congr_deriv (by linear_combination he t ht),
      h0, h1, hl, hlo, hhi⟩
  · rintro ⟨f, p, q, hf, hp, hq, h0, h1, hl, hlo, hhi⟩
    exact ⟨f, p, q, _, ⟨hf, hp, hq, fun t _ => by ring⟩, h0, h1, hl, hlo, hhi⟩

theorem c_hiemenz_exists.bite : ¬ ∀ a b : ℝ, ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    a < q 0 ∧ q 0 < b := by
  intro h
  obtain ⟨f, p, q, -, -, -, -, -, -, hlo, hhi⟩ := h 0 0
  linarith

/-! ## B2: Hiemenz undershoot (the reading fixes S = 7.5 and writes 7.5; the headline is for every S ≥ 15/2) -/
theorem c_hiemenz_under : ∀ a b c : ℝ, (∀ f f1 f2 f3 : ℝ → ℝ, SecondReading.HiemenzODE (Icc 0 a) f f1 f2 f3 →
    f 0 = 0 → f1 0 = 0 → f2 0 = b →
    ∃ η : ℝ, 0 < η ∧ η ≤ c ∧ f2 η < 0 ∧ ∀ s ∈ Icc 0 η, f1 s < 1) ↔
    ∀ (S : ℝ) (_ : a ≤ S) (f p q : ℝ → ℝ)
    (_ : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt f (p η) (Icc 0 S) η)
    (_ : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt p (q η) (Icc 0 S) η)
    (_ : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Icc 0 S) η)
    (_ : f 0 = 0) (_ : p 0 = 0) (_ : q 0 = b),
    ∃ η ∈ Ioc (0 : ℝ) c, q η < 0 ∧ ∀ s ∈ Icc 0 η, p s < 1 := by
  intro a b c
  unfold SecondReading.HiemenzODE
  constructor
  · intro hR S hS f p q hf hp hq h0 h1 h2
    have sub : Icc (0 : ℝ) a ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS
    obtain ⟨η, hη0, hη1, k1, k2⟩ := hR f p q (fun t => -(f t * q t) - 1 + p t ^ 2)
      ⟨fun t ht => (hf t (sub ht)).mono sub, fun t ht => (hp t (sub ht)).mono sub,
        fun t ht => (hq t (sub ht)).mono sub, fun t _ => by ring⟩ h0 h1 h2
    exact ⟨η, ⟨hη0, hη1⟩, k1, k2⟩
  · rintro hH f f1 f2 f3 ⟨hf, hp, hq, he⟩ h0 h1 h2
    obtain ⟨η, ⟨hη0, hη1⟩, k1, k2⟩ := hH a le_rfl f f1 f2 hf hp
      (fun t ht => (hq t ht).congr_deriv (by linear_combination he t ht)) h0 h1 h2
    exact ⟨η, hη0, hη1, k1, k2⟩

theorem c_hiemenz_under.bite : ¬ ∀ a b c : ℝ, ∀ (S : ℝ) (_ : a ≤ S) (f p q : ℝ → ℝ)
    (_ : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt f (p η) (Icc 0 S) η)
    (_ : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt p (q η) (Icc 0 S) η)
    (_ : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Icc 0 S) η)
    (_ : f 0 = 0) (_ : p 0 = 0) (_ : q 0 = b),
    ∃ η ∈ Ioc (0 : ℝ) c, q η < 0 ∧ ∀ s ∈ Icc 0 η, p s < 1 := by
  intro h
  have e : Icc (0 : ℝ) (-1) = ∅ := Icc_eq_empty (by norm_num)
  obtain ⟨η, ⟨hη0, hη1⟩, -⟩ := h (-1) 0 0 (-1) le_rfl (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun η hη => by rw [e] at hη; exact absurd hη (Set.notMem_empty _))
    (fun η hη => by rw [e] at hη; exact absurd hη (Set.notMem_empty _))
    (fun η hη => by rw [e] at hη; exact absurd hη (Set.notMem_empty _)) rfl rfl rfl
  linarith

/-! ## B3: Homann existence (three literals: the 2 of the equation and the two bounds) -/
theorem c_homann_exists : ∀ k a b : ℝ, (∃ f f1 f2 f3 : ℝ → ℝ,
    ((∀ x ∈ Set.Ici 0, HasDerivWithinAt f (f1 x) (Set.Ici 0) x) ∧
     (∀ x ∈ Set.Ici 0, HasDerivWithinAt f1 (f2 x) (Set.Ici 0) x) ∧
     (∀ x ∈ Set.Ici 0, HasDerivWithinAt f2 (f3 x) (Set.Ici 0) x) ∧
     (∀ x ∈ Set.Ici 0, f3 x + k * f x * f2 x + 1 - (f1 x) ^ 2 = 0)) ∧
    f 0 = 0 ∧ f1 0 = 0 ∧ Filter.Tendsto f1 Filter.atTop (nhds 1) ∧
    a < f2 0 ∧ f2 0 < b) ↔ ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    a < q 0 ∧ q 0 < b := by
  intro k a b
  constructor
  · rintro ⟨f, f1, f2, f3, ⟨hf, hp, hq, he⟩, h0, h1, hl, hlo, hhi⟩
    exact ⟨f, f1, f2, hf, hp, fun t ht => (hq t ht).congr_deriv (by linear_combination he t ht),
      h0, h1, hl, hlo, hhi⟩
  · rintro ⟨f, p, q, hf, hp, hq, h0, h1, hl, hlo, hhi⟩
    exact ⟨f, p, q, _, ⟨hf, hp, hq, fun t _ => by ring⟩, h0, h1, hl, hlo, hhi⟩

theorem c_homann_exists.bite : ¬ ∀ k a b : ℝ, ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    a < q 0 ∧ q 0 < b := by
  intro h
  obtain ⟨f, p, q, -, -, -, -, -, -, hlo, hhi⟩ := h 2 0 0
  linarith

/-! ## B4: Gelfand bound -/
theorem c_gelfand_bound : ∀ c : ℝ, (∀ lam : ℝ, (∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
    SecondReading.IsClassicalGelfandSolution lam u) → lam ≤ c) ↔
    ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (_ : ContDiffOn ℝ 2 u (ball 0 1))
    (_ : ContinuousOn u (closedBall 0 1))
    (_ : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (_ : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ c := by
  intro c
  constructor
  · intro hR lam u hu hc hb hpde
    exact hR lam ⟨u, hu, hc, hpde, fun x hx => hb x (mem_sphere_zero_iff_norm.1 hx)⟩
  · rintro hH lam ⟨u, hu, hc, hpde, hb⟩
    exact hH lam u hu hc (fun x hx => hb x (mem_sphere_zero_iff_norm.2 hx)) hpde

theorem c_gelfand_bound.bite : ¬ ∀ c : ℝ, ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (_ : ContDiffOn ℝ 2 u (ball 0 1))
    (_ : ContinuousOn u (closedBall 0 1))
    (_ : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (_ : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ c := by
  intro h
  have := h (-1) 0 (fun _ => 0) contDiffOn_const continuousOn_const (fun _ _ => rfl)
    (fun x _ => by simp)
  linarith

end PBench

open Set Filter Topology InnerProductSpace Laplacian Metric
namespace RB1
namespace SecondReading
/-- P c: "c ≥ 3.321992119 (spelled as a natural number times 1e-9), or no solution has λ above c" -/
def P (c : ℝ) : Prop :=
  (c ≥ (0.000000001 : ℝ) * ((3321992119 : ℕ) : ℝ)) ∨
  ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    ¬ (c < lam)
def rn : Prop := P 3.321992119
end SecondReading

theorem cl : ∀ c : ℝ, SecondReading.P c ↔
  ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ c := by
  intro c
  unfold SecondReading.P
  constructor
  · rintro (h | h)
    · intro lam u hu hc hb hpde
      have := Checked.Math.GelfandPDEBound.gelfand_pde_bound lam u hu hc hb hpde
      have h2 : (3.321992119 : ℝ) ≤ c := by norm_num at h ⊢; linarith
      linarith
    · intro lam u hu hc hb hpde
      exact not_lt.mp (h lam u hu hc hb hpde)
  · intro h
    exact Or.inr fun lam u hu hc hb hpde => not_lt.mpr (h lam u hu hc hb hpde)

theorem cl.bite : ¬ ∀ c : ℝ,
  ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ c := by
  intro h
  obtain ⟨u, hu, hc, hb, -, hpde⟩ :=
    Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists 3.3 (by norm_num) (by norm_num)
  have := h 3 3.3 u hu hc hb hpde
  norm_num at this
end RB1

open Set Filter Topology
namespace RB2
namespace SecondReading
/-- P a b: "the interval (a,b) contains [A,B] (A, B spelled as naturals times 1e-10), or a solution has wall value in (a,b)" -/
def P (a b : ℝ) : Prop :=
  (a ≤ (0.0000000001 : ℝ) * ((12325876568 : ℕ) : ℝ) ∧ (0.0000000001 : ℝ) * ((12325876569 : ℕ) : ℝ) ≤ b) ∨
  ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    q 0 < b ∧ a < q 0
def rn : Prop := P 1.2325876568 1.2325876569
end SecondReading

theorem cl : ∀ a b : ℝ, SecondReading.P a b ↔ ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    a < q 0 ∧ q 0 < b := by
  intro a b
  unfold SecondReading.P
  constructor
  · rintro (⟨h1, h2⟩ | ⟨f, p, q, h1, h2, h3, h4, h5, h6, h7, h8⟩)
    · obtain ⟨f, p, q, h1, h2, h3, h4, h5, h6, h7, h8⟩ := Checked.Hiemenz.hiemenz_exists
      refine ⟨f, p, q, h1, h2, h3, h4, h5, h6, ?_, ?_⟩
      · norm_num at h1 h2 h7 ⊢; linarith
      · norm_num at h1 h2 h8 ⊢; linarith
    · exact ⟨f, p, q, h1, h2, h3, h4, h5, h6, h8, h7⟩
  · rintro ⟨f, p, q, h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact Or.inr ⟨f, p, q, h1, h2, h3, h4, h5, h6, h8, h7⟩

theorem cl.bite : ¬ ∀ a b : ℝ, ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    a < q 0 ∧ q 0 < b := by
  intro h
  obtain ⟨f, p, q, -, -, -, -, -, -, h7, h8⟩ := h 0 0
  exact lt_asymm h7 h8
end RB2

open Set Filter Topology InnerProductSpace Laplacian Metric
namespace RB3
namespace SecondReading
/-- P c: "c ≥ 3.321992119 (spelled as a natural number times 1e-9), or no solution has λ above c" -/
def P (c : ℝ) : Prop :=
  (c ≥ Real.sqrt ((3.321992119 : ℝ) ^ 2)) ∨
  ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    ¬ (c < lam)
def rn : Prop := P 3.321992119
end SecondReading

theorem cl : ∀ c : ℝ, SecondReading.P c ↔
  ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ c := by
  intro c
  unfold SecondReading.P
  constructor
  · rintro (h | h)
    · intro lam u hu hc hb hpde
      have := Checked.Math.GelfandPDEBound.gelfand_pde_bound lam u hu hc hb hpde
      have h2 : (3.321992119 : ℝ) ≤ c := by
        rw [Real.sqrt_sq (by norm_num)] at h; exact h
      linarith
    · intro lam u hu hc hb hpde
      exact not_lt.mp (h lam u hu hc hb hpde)
  · intro h
    exact Or.inr fun lam u hu hc hb hpde => not_lt.mpr (h lam u hu hc hb hpde)

theorem cl.bite : ¬ ∀ c : ℝ,
  ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ c := by
  intro h
  obtain ⟨u, hu, hc, hb, -, hpde⟩ :=
    Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists 3.3 (by norm_num) (by norm_num)
  have := h 3 3.3 u hu hc hb hpde
  norm_num at this
end RB3

/-! Controls of `paramClosureFaults` (run 2026-11-26T0828Z). -/
namespace PC
theorem head : (2 : ℝ) < 3 := by norm_num
theorem head2 : (3 / 2 : ℝ) < 2 := by norm_num
theorem headN : ∀ x : ℝ, 0 ≤ x ^ 2 ∨ x = 2 := fun x => Or.inl (sq_nonneg x)
theorem headZ : ∀ x : ℝ, x * 0 = 0 := fun x => by ring
namespace SecondReading
def r : Prop := (3 : ℝ) > 2
def r2 : Prop := (1.5 : ℝ) < 2
def rN : Prop := True
def rC : Prop := ((2 : ℝ) = 2 ∧ (3 : ℝ) = 3) ∨ (2 : ℝ) < 3
def rD : Prop := ((2 : ℝ) = 2 ∧ (3 : ℝ) = 3) ∨ (3 : ℝ) > 2
def rZ : Prop := True
end SecondReading
def other : Prop := (3 : ℝ) > 2
/-- valid -/
theorem good : ∀ a b : ℝ, b > a ↔ a < b := fun _ _ => Iff.rfl
theorem good.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- valid: variables in the other order -/
theorem good_order : ∀ b a : ℝ, b > a ↔ a < b := fun _ _ => Iff.rfl
theorem good_order.bite : ¬ ∀ b a : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- valid: the reading writes 1.5 where the headline writes 3 / 2 -/
theorem good_norm : ∀ a b : ℝ, a < b ↔ a < b := fun _ _ => Iff.rfl
theorem good_norm.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: the test-AZ shape, not parametric -/
theorem old_style : SecondReading.r ↔ (2 : ℝ) < 3 := iff_of_true (by unfold SecondReading.r; norm_num) head
theorem old_style.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: variables quantified but the literals kept -/
theorem kept : ∀ a b : ℝ, (3 : ℝ) > 2 ↔ (2 : ℝ) < 3 := fun _ _ => iff_of_true (by norm_num) (by norm_num)
theorem kept.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: one literal varied, one kept -/
theorem one_var : ∀ a b : ℝ, b > 2 ↔ 2 < b := fun _ _ => Iff.rfl
theorem one_var.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: a literal that does not bite, with no bite theorem -/
theorem nobite : ∀ c : ℝ, SecondReading.rN ↔ ∀ x : ℝ, 0 ≤ x ^ 2 ∨ x = c :=
  fun _ => iff_of_true trivial fun x => Or.inl (sq_nonneg x)
/-- forged: a literal that does not bite, with a bite theorem of another statement -/
theorem nobite2 : ∀ c : ℝ, SecondReading.rN ↔ ∀ x : ℝ, 0 ≤ x ^ 2 ∨ x = c :=
  fun _ => iff_of_true trivial fun x => Or.inl (sq_nonneg x)
theorem nobite2.bite : ¬ ∀ c : ℝ, c * 0 = 1 := fun h => by have := h 0; norm_num at this
/-- forged: a reading that holds the headline behind a case split on its literals -/
theorem case_split : ∀ a b : ℝ, ((a = 2 ∧ b = 3) ∨ a < b) ↔ a < b := fun a b =>
  ⟨fun h => h.elim (fun ⟨ha, hb⟩ => by subst ha hb; norm_num) id, Or.inr⟩
theorem case_split.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: the left side is not the reading -/
theorem wrong_rd : ∀ a b : ℝ, a < b ↔ a < b := fun _ _ => Iff.rfl
theorem wrong_rd.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: the reading is not a blind reader's definition -/
theorem not_rd : ∀ a b : ℝ, b > a ↔ a < b := fun _ _ => Iff.rfl
theorem not_rd.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: a headline with no literal to vary -/
theorem nolit : SecondReading.rZ ↔ ∀ x : ℝ, x * 0 = 0 := iff_of_true trivial headZ
/-- forged: the case split with the headline restated (`b > a` for `a < b`), accepted by the first version -/
theorem case_split2 : ∀ a b : ℝ, ((a = 2 ∧ b = 3) ∨ b > a) ↔ a < b := fun a b =>
  ⟨fun h => h.elim (fun ⟨ha, hb⟩ => by subst ha hb; norm_num) id, Or.inr⟩
theorem case_split2.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
end PC


open Claims in
run_cmd do
  let env ← getEnv
  for (ns, rn) in [(`PBench.SecondReading, `PBench.SecondReading.hiemenzExists),
      (`PBench.SecondReading, `PBench.SecondReading.hiemenzUnder),
      (`PBench.SecondReading, `PBench.SecondReading.homannExists),
      (`PBench.SecondReading, `PBench.SecondReading.gelfandBound),
      (`RB1.SecondReading, `RB1.SecondReading.rn), (`RB2.SecondReading, `RB2.SecondReading.rn),
      (`RB3.SecondReading, `RB3.SecondReading.rn), (`PC.SecondReading, `PC.SecondReading.r),
      (`PC.SecondReading, `PC.SecondReading.rD)] do
    let f ← liftTermElabM <| decidedParts env (fun c => ns.isPrefixOf c) rn
    logInfo m!"READING {rn}: {if f.isEmpty then "no decided part" else "DECIDED PART"} {f.toList}"
