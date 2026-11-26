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

open Claims in
run_cmd do
  let env ← getEnv
  let isRd := fun (c : Name) => (`PBench.SecondReading).isPrefixOf c
  for (head, t, rn) in [(`Checked.Hiemenz.hiemenz_exists, `PBench.c_hiemenz_exists, `PBench.SecondReading.hiemenzExists),
      (`Checked.Hiemenz.hiemenz_under, `PBench.c_hiemenz_under, `PBench.SecondReading.hiemenzUnder),
      (`Checked.Homann.homann_exists, `PBench.c_homann_exists, `PBench.SecondReading.homannExists),
      (`Checked.Math.GelfandPDEBound.gelfand_pde_bound, `PBench.c_gelfand_bound, `PBench.SecondReading.gelfandBound)] do
    let faults ← liftTermElabM <| paramClosureFaults env isRd head t rn
    if faults.isEmpty then logInfo m!"BENCH {t}: ACCEPTED"
    else logInfo m!"BENCH {t}: REJECTED ({faults.size}): {faults.toList}"
