/-! Bench of honest closures (run 2026-11-26T0228Z, part 3): real headlines of `Checked`, the statement of a blind
reader copied from `Work/**/…Blind.lean` as a `def … : Prop` (the shape a `Checked.Trust.SecondReading*` reading
has), and a bridge `R ↔ H` written the way an honest author writes one (rcases, `unfold`, helper lemmas). Every
bridge here proves an equivalence of meaning: no side is proved, no lemma of the program's proofs is used. The
bench runs the page's `closureFaults` on each and prints what it says. `Bench.*` stands for the closure module (a
`Checked` module on the page), so its helper theorems count as the program's, as they would there. -/

open Set Filter Topology Metric InnerProductSpace Laplacian
open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

namespace Bench

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

/-- Blind reader, B1 third coefficient (`Work/Cosmography/B1A3BoundBlind.lean`; given the program's pinned
definitions `hubble`, `redshift`, `lumDistFlat`, `logPolyDL3`). -/
noncomputable def blindModulus (d : ℝ) : ℝ := 5 * Real.logb 10 d

def a3Bound : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ t₁ t₂ t₃ : ℝ) (H₀ Ωm : ℝ), 0 < H₀ → Ωm ∈ Set.Icc (0 : ℝ) 1 →
    t₃ < t₂ → t₂ < t₁ → t₁ < t₀ →
    (∀ t ∈ Set.Icc t₃ t₀, 0 < a t) → (∀ t ∈ Set.Icc t₃ t₀, DifferentiableAt ℝ a t) →
    (∀ t ∈ Set.Icc t₃ t₀, hubble a t = H₀ * Real.sqrt (Ωm * (1 + redshift a t₀ t) ^ 3 + 1 - Ωm)) →
    1 + redshift a t₀ t₁ = Real.sqrt 2 → 1 + redshift a t₀ t₂ = 2 * Real.sqrt 2 →
    1 + redshift a t₀ t₃ = 4 * Real.sqrt 2 →
    ∀ (a₂ a₃ H : ℝ), 0 < H →
    0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁) → 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₂) →
    0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃) →
    (∃ D : ℝ,
      |blindModulus (logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)) - blindModulus (lumDistFlat a t₀ t₁) - D| ≤ 0.05 ∧
      |blindModulus (logPolyDL3 a₂ a₃ H (redshift a t₀ t₂)) - blindModulus (lumDistFlat a t₀ t₂) - D| ≤ 0.05 ∧
      |blindModulus (logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - blindModulus (lumDistFlat a t₀ t₃) - D| ≤ 0.05) →
    a₃ > 13 / 5
end SecondReading

/-! ## B1: Hiemenz existence (rcases through the reading's definitions; Mathlib only) -/
theorem c_hiemenz_exists : SecondReading.hiemenzExists ↔ ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    1.2325876568 < q 0 ∧ q 0 < 1.2325876569 := by
  constructor
  · rintro ⟨f, f1, f2, f3, ⟨hf, hp, hq, he⟩, h0, h1, hl, hlo, hhi⟩
    exact ⟨f, f1, f2, hf, hp, fun t ht => (hq t ht).congr_deriv (by linear_combination he t ht),
      h0, h1, hl, hlo, hhi⟩
  · rintro ⟨f, p, q, hf, hp, hq, h0, h1, hl, hlo, hhi⟩
    exact ⟨f, p, q, _, ⟨hf, hp, hq, fun t _ => by ring⟩, h0, h1, hl, hlo, hhi⟩

/-! ## B2: Hiemenz undershoot (the reading fixes S = 7.5; the headline is for every S ≥ 15/2) -/
theorem c_hiemenz_under : SecondReading.hiemenzUnder ↔ ∀ (S : ℝ) (_ : 15 / 2 ≤ S) (f p q : ℝ → ℝ)
    (_ : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt f (p η) (Icc 0 S) η)
    (_ : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt p (q η) (Icc 0 S) η)
    (_ : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Icc 0 S) η)
    (_ : f 0 = 0) (_ : p 0 = 0) (_ : q 0 = 1.2325876568),
    ∃ η ∈ Ioc (0 : ℝ) (15 / 2), q η < 0 ∧ ∀ s ∈ Icc 0 η, p s < 1 := by
  unfold SecondReading.hiemenzUnder SecondReading.HiemenzODE
  have h75 : (7.5 : ℝ) = 15 / 2 := by norm_num
  constructor
  · intro hR S hS f p q hf hp hq h0 h1 h2
    have sub : Icc (0 : ℝ) 7.5 ⊆ Icc 0 S := Icc_subset_Icc le_rfl (by rw [h75]; exact hS)
    obtain ⟨η, hη0, hη1, k1, k2⟩ := hR f p q (fun t => -(f t * q t) - 1 + p t ^ 2)
      ⟨fun t ht => (hf t (sub ht)).mono sub, fun t ht => (hp t (sub ht)).mono sub,
        fun t ht => (hq t (sub ht)).mono sub, fun t _ => by ring⟩ h0 h1 h2
    exact ⟨η, ⟨hη0, by rw [← h75]; exact hη1⟩, k1, k2⟩
  · rintro hH f f1 f2 f3 ⟨hf, hp, hq, he⟩ h0 h1 h2
    obtain ⟨η, ⟨hη0, hη1⟩, k1, k2⟩ := hH 7.5 (by norm_num) f f1 f2 hf hp
      (fun t ht => (hq t ht).congr_deriv (by linear_combination he t ht)) h0 h1 h2
    exact ⟨η, hη0, by rw [h75]; exact hη1, k1, k2⟩

/-! ## B3: Homann existence (`simp only` with the reading's definitions, then as B1) -/
theorem c_homann_exists : SecondReading.homannExists ↔ ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    1.3119376938 < q 0 ∧ q 0 < 1.3119376939 := by
  simp only [SecondReading.homannExists, SecondReading.HomannSol]
  constructor
  · rintro ⟨f, f1, f2, f3, ⟨hf, hp, hq, he⟩, h0, h1, hl, hlo, hhi⟩
    exact ⟨f, f1, f2, hf, hp, fun t ht => (hq t ht).congr_deriv (by linear_combination he t ht),
      h0, h1, hl, hlo, hhi⟩
  · rintro ⟨f, p, q, hf, hp, hq, h0, h1, hl, hlo, hhi⟩
    exact ⟨f, p, q, _, ⟨hf, hp, hq, fun t _ => by ring⟩, h0, h1, hl, hlo, hhi⟩

/-! ## B4: Gelfand bound (Mathlib's `mem_sphere_zero_iff_norm`) -/
theorem c_gelfand_bound : SecondReading.gelfandBound ↔ ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (_ : ContDiffOn ℝ 2 u (ball 0 1))
    (_ : ContinuousOn u (closedBall 0 1))
    (_ : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (_ : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ 3.321992119 := by
  constructor
  · intro hR lam u hu hc hb hpde
    exact hR lam ⟨u, hu, hc, hpde, fun x hx => hb x (mem_sphere_zero_iff_norm.1 hx)⟩
  · rintro hH lam ⟨u, hu, hc, hpde, hb⟩
    exact hH lam u hu hc (fun x hx => hb x (mem_sphere_zero_iff_norm.2 hx)) hpde

/-! ## B5: B1 third coefficient (program definitions; the bridge needs that the luminosity distance is positive:
a helper lemma, as in the audit `Work/Cosmography/B1A3BoundAudit.lean`) -/
lemma ld_pos (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t < t₀) (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s) : 0 < lumDistFlat a t₀ t := by
  have hcont : ContinuousOn (fun s => 1 / a s) (Set.Icc t t₀) :=
    ContinuousOn.div continuousOn_const (fun s hs => (hdiff s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hpos s hs).ne')
  have hint : 0 < ∫ s in t..t₀, 1 / a s :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable_of_Icc htt.le)
      (fun s hs => by have := hpos s ⟨hs.1.le, hs.2.le⟩; positivity) htt
  have h0 := hpos t₀ ⟨htt.le, le_rfl⟩
  have h1 := hpos t ⟨le_rfl, htt.le⟩
  have hz : 0 < 1 + redshift a t₀ t := by
    unfold redshift; have : 0 < a t₀ / a t := by positivity
    linarith
  unfold lumDistFlat comoving
  positivity

/-- `|5 log₁₀ P − 5 log₁₀ d − Δ| ≤ 0.05 ↔ |5 log₁₀ (d / P) − (−Δ)| ≤ 1/20` for positive `d`, `P`. -/
lemma mod_iff (d P D : ℝ) (hd : 0 < d) (hP : 0 < P) :
    |SecondReading.blindModulus P - SecondReading.blindModulus d - D| ≤ 0.05 ↔
      |5 * Real.logb 10 (d / P) - (-D)| ≤ 1 / 20 := by
  unfold SecondReading.blindModulus
  rw [Real.logb_div hd.ne' hP.ne',
    show 5 * (Real.logb 10 d - Real.logb 10 P) - -D = -(5 * Real.logb 10 P - 5 * Real.logb 10 d - D) by ring,
    abs_neg]
  norm_num

theorem c_a3_bound : SecondReading.a3Bound ↔ ∀ (Ω : ℝ) (_ : 0 ≤ Ω) (_ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₁ t₀ : ℝ) (_ : t₅ ≤ t₃) (_ : t₃ ≤ t₁) (_ : t₁ ≤ t₀)
    (_ : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (_ : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (_ : 0 < hubble a t₀)
    (_ : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (_ : redshift a t₀ t₁ = √2 - 1) (_ : redshift a t₀ t₃ = 2 * √2 - 1)
    (_ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ H c : ℝ) (_ : 0 < H)
    (_ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁))
    (_ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (_ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₅))
    (_ : |5 * Real.logb 10 (lumDistFlat a t₀ t₁ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)) - c| ≤ 1 / 20)
    (_ : |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c| ≤ 1 / 20)
    (_ : |5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) - c| ≤ 1 / 20),
    13 / 5 < a₃ := by
  have s2 : (0 : ℝ) < √2 := by positivity
  constructor
  · intro hR Ω hΩ₀ hΩ₁ a t₅ t₃ t₁ t₀ h₅₃ h₃₁ h₁₀ hpos hdiff hH₀ hH hz₁ hz₃ hz₅ a₂ a₃ H c hHp hp₁ hp₃ hp₅
      hm₁ hm₃ hm₅
    have l53 : t₅ < t₃ := lt_of_le_of_ne h₅₃ (fun e => by rw [e] at hz₅; linarith)
    have l31 : t₃ < t₁ := lt_of_le_of_ne h₃₁ (fun e => by rw [e] at hz₃; linarith)
    have l10 : t₁ < t₀ := lt_of_le_of_ne h₁₀ (fun e => by
      rw [e] at hz₁
      have h0 := hpos t₀ ⟨by linarith, le_rfl⟩
      unfold redshift at hz₁; rw [div_self h0.ne'] at hz₁
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])
    have sub : ∀ {t}, t₅ ≤ t → Set.Icc t t₀ ⊆ Set.Icc t₅ t₀ := fun h => Set.Icc_subset_Icc_left h
    have d₁ := ld_pos a t₁ t₀ l10 (fun s hs => hpos s (sub (by linarith) hs)) (fun s hs => hdiff s (sub (by linarith) hs))
    have d₃ := ld_pos a t₃ t₀ (by linarith) (fun s hs => hpos s (sub h₅₃ hs)) (fun s hs => hdiff s (sub h₅₃ hs))
    have d₅ := ld_pos a t₅ t₀ (by linarith) hpos hdiff
    have := hR a t₀ t₁ t₃ t₅ (hubble a t₀) Ω hH₀ ⟨hΩ₀, hΩ₁⟩ l53 l31 l10 hpos hdiff hH
      (by rw [hz₁]; ring) (by rw [hz₃]; ring) (by rw [hz₅]; ring) a₂ a₃ H hHp hp₁ hp₃ hp₅
      ⟨-c, (mod_iff _ _ _ d₁ hp₁).2 (by simpa using hm₁), (mod_iff _ _ _ d₃ hp₃).2 (by simpa using hm₃),
        (mod_iff _ _ _ d₅ hp₅).2 (by simpa using hm₅)⟩
    exact this
  · intro hH a t₀ t₁ t₂ t₃ H₀ Ωm hH₀ hΩ h32 h21 h10 hpos hdiff hlaw hz1 hz2 hz3 a₂ a₃ H hHp hp1 hp2 hp3 hfit
    obtain ⟨D, f1, f2, f3⟩ := hfit
    have h30 : t₃ ≤ t₀ := by linarith
    have ha0 : 0 < a t₀ := hpos t₀ ⟨h30, le_rfl⟩
    have hr0 : redshift a t₀ t₀ = 0 := by unfold redshift; rw [div_self ha0.ne']; ring
    have hHt : hubble a t₀ = H₀ := by rw [hlaw t₀ ⟨h30, le_rfl⟩, hr0]; norm_num
    have sub : ∀ {t}, t₃ ≤ t → Set.Icc t t₀ ⊆ Set.Icc t₃ t₀ := fun h => Set.Icc_subset_Icc_left h
    have d₁ := ld_pos a t₁ t₀ h10 (fun s hs => hpos s (sub (by linarith) hs)) (fun s hs => hdiff s (sub (by linarith) hs))
    have d₂ := ld_pos a t₂ t₀ (by linarith) (fun s hs => hpos s (sub h32.le hs)) (fun s hs => hdiff s (sub h32.le hs))
    have d₃ := ld_pos a t₃ t₀ (by linarith) hpos hdiff
    have := hH Ωm hΩ.1 hΩ.2 a t₃ t₂ t₁ t₀ h32.le h21.le h10.le hpos hdiff (by rw [hHt]; exact hH₀)
      (fun s hs => by rw [hHt]; exact hlaw s hs) (by linarith) (by linarith) (by linarith) a₂ a₃ H (-D) hHp
      hp1 hp2 hp3 ((mod_iff _ _ _ d₁ hp1).1 f1) ((mod_iff _ _ _ d₂ hp2).1 f2) ((mod_iff _ _ _ d₃ hp3).1 f3)
    linarith

/-! ## B5n: B5 with its two helpers named under the closure theorem (`c_a3_bound_ns.ld_pos`, `c_a3_bound_ns.mod_iff`) -/
lemma c_a3_bound_ns.ld_pos (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t < t₀) (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s) : 0 < lumDistFlat a t₀ t := by
  have hcont : ContinuousOn (fun s => 1 / a s) (Set.Icc t t₀) :=
    ContinuousOn.div continuousOn_const (fun s hs => (hdiff s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hpos s hs).ne')
  have hint : 0 < ∫ s in t..t₀, 1 / a s :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable_of_Icc htt.le)
      (fun s hs => by have := hpos s ⟨hs.1.le, hs.2.le⟩; positivity) htt
  have h0 := hpos t₀ ⟨htt.le, le_rfl⟩
  have h1 := hpos t ⟨le_rfl, htt.le⟩
  have hz : 0 < 1 + redshift a t₀ t := by
    unfold redshift; have : 0 < a t₀ / a t := by positivity
    linarith
  unfold lumDistFlat comoving
  positivity

/-- `|5 log₁₀ P − 5 log₁₀ d − Δ| ≤ 0.05 ↔ |5 log₁₀ (d / P) − (−Δ)| ≤ 1/20` for positive `d`, `P`. -/
lemma c_a3_bound_ns.mod_iff (d P D : ℝ) (hd : 0 < d) (hP : 0 < P) :
    |SecondReading.blindModulus P - SecondReading.blindModulus d - D| ≤ 0.05 ↔
      |5 * Real.logb 10 (d / P) - (-D)| ≤ 1 / 20 := by
  unfold SecondReading.blindModulus
  rw [Real.logb_div hd.ne' hP.ne',
    show 5 * (Real.logb 10 d - Real.logb 10 P) - -D = -(5 * Real.logb 10 P - 5 * Real.logb 10 d - D) by ring,
    abs_neg]
  norm_num

theorem c_a3_bound_ns : SecondReading.a3Bound ↔ ∀ (Ω : ℝ) (_ : 0 ≤ Ω) (_ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₁ t₀ : ℝ) (_ : t₅ ≤ t₃) (_ : t₃ ≤ t₁) (_ : t₁ ≤ t₀)
    (_ : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (_ : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (_ : 0 < hubble a t₀)
    (_ : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (_ : redshift a t₀ t₁ = √2 - 1) (_ : redshift a t₀ t₃ = 2 * √2 - 1)
    (_ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ H c : ℝ) (_ : 0 < H)
    (_ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁))
    (_ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (_ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₅))
    (_ : |5 * Real.logb 10 (lumDistFlat a t₀ t₁ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)) - c| ≤ 1 / 20)
    (_ : |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c| ≤ 1 / 20)
    (_ : |5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) - c| ≤ 1 / 20),
    13 / 5 < a₃ := by
  have s2 : (0 : ℝ) < √2 := by positivity
  constructor
  · intro hR Ω hΩ₀ hΩ₁ a t₅ t₃ t₁ t₀ h₅₃ h₃₁ h₁₀ hpos hdiff hH₀ hH hz₁ hz₃ hz₅ a₂ a₃ H c hHp hp₁ hp₃ hp₅
      hm₁ hm₃ hm₅
    have l53 : t₅ < t₃ := lt_of_le_of_ne h₅₃ (fun e => by rw [e] at hz₅; linarith)
    have l31 : t₃ < t₁ := lt_of_le_of_ne h₃₁ (fun e => by rw [e] at hz₃; linarith)
    have l10 : t₁ < t₀ := lt_of_le_of_ne h₁₀ (fun e => by
      rw [e] at hz₁
      have h0 := hpos t₀ ⟨by linarith, le_rfl⟩
      unfold redshift at hz₁; rw [div_self h0.ne'] at hz₁
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])
    have sub : ∀ {t}, t₅ ≤ t → Set.Icc t t₀ ⊆ Set.Icc t₅ t₀ := fun h => Set.Icc_subset_Icc_left h
    have d₁ := c_a3_bound_ns.ld_pos a t₁ t₀ l10 (fun s hs => hpos s (sub (by linarith) hs)) (fun s hs => hdiff s (sub (by linarith) hs))
    have d₃ := c_a3_bound_ns.ld_pos a t₃ t₀ (by linarith) (fun s hs => hpos s (sub h₅₃ hs)) (fun s hs => hdiff s (sub h₅₃ hs))
    have d₅ := c_a3_bound_ns.ld_pos a t₅ t₀ (by linarith) hpos hdiff
    have := hR a t₀ t₁ t₃ t₅ (hubble a t₀) Ω hH₀ ⟨hΩ₀, hΩ₁⟩ l53 l31 l10 hpos hdiff hH
      (by rw [hz₁]; ring) (by rw [hz₃]; ring) (by rw [hz₅]; ring) a₂ a₃ H hHp hp₁ hp₃ hp₅
      ⟨-c, (c_a3_bound_ns.mod_iff _ _ _ d₁ hp₁).2 (by simpa using hm₁), (c_a3_bound_ns.mod_iff _ _ _ d₃ hp₃).2 (by simpa using hm₃),
        (c_a3_bound_ns.mod_iff _ _ _ d₅ hp₅).2 (by simpa using hm₅)⟩
    exact this
  · intro hH a t₀ t₁ t₂ t₃ H₀ Ωm hH₀ hΩ h32 h21 h10 hpos hdiff hlaw hz1 hz2 hz3 a₂ a₃ H hHp hp1 hp2 hp3 hfit
    obtain ⟨D, f1, f2, f3⟩ := hfit
    have h30 : t₃ ≤ t₀ := by linarith
    have ha0 : 0 < a t₀ := hpos t₀ ⟨h30, le_rfl⟩
    have hr0 : redshift a t₀ t₀ = 0 := by unfold redshift; rw [div_self ha0.ne']; ring
    have hHt : hubble a t₀ = H₀ := by rw [hlaw t₀ ⟨h30, le_rfl⟩, hr0]; norm_num
    have sub : ∀ {t}, t₃ ≤ t → Set.Icc t t₀ ⊆ Set.Icc t₃ t₀ := fun h => Set.Icc_subset_Icc_left h
    have d₁ := c_a3_bound_ns.ld_pos a t₁ t₀ h10 (fun s hs => hpos s (sub (by linarith) hs)) (fun s hs => hdiff s (sub (by linarith) hs))
    have d₂ := c_a3_bound_ns.ld_pos a t₂ t₀ (by linarith) (fun s hs => hpos s (sub h32.le hs)) (fun s hs => hdiff s (sub h32.le hs))
    have d₃ := c_a3_bound_ns.ld_pos a t₃ t₀ (by linarith) hpos hdiff
    have := hH Ωm hΩ.1 hΩ.2 a t₃ t₂ t₁ t₀ h32.le h21.le h10.le hpos hdiff (by rw [hHt]; exact hH₀)
      (fun s hs => by rw [hHt]; exact hlaw s hs) (by linarith) (by linarith) (by linarith) a₂ a₃ H (-D) hHp
      hp1 hp2 hp3 ((c_a3_bound_ns.mod_iff _ _ _ d₁ hp1).1 f1) ((c_a3_bound_ns.mod_iff _ _ _ d₂ hp2).1 f2) ((c_a3_bound_ns.mod_iff _ _ _ d₃ hp3).1 f3)
    linarith

/-! ## B6: Homann existence again, unfolding by `rw` with the reading's definitions (equation lemmas) -/
theorem c_homann_exists_rw : SecondReading.homannExists ↔ ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    1.3119376938 < q 0 ∧ q 0 < 1.3119376939 := by
  rw [SecondReading.homannExists]
  constructor
  · rintro ⟨f, f1, f2, f3, hs, h0, h1, hl, hlo, hhi⟩
    rw [SecondReading.HomannSol] at hs
    obtain ⟨hf, hp, hq, he⟩ := hs
    exact ⟨f, f1, f2, hf, hp, fun t ht => (hq t ht).congr_deriv (by linear_combination he t ht),
      h0, h1, hl, hlo, hhi⟩
  · rintro ⟨f, p, q, hf, hp, hq, h0, h1, hl, hlo, hhi⟩
    refine ⟨f, p, q, fun t => -(2 * f t * q t) - 1 + p t ^ 2, ?_, h0, h1, hl, hlo, hhi⟩
    rw [SecondReading.HomannSol]
    exact ⟨hf, hp, hq, fun t _ => by ring⟩

end Bench

open Claims in
run_cmd do
  let env ← getEnv
  let isProg := fun (c : Name) => isCheckedConst env c || (`Bench).isPrefixOf c
  let isRd := fun (c : Name) => (`Bench.SecondReading).isPrefixOf c
  for (head, t) in [(`Checked.Hiemenz.hiemenz_exists, `Bench.c_hiemenz_exists),
      (`Checked.Hiemenz.hiemenz_under, `Bench.c_hiemenz_under),
      (`Checked.Homann.homann_exists, `Bench.c_homann_exists),
      (`Checked.Math.GelfandPDEBound.gelfand_pde_bound, `Bench.c_gelfand_bound),
      (`Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound, `Bench.c_a3_bound),
      (`Checked.Homann.homann_exists, `Bench.c_homann_exists_rw),
      (`Checked.Cosmography.B1A3Bound.third_coefficient_lower_bound, `Bench.c_a3_bound_ns)] do
    let faults ← liftTermElabM <| closureFaults env isProg isRd head t
    if faults.isEmpty then logInfo m!"BENCH {t}: ACCEPTED"
    else logInfo m!"BENCH {t}: REJECTED ({faults.size}): {faults.toList}"
