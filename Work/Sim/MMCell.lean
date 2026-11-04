import Mathlib
import Work.Sim.ODETools
import Work.Sim.Validated

/-!
# Michaelis–Menten (reduced): Lipschitz box and the validated cell step

Reduced field (conservation e = 1 − c, p = 1 − s − c, all rate constants 1):
F(s, c) = (−s + c s + c, s − c s − 2c) on ℝ × ℝ (sup norm). On the box
s ∈ [−1/10, 11/10], c ∈ [−1/10, 1/4] it is Lipschitz with constant 21/5
(row sums |c − 1| + |s + 1| ≤ 16/5, |1 − c| + |s + 2| ≤ 21/5).
`cell`: one Grönwall step from a rational polynomial approximation with certified defect,
valid for every field Φ that agrees with F on the box (the true field, or a clamped one used
for existence). Confinement to the box comes from the enclosure itself
(`Work.Sim.Validated.tube_cell`), with tube radius 1/100: no invariant is needed.
-/

namespace Work.Sim.MMCell
open Set Work.Sim

/-- Reduced Michaelis–Menten field with k₁ = k₋₁ = k₂ = 1, e₀ = s₀ = 1. -/
def mmF (p : ℝ × ℝ) : ℝ × ℝ := (-p.1 + p.2 * p.1 + p.2, p.1 - p.2 * p.1 - 2 * p.2)

/-- The box s ∈ [−1/10, 11/10], c ∈ [−1/10, 1/4]. -/
def box : Set (ℝ × ℝ) := {p | -1 / 10 ≤ p.1 ∧ p.1 ≤ 11 / 10 ∧ -1 / 10 ≤ p.2 ∧ p.2 ≤ 1 / 4}

theorem comb {a b x y A B m : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hx : |x| ≤ m) (hy : |y| ≤ m) :
    |a * x + b * y| ≤ (A + B) * m := by
  calc |a * x + b * y| ≤ |a * x| + |b * y| := abs_add_le _ _
    _ = |a| * |x| + |b| * |y| := by rw [abs_mul, abs_mul]
    _ ≤ A * m + B * m := add_le_add
        (mul_le_mul ha hx (abs_nonneg _) ((abs_nonneg _).trans ha))
        (mul_le_mul hb hy (abs_nonneg _) ((abs_nonneg _).trans hb))
    _ = (A + B) * m := by ring

theorem lip_box : LipschitzOnWith ⟨21 / 5, by norm_num⟩ mmF box := by
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
  simp only [mmF, Prod.dist_eq, Real.dist_eq]
  change _ ≤ (21 / 5 : ℝ) * _
  set m := max |p.1 - q.1| |p.2 - q.2|
  have hd1 : |p.1 - q.1| ≤ m := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ m := le_max_right _ _
  have hm : 0 ≤ m := (abs_nonneg _).trans hd1
  refine max_le ?_ ?_
  · have e : (-p.1 + p.2 * p.1 + p.2) - (-q.1 + q.2 * q.1 + q.2) =
        (p.2 - 1) * (p.1 - q.1) + (q.1 + 1) * (p.2 - q.2) := by ring
    rw [e]
    have h1 : |p.2 - 1| ≤ 11 / 10 := by rw [abs_le]; constructor <;> linarith
    have h2 : |q.1 + 1| ≤ 21 / 10 := by rw [abs_le]; constructor <;> linarith
    have := comb h1 h2 hd1 hd2
    linarith
  · have e : (p.1 - p.2 * p.1 - 2 * p.2) - (q.1 - q.2 * q.1 - 2 * q.2) =
        (1 - p.2) * (p.1 - q.1) + (-(q.1 + 2)) * (p.2 - q.2) := by ring
    rw [e]
    have h1 : |1 - p.2| ≤ 11 / 10 := by rw [abs_le]; constructor <;> linarith
    have h2 : |-(q.1 + 2)| ≤ 31 / 10 := by rw [abs_neg, abs_le]; constructor <;> linarith
    have := comb h1 h2 hd1 hd2
    linarith

/-- A field agreeing with `mmF` on the box is Lipschitz there with the same constant. -/
theorem lip_of_eq {Φ : ℝ × ℝ → ℝ × ℝ} (hΦ : ∀ p ∈ box, Φ p = mmF p) :
    LipschitzOnWith ⟨21 / 5, by norm_num⟩ Φ box := by
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  rw [hΦ p hp, hΦ q hq]
  exact lip_box.dist_le_mul p hp q hq

/-- One validated step on the cell [t₀, t₀ + h] ⊆ [0, T] for any solution `y` (derivatives within
[0, T]) of any field Φ that equals `mmF` on the box: if the polynomial pair (ps, pc) stays 1/100
inside the box, has defect at most ε, and `y` starts within δ of it, then `y` stays within B of it
on the whole cell. -/
theorem cell (ps pc : List ℚ) {Φ : ℝ × ℝ → ℝ × ℝ} (hΦ : ∀ p ∈ box, Φ p = mmF p)
    {T t0 h δ ε B : ℝ} {y : ℝ → ℝ × ℝ}
    (ht0 : 0 ≤ t0) (hT : t0 + h ≤ T) (hh : 0 < h) (hKh : 21 / 5 * h < 1) (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (Φ (y t)) (Icc 0 T) t)
    (hs1 : ∀ σ ∈ Icc 0 h, -9 / 100 ≤ evalQ ps σ) (hs2 : ∀ σ ∈ Icc 0 h, evalQ ps σ ≤ 109 / 100)
    (hc1 : ∀ σ ∈ Icc 0 h, -9 / 100 ≤ evalQ pc σ) (hc2 : ∀ σ ∈ Icc 0 h, evalQ pc σ ≤ 6 / 25)
    (hd1 : ∀ σ ∈ Icc 0 h,
      |dEvalQ ps σ - (-evalQ ps σ + evalQ pc σ * evalQ ps σ + evalQ pc σ)| ≤ ε)
    (hd2 : ∀ σ ∈ Icc 0 h,
      |dEvalQ pc σ - (evalQ ps σ - evalQ pc σ * evalQ ps σ - 2 * evalQ pc σ)| ≤ ε)
    (h0 : |(y t0).1 - evalQ ps 0| ≤ δ) (h0' : |(y t0).2 - evalQ pc 0| ≤ δ)
    (hB : δ * (1 / (1 - 21 / 5 * h)) + ε / (21 / 5) * (1 / (1 - 21 / 5 * h) - 1) ≤ B)
    (hBM : B < 1 / 100) :
    ∀ t ∈ Icc t0 (t0 + h), |(y t).1 - evalQ ps (t - t0)| ≤ B ∧
      |(y t).2 - evalQ pc (t - t0)| ≤ B ∧ y t ∈ box := by
  have hsub : Icc t0 (t0 + h) ⊆ Icc 0 T := Icc_subset_Icc ht0 hT
  have hs : ∀ t ∈ Icc t0 (t0 + h), t - t0 ∈ Icc 0 h := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set g : ℝ → ℝ × ℝ := fun t => (evalQ ps (t - t0), evalQ pc (t - t0)) with hg
  have hgbox : ∀ t ∈ Icc t0 (t0 + h), g t ∈ box := fun t ht =>
    ⟨by linarith [hs1 _ (hs t ht)], by linarith [hs2 _ (hs t ht)],
      by linarith [hc1 _ (hs t ht)], by linarith [hc2 _ (hs t ht)]⟩
  have key := Work.Sim.Validated.tube_cell (lip_of_eq hΦ) (f := y) (g := g)
    (g' := fun t => (dEvalQ ps (t - t0), dEvalQ pc (t - t0))) (a := t0) (b := t0 + h)
    (δ := δ) (ε := ε) (B := B) (B' := 1 / 100) (by linarith)
    (fun t ht => ((hd t (hsub ht)).continuousWithinAt).mono hsub)
    (fun t ht => (hd t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩))
    (((continuous_evalQ ps).comp (continuous_sub_right t0)).prodMk
      ((continuous_evalQ pc).comp (continuous_sub_right t0))).continuousOn
    (fun t _ => (((hasDerivAt_evalQ ps (t - t0)).comp_sub_const t t0).prodMk
      ((hasDerivAt_evalQ pc (t - t0)).comp_sub_const t t0)).hasDerivWithinAt)
    (fun t ht => by
      rw [hΦ _ (hgbox t (Ico_subset_Icc_self ht))]
      simp only [hg, mmF, Prod.dist_eq, Real.dist_eq]
      have hσ := hs t (Ico_subset_Icc_self ht)
      exact max_le (hd1 _ hσ) (hd2 _ hσ))
    (fun t ht z hz => by
      simp only [hg, Prod.dist_eq, Real.dist_eq, max_lt_iff] at hz
      obtain ⟨hz1, hz2⟩ := hz
      have g1 := hs1 _ (hs t ht)
      have g2 := hs2 _ (hs t ht)
      have g3 := hc1 _ (hs t ht)
      have g4 := hc2 _ (hs t ht)
      have a1 := abs_lt.1 hz1
      have a2 := abs_lt.1 hz2
      exact ⟨by linarith [a1.1], by linarith [a1.2], by linarith [a2.1], by linarith [a2.2]⟩)
    hBM
    (by
      simp only [hg, sub_self, Prod.dist_eq, Real.dist_eq]
      exact max_le h0 h0')
    (fun t ht => by
      have := gronwallBound_le_cell (K := 21 / 5) hδ hε (by norm_num)
        (show t - t0 ≤ h by linarith [ht.2]) hh hKh
      exact this.trans hB)
  intro t ht
  have h1 := key t ht
  simp only [hg, Prod.dist_eq, Real.dist_eq] at h1
  have e1 := (le_max_left _ _).trans h1
  have e2 := (le_max_right _ _).trans h1
  refine ⟨e1, e2, ?_⟩
  have g1 := hs1 _ (hs t ht)
  have g2 := hs2 _ (hs t ht)
  have g3 := hc1 _ (hs t ht)
  have g4 := hc2 _ (hs t ht)
  rw [abs_le] at e1 e2
  exact ⟨by linarith [e1.1], by linarith [e1.2], by linarith [e2.1], by linarith [e2.2]⟩

/-- Crude lower bound p(σ) ≥ c₀ − h·Σ|cₖ₊₁|hᵏ on [0, h], for any coefficient list. -/
theorem lower_of (p : List ℚ) {σ h : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ h) :
    ((p.headD 0 : ℚ) : ℝ) - h * evalQ (p.tail.map (fun c => |c|)) h ≤ evalQ p σ := by
  cases p with
  | nil => simp [evalQ]
  | cons c cs => simpa using evalQ_ge c cs h0 h1

/-- Crude upper bound p(σ) ≤ c₀ + h·Σ|cₖ₊₁|hᵏ on [0, h], for any coefficient list. -/
theorem upper_of (p : List ℚ) {σ h : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ h) :
    evalQ p σ ≤ ((p.headD 0 : ℚ) : ℝ) + h * evalQ (p.tail.map (fun c => |c|)) h := by
  cases p with
  | nil => simp [evalQ]
  | cons c cs => simpa using evalQ_le c cs h0 h1

end Work.Sim.MMCell
