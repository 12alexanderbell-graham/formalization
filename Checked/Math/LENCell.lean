import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Sim.ODETools

/-! Lane–Emden equation of any integer index n: time-dependent validated cell step (`tube_cell_t`) and one Grönwall step `cell` for the system θ' = φ, φ' = −(two/ξ)φ − θⁿ with the state confined to a slab in θ; the defect of the second component is certified multiplied out. Generalised from `Checked.Math.LECell`; promoted verbatim from `Work/Math/LENCell.lean`. -/

namespace Checked.Math.LENCell
open Set Checked.Sim

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Validated cell step for a time-dependent field, with confinement by the enclosure itself. -/
theorem tube_cell_t {F : ℝ → E → E} {K : NNReal} {S : Set E} {f g g' : ℝ → E}
    {a b δ ε B B' : ℝ} (hF : ∀ t ∈ Ico a b, LipschitzOnWith K (F t) S) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (F t (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (hdef : ∀ t ∈ Ico a b, dist (g' t) (F t (g t)) ≤ ε)
    (htube : ∀ t ∈ Icc a b, ∀ y, dist y (g t) < B' → y ∈ S)
    (hBB : B < B') (h0 : dist (f a) (g a) ≤ δ)
    (hgron : ∀ t ∈ Icc a b, gronwallBound δ K ε (t - a) ≤ B) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ B := by
  have hB0 : 0 ≤ B := by
    have := hgron a ⟨le_rfl, hab⟩
    rw [sub_self, gronwallBound_x0] at this
    exact dist_nonneg.trans (h0.trans this)
  have hB'0 : 0 < B' := lt_of_le_of_lt hB0 hBB
  have gr : ∀ c ∈ Icc a b, (∀ u ∈ Ico a c, f u ∈ S) →
      ∀ t ∈ Icc a c, dist (f t) (g t) ≤ B := by
    intro c hc hS t ht
    have hsub : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl hc.2
    have hsub' : Ico a c ⊆ Ico a b := Ico_subset_Ico le_rfl hc.2
    have key := dist_le_of_approx_trajectories_ODE_of_mem (v := F) (s := fun _ => S)
      (K := K) (f := f) (f' := fun t => F t (f t)) (εf := 0) (g := g) (g' := g') (εg := ε)
      (δ := δ) (a := a) (b := c)
      (fun t ht => hF t (hsub' ht)) (hf.mono hsub) (fun t ht => hf' t (hsub' ht))
      (fun t _ => by simp)
      hS (hg.mono hsub) (fun t ht => hg' t (hsub' ht)) (fun t ht => hdef t (hsub' ht))
      (fun t ht => htube t (hsub (Ico_subset_Icc_self ht)) _ (by rw [dist_self]; exact hB'0))
      h0 t ht
    rw [zero_add] at key
    exact key.trans (hgron t (hsub ht))
  set A : Set ℝ := {c | c ∈ Icc a b ∧ ∀ u ∈ Ico a c, f u ∈ S} with hA
  have haA : a ∈ A := ⟨⟨le_rfl, hab⟩, fun u hu => absurd hu.2 (not_lt.2 hu.1)⟩
  have hbdd : BddAbove A := ⟨b, fun c hc => hc.1.2⟩
  set T := sSup A with hT
  have hTa : a ≤ T := le_csSup hbdd haA
  have hTb : T ≤ b := csSup_le ⟨a, haA⟩ fun c hc => hc.1.2
  have hTS : ∀ u ∈ Ico a T, f u ∈ S := by
    intro u hu
    obtain ⟨c, hcA, huc⟩ := exists_lt_of_lt_csSup ⟨a, haA⟩ hu.2
    exact hcA.2 u ⟨hu.1, huc⟩
  have hTmem : T ∈ Icc a b := ⟨hTa, hTb⟩
  rcases eq_or_lt_of_le hTb with hTb' | hTb'
  · have h := gr T hTmem hTS
    rw [hTb'] at h
    exact h
  · exfalso
    have hTB : dist (f T) (g T) ≤ B := gr T hTmem hTS T ⟨hTa, le_rfl⟩
    have hcont : ContinuousWithinAt (fun t => dist (f t) (g t)) (Icc a b) T :=
      ((hf T hTmem).dist (hg T hTmem))
    obtain ⟨η, hη, hηb⟩ := Metric.continuousWithinAt_iff.1 hcont (B' - B) (by linarith)
    set c := min (T + η / 2) b with hc
    have hTc : T < c := lt_min (by linarith) hTb'
    have hcA : c ∈ A := by
      refine ⟨⟨by linarith, min_le_right _ _⟩, fun u hu => ?_⟩
      rcases lt_or_ge u T with huT | huT
      · exact hTS u ⟨hu.1, huT⟩
      · have huc : u < c := hu.2
        have hub : u ∈ Icc a b := ⟨hu.1, le_trans huc.le (min_le_right _ _)⟩
        have hdu : dist u T < η := by
          rw [Real.dist_eq, abs_of_nonneg (by linarith)]
          linarith [min_le_left (T + η / 2) b]
        have h1 := hηb hub hdu
        rw [Real.dist_eq] at h1
        have h2 : dist (f u) (g u) < B' := by
          have := (abs_lt.1 h1).2
          linarith
        exact htube u hub (f u) h2
    have := le_csSup hbdd hcA
    linarith

/-- The Lane–Emden field at time ξ. -/
noncomputable def leF (n : ℕ) (ξ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.2, -(2 / ξ * p.2) - p.1 ^ n)

/-- The slab |θ| ≤ TH. -/
def slab (TH : ℝ) : Set (ℝ × ℝ) := {p | |p.1| ≤ TH}

theorem pow_sub_le_slab (n : ℕ) {a b TH : ℝ} (ha : |a| ≤ TH) (hb : |b| ≤ TH) :
    |a ^ n - b ^ n| ≤ n * TH ^ (n - 1) * |a - b| := by
  have hm : max |a| |b| ≤ TH := max_le ha hb
  calc |a ^ n - b ^ n| ≤ |a - b| * n * max |a| |b| ^ (n - 1) := abs_pow_sub_pow_le a b n
    _ ≤ |a - b| * n * TH ^ (n - 1) := by gcongr
    _ = n * TH ^ (n - 1) * |a - b| := by ring

theorem lip_slab (n : ℕ) {ξ t0 TH K : ℝ} (ht0 : 0 < t0) (hξ : t0 ≤ ξ) (hK1 : 1 ≤ K)
    (hK : 2 / t0 + n * TH ^ (n - 1) ≤ K) :
    LipschitzOnWith (Real.toNNReal K) (leF n ξ) (slab TH) := by
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  have hK0 : (0 : ℝ) ≤ K := by linarith
  rw [Real.coe_toNNReal _ hK0]
  simp only [leF, Prod.dist_eq, Real.dist_eq]
  set m := max |p.1 - q.1| |p.2 - q.2|
  have hd1 : |p.1 - q.1| ≤ m := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ m := le_max_right _ _
  have hm : 0 ≤ m := (abs_nonneg _).trans hd1
  have hξ0 : 0 < ξ := lt_of_lt_of_le ht0 hξ
  refine max_le (by nlinarith) ?_
  have e : (-(2 / ξ * p.2) - p.1 ^ n) - (-(2 / ξ * q.2) - q.1 ^ n) =
      -(2 / ξ * (p.2 - q.2)) - (p.1 ^ n - q.1 ^ n) := by ring
  rw [e]
  have c1 := pow_sub_le_slab n (TH := TH) hp hq
  have c2 : |2 / ξ * (p.2 - q.2)| ≤ 2 / t0 * m := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul (div_le_div_of_nonneg_left (by norm_num) ht0 hξ) hd2 (abs_nonneg _)
      (by positivity)
  have c3 : n * TH ^ (n - 1) * |p.1 - q.1| ≤ n * TH ^ (n - 1) * m :=
    mul_le_mul_of_nonneg_left hd1 (by
      have hTH : 0 ≤ TH := (abs_nonneg _).trans hp
      positivity)
  calc |-(2 / ξ * (p.2 - q.2)) - (p.1 ^ n - q.1 ^ n)|
      ≤ |2 / ξ * (p.2 - q.2)| + |p.1 ^ n - q.1 ^ n| := by
        rw [sub_eq_add_neg, ← neg_add]; rw [abs_neg]; exact abs_add_le _ _
    _ ≤ 2 / t0 * m + n * TH ^ (n - 1) * m := by linarith
    _ = (2 / t0 + n * TH ^ (n - 1)) * m := by ring
    _ ≤ K * m := mul_le_mul_of_nonneg_right hK hm

/-- One validated step on the cell [t₀, t₀ + h] ⊆ (0, T] for every solution (θ, φ) of the
Lane–Emden system (derivatives within [0, T]). -/
theorem cell (n : ℕ) (pt pp : List ℚ) {θ φ : ℝ → ℝ} {T t0 h δ ε B TH K : ℝ}
    (ht0 : 0 < t0) (hT : t0 + h ≤ T) (hh : 0 < h) (hK1 : 1 ≤ K)
    (hK : 2 / t0 + n * TH ^ (n - 1) ≤ K) (hKh : K * h < 1) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hθ : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt θ (φ t) (Icc 0 T) t)
    (hφ : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt φ (-(2 / t * φ t) - θ t ^ n) (Icc 0 T) t)
    (ht1 : ∀ σ ∈ Icc 0 h, -(TH - 1 / 100) ≤ evalQ pt σ)
    (ht2 : ∀ σ ∈ Icc 0 h, evalQ pt σ ≤ TH - 1 / 100)
    (hd1 : ∀ σ ∈ Icc 0 h, |dEvalQ pt σ - evalQ pp σ| ≤ ε)
    (hd2 : ∀ σ ∈ Icc 0 h,
      |(t0 + σ) * dEvalQ pp σ + 2 * evalQ pp σ + (t0 + σ) * evalQ pt σ ^ n| ≤ ε * t0)
    (h0 : |θ t0 - evalQ pt 0| ≤ δ) (h0' : |φ t0 - evalQ pp 0| ≤ δ)
    (hB : δ * (1 / (1 - K * h)) + ε / K * (1 / (1 - K * h) - 1) ≤ B)
    (hBM : B < 1 / 100) :
    ∀ t ∈ Icc t0 (t0 + h), |θ t - evalQ pt (t - t0)| ≤ B ∧ |φ t - evalQ pp (t - t0)| ≤ B := by
  have hK0 : (0 : ℝ) < K := by linarith
  have hT0 : Icc t0 (t0 + h) ⊆ Icc 0 T := Icc_subset_Icc ht0.le hT
  have hs : ∀ t ∈ Icc t0 (t0 + h), t - t0 ∈ Icc 0 h := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set f : ℝ → ℝ × ℝ := fun t => (θ t, φ t) with hfdef
  set g : ℝ → ℝ × ℝ := fun t => (evalQ pt (t - t0), evalQ pp (t - t0)) with hg
  have hfd : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt f (leF n t (f t)) (Icc 0 T) t :=
    fun t ht => (hθ t ht).prodMk (hφ t ht)
  have key := tube_cell_t (F := leF n) (K := Real.toNNReal K) (S := slab TH) (f := f) (g := g)
    (g' := fun t => (dEvalQ pt (t - t0), dEvalQ pp (t - t0))) (a := t0) (b := t0 + h)
    (δ := δ) (ε := ε) (B := B) (B' := 1 / 100)
    (fun t ht => lip_slab n ht0 ht.1 hK1 hK) (by linarith)
    (fun t ht => ((hfd t ht).continuousWithinAt).mono hT0)
    (fun t ht => (hfd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨by linarith [ht.1, ht0], by linarith [ht.2]⟩))
    (((continuous_evalQ pt).comp (continuous_sub_right t0)).prodMk
      ((continuous_evalQ pp).comp (continuous_sub_right t0))).continuousOn
    (fun t _ => (((hasDerivAt_evalQ pt (t - t0)).comp_sub_const t t0).prodMk
      ((hasDerivAt_evalQ pp (t - t0)).comp_sub_const t t0)).hasDerivWithinAt)
    (fun t ht => by
      have hσ := hs t (Ico_subset_Icc_self ht)
      have htpos : 0 < t := lt_of_lt_of_le ht0 ht.1
      simp only [hg, leF, Prod.dist_eq, Real.dist_eq]
      refine max_le (hd1 _ hσ) ?_
      have h2 := hd2 _ hσ
      have et : t0 + (t - t0) = t := by ring
      rw [et] at h2
      have e : dEvalQ pp (t - t0) - (-(2 / t * evalQ pp (t - t0)) - evalQ pt (t - t0) ^ n) =
          (t * dEvalQ pp (t - t0) + 2 * evalQ pp (t - t0) + t * evalQ pt (t - t0) ^ n) / t := by
        field_simp
        ring
      rw [e, abs_div, abs_of_pos htpos, div_le_iff₀ htpos]
      exact h2.trans (mul_le_mul_of_nonneg_left ht.1 hε))
    (fun t ht z hz => by
      simp only [hg, Prod.dist_eq, Real.dist_eq, max_lt_iff] at hz
      have g1 := ht1 _ (hs t ht)
      have g2 := ht2 _ (hs t ht)
      have a1 := abs_lt.1 hz.1
      show |z.1| ≤ TH
      rw [abs_le]; constructor <;> linarith [a1.1, a1.2])
    hBM
    (by
      simp only [hfdef, hg, sub_self, Prod.dist_eq, Real.dist_eq]
      exact max_le h0 h0')
    (fun t ht => by
      rw [Real.coe_toNNReal _ hK0.le]
      have := gronwallBound_le_cell (K := K) hδ hε hK0
        (show t - t0 ≤ h by linarith [ht.2]) hh hKh
      exact this.trans hB)
  intro t ht
  have h1 := key t ht
  simp only [hfdef, hg, Prod.dist_eq, Real.dist_eq] at h1
  exact ⟨(le_max_left _ _).trans h1, (le_max_right _ _).trans h1⟩

/-- Crude lower bound p(σ) ≥ c₀ − h·Σ|cₖ₊₁|hᵏ on [0, h]. -/
theorem lower_of (p : List ℚ) {σ h : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ h) :
    ((p.headD 0 : ℚ) : ℝ) - h * evalQ (p.tail.map (fun c => |c|)) h ≤ evalQ p σ := by
  cases p with
  | nil => simp [evalQ]
  | cons c cs => simpa using evalQ_ge c cs h0 h1

/-- Crude upper bound p(σ) ≤ c₀ + h·Σ|cₖ₊₁|hᵏ on [0, h]. -/
theorem upper_of (p : List ℚ) {σ h : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ h) :
    evalQ p σ ≤ ((p.headD 0 : ℚ) : ℝ) + h * evalQ (p.tail.map (fun c => |c|)) h := by
  cases p with
  | nil => simp [evalQ]
  | cons c cs => simpa using evalQ_le c cs h0 h1

end Checked.Math.LENCell
