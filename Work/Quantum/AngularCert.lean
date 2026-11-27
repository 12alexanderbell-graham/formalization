import Work.Quantum.AngularAssembly
import Work.Quantum.H2PlusConditional
import Work.Quantum.RegularUnique
/-!
# H₂⁺ route step 4 (i), (ii): the angular half of the certificate (run 2026-11-27T0828Z)

Hypotheses `hlo`, `hhi` of `RegularUnique.freeze_of_IVP_certificate`: g(k, a) < 0 < g(k, b) for every k in the
energy window [k₁, k₂] (`H2PlusConditional.k₁`, `k₂`, width 2·10⁻¹³), with g(k, A) = dM/ds at s = 1 =
∑ (n + 1) bₙ₊₁(k, A) (`AngularAssembly.g`, `ab`).

Method (no floating point): closed intervals with rational ends, evaluated by the kernel (`decide +kernel`).
* `run`: the recurrence of `ab` carried on intervals (k ∈ K, A ∈ AI, x ∈ X), with the partial sums
  ∑_{n<N} (n + 1) bₙ₊₁ of g and ∑_{n<N} bₙ xⁿ of M; `run_sound`: for every real k, A, x in the intervals the true
  coefficients and partial sums lie in the computed intervals (interval product, sum and positive scaling are sound: `mem_mul`, `mem_add`, `mem_smul`).
* `tail`: the rest of the series is bounded by the uniform geometric bound `ab_geom`,
  ∑_{n ≥ N} (n + 1) CB (2/3)ⁿ⁺¹ = CB (2/3)ᴺ⁺¹ (3N + 9) (`tail_le`).
* `g_neg_of_check`, `g_pos_of_check`: a passing Boolean check gives the sign of g on the whole k-interval.
* `g_lo`, `g_hi`: the two checks at a = 0.811729584623719, b = 0.811729584625801 (run 1628Z's bracket
  [0.8117295846247197, 0.8117295846248006] of the root over the window, widened by about 10⁻¹²), N = 130.
  Emulation: `runs/2026-11-27T0828Z/scripts/g_interval.py` (g(k, a) ≤ −3.6·10⁻¹³, g(k, b) ≥ 3.6·10⁻¹³).
* `M_pos` (step 4 (i), hypothesis `hM`): M(k, A, s) > 0 for every k in the window, A ∈ [a, b], s ∈ [0, 1], by the
  same run with intervals for A and for s (the whole of [0, 1] at once), partial sum ∑_{n<60} bₙ sⁿ, tail
  3 CB (2/3)⁶⁰ (`tailM_le`). Emulation: `runs/2026-11-27T0828Z/scripts/m_interval.py` (M ≥ 0.12).
* `freeze_of_radial_events`: the H₂⁺ freeze from the two radial shooting events alone (step 4 (iii) remains).
-/

namespace Work.Quantum.AngularCert
open Set Work.Quantum.AngularAssembly Work.Quantum.FluxSeries

/-- A closed interval with rational ends. -/
structure Iv where
  lo : ℚ
  hi : ℚ

/-- Membership of a real number. -/
def Iv.mem (x : ℝ) (i : Iv) : Prop := (i.lo : ℝ) ≤ x ∧ x ≤ (i.hi : ℝ)

def iadd (a b : Iv) : Iv := ⟨a.lo + b.lo, a.hi + b.hi⟩
def ineg (a : Iv) : Iv := ⟨-a.hi, -a.lo⟩
/-- Scaling by a non-negative rational. -/
def ismul (c : ℚ) (a : Iv) : Iv := ⟨c * a.lo, c * a.hi⟩
def imul (a b : Iv) : Iv :=
  ⟨min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)),
   max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))⟩

theorem mem_add {x y : ℝ} {a b : Iv} (hx : Iv.mem x a) (hy : Iv.mem y b) : Iv.mem (x + y) (iadd a b) := by
  unfold Iv.mem iadd at *; push_cast; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem mem_neg {x : ℝ} {a : Iv} (hx : Iv.mem x a) : Iv.mem (-x) (ineg a) := by
  unfold Iv.mem ineg at *; push_cast; constructor <;> linarith [hx.1, hx.2]

theorem mem_smul {x : ℝ} {a : Iv} {c : ℚ} (hc : 0 ≤ c) (hx : Iv.mem x a) : Iv.mem ((c : ℝ) * x) (ismul c a) := by
  unfold Iv.mem ismul at *
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  push_cast
  exact ⟨mul_le_mul_of_nonneg_left hx.1 hc', mul_le_mul_of_nonneg_left hx.2 hc'⟩

/-- A product of two reals in two intervals lies between the least and the greatest corner product. -/
theorem mem_mul {x y : ℝ} {a b : Iv} (hx : Iv.mem x a) (hy : Iv.mem y b) : Iv.mem (x * y) (imul a b) := by
  unfold Iv.mem imul at *
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  set p := (a.lo : ℝ); set q := (a.hi : ℝ); set r := (b.lo : ℝ); set s := (b.hi : ℝ)
  push_cast
  -- x y is bilinear: it lies between its values at the corners
  have e1 : min (min (p * r) (p * s)) (min (q * r) (q * s)) ≤ x * y := by
    rcases le_total 0 y with hy0 | hy0
    · have : p * y ≤ x * y := mul_le_mul_of_nonneg_right h1 hy0
      have : min (p * r) (p * s) ≤ p * y := by
        rcases le_total 0 p with hp | hp
        · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left h3 hp)
        · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left h4 hp)
      linarith [min_le_left (min (p * r) (p * s)) (min (q * r) (q * s))]
    · have : q * y ≤ x * y := mul_le_mul_of_nonpos_right h2 hy0
      have : min (q * r) (q * s) ≤ q * y := by
        rcases le_total 0 q with hq | hq
        · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left h3 hq)
        · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left h4 hq)
      linarith [min_le_right (min (p * r) (p * s)) (min (q * r) (q * s))]
  have e2 : x * y ≤ max (max (p * r) (p * s)) (max (q * r) (q * s)) := by
    rcases le_total 0 y with hy0 | hy0
    · have : x * y ≤ q * y := mul_le_mul_of_nonneg_right h2 hy0
      have : q * y ≤ max (q * r) (q * s) := by
        rcases le_total 0 q with hq | hq
        · exact (mul_le_mul_of_nonneg_left h4 hq).trans (le_max_right _ _)
        · exact (mul_le_mul_of_nonpos_left h3 hq).trans (le_max_left _ _)
      linarith [le_max_right (max (p * r) (p * s)) (max (q * r) (q * s))]
    · have : x * y ≤ p * y := mul_le_mul_of_nonpos_right h1 hy0
      have : p * y ≤ max (p * r) (p * s) := by
        rcases le_total 0 p with hp | hp
        · exact (mul_le_mul_of_nonneg_left h4 hp).trans (le_max_right _ _)
        · exact (mul_le_mul_of_nonpos_left h3 hp).trans (le_max_left _ _)
      linarith [le_max_left (max (p * r) (p * s)) (max (q * r) (q * s))]
  exact ⟨e1, e2⟩

/-- The state after n steps: enclosures of bₙ, bₙ₊₁, bₙ₊₂, of ∑_{j<n} (j + 1) bⱼ₊₁ (g's partial sum), of
∑_{j<n} bⱼ xʲ (M's partial sum at a point x of the interval X) and of xⁿ. -/
structure St where
  b0 : Iv
  b1 : Iv
  b2 : Iv
  gs : Iv
  ms : Iv
  pw : Iv

/-- One step of the recurrence (`ab_succ3`) on intervals, at step index n, for k ∈ K, A ∈ AI, x ∈ X. -/
def step (K AI X : Iv) (n : ℕ) (st : St) : St :=
  let c : Iv := ⟨((n : ℚ) + 2) * ((n : ℚ) + 3) - K.hi + AI.lo, ((n : ℚ) + 2) * ((n : ℚ) + 3) - K.lo + AI.hi⟩
  let num := iadd (iadd (imul c st.b2) (imul (ismul 2 K) st.b1)) (ineg (imul K st.b0))
  ⟨st.b1, st.b2, ismul (1 / (2 * ((n : ℚ) + 3) ^ 2)) num, iadd st.gs (ismul ((n : ℚ) + 1) st.b1),
    iadd st.ms (imul st.b0 st.pw), imul st.pw X⟩

/-- The start: b₀ = 1, b₁ = (A − k)/2, b₂ = ((2 − k + A) b₁ + 2k)/8, empty sums, x⁰ = 1. -/
def start (K AI : Iv) : St :=
  let b1 : Iv := ⟨(AI.lo - K.hi) / 2, (AI.hi - K.lo) / 2⟩
  ⟨⟨1, 1⟩, b1, ismul (1 / 8) (iadd (imul ⟨2 - K.hi + AI.lo, 2 - K.lo + AI.hi⟩ b1) (ismul 2 K)), ⟨0, 0⟩,
    ⟨0, 0⟩, ⟨1, 1⟩⟩

/-- n steps. -/
def run (K AI X : Iv) : ℕ → St
  | 0 => start K AI
  | n + 1 => step K AI X n (run K AI X n)

/-- The partial sums of g. -/
noncomputable def S (k A : ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, ((j : ℝ) + 1) * ab k A (j + 1)

/-- The partial sums of M. -/
noncomputable def SM (k A x : ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, ab k A j * x ^ j

/-- The invariant of `run`. -/
def Inv (k A x : ℝ) (n : ℕ) (st : St) : Prop :=
  Iv.mem (ab k A n) st.b0 ∧ Iv.mem (ab k A (n + 1)) st.b1 ∧ Iv.mem (ab k A (n + 2)) st.b2 ∧
    Iv.mem (S k A n) st.gs ∧ Iv.mem (SM k A x n) st.ms ∧ Iv.mem (x ^ n) st.pw

theorem run_sound (K AI X : Iv) {k A x : ℝ} (hk : Iv.mem k K) (hA : Iv.mem A AI) (hx : Iv.mem x X) :
    ∀ n, Inv k A x n (run K AI X n) := by
  have hK2 : Iv.mem (2 * k) (ismul 2 K) := by
    have := mem_smul (c := 2) (by norm_num) hk; simpa using this
  intro n
  induction n with
  | zero =>
    have h1 : Iv.mem (ab k A 1) ⟨(AI.lo - K.hi) / 2, (AI.hi - K.lo) / 2⟩ := by
      unfold Iv.mem at *; simp only [ab]; push_cast; constructor <;> linarith [hk.1, hk.2, hA.1, hA.2]
    refine ⟨?_, h1, ?_, ?_, ?_, ?_⟩
    · simp [Iv.mem, ab, run, start]
    · have hc : Iv.mem (2 - k + A) ⟨2 - K.hi + AI.lo, 2 - K.lo + AI.hi⟩ := by
        unfold Iv.mem at *; push_cast; constructor <;> linarith [hk.1, hk.2, hA.1, hA.2]
      have := mem_smul (c := 1 / 8) (by norm_num) (mem_add (mem_mul hc h1) hK2)
      simp only [run, start]
      convert this using 1
      simp only [ab]; push_cast; ring
    · simp [Iv.mem, S, run, start]
    · simp [Iv.mem, SM, run, start]
    · simp [Iv.mem, run, start]
  | succ n ih =>
    obtain ⟨i0, i1, i2, is, im, ip⟩ := ih
    refine ⟨i1, i2, ?_, ?_, ?_, ?_⟩
    · have hc : Iv.mem (((n : ℝ) + 2) * ((n : ℝ) + 3) - k + A)
          ⟨((n : ℚ) + 2) * ((n : ℚ) + 3) - K.hi + AI.lo, ((n : ℚ) + 2) * ((n : ℚ) + 3) - K.lo + AI.hi⟩ := by
        unfold Iv.mem at *; push_cast; constructor <;> linarith [hk.1, hk.2, hA.1, hA.2]
      have hnum := mem_add (mem_add (mem_mul hc i2) (mem_mul hK2 i1)) (mem_neg (mem_mul hk i0))
      have hpos : (0 : ℚ) ≤ 1 / (2 * ((n : ℚ) + 3) ^ 2) := by positivity
      have := mem_smul hpos hnum
      simp only [run, step]
      convert this using 1
      rw [show n + 1 + 2 = n + 3 by ring, ab_succ3]
      push_cast; ring
    · have := mem_add is (mem_smul (c := (n : ℚ) + 1) (by positivity) i1)
      simp only [run, step]
      convert this using 1
      simp only [S, Finset.sum_range_succ]; push_cast; ring
    · have := mem_add im (mem_mul i0 ip)
      simp only [run, step]
      convert this using 1
      simp only [SM, Finset.sum_range_succ]
    · have := mem_mul ip hx
      simp only [run, step]
      convert this using 1
      ring

/-- The tail bound: CB (2/3)ᴺ⁺¹ (3N + 9) = ∑_{n ≥ N} (n + 1) CB (2/3)ⁿ⁺¹. -/
def tailQ (N : ℕ) : ℚ := (9 / 4) ^ 9 * (2 / 3) ^ (N + 1) * (3 * N + 9)

theorem hasSum_tail (N : ℕ) :
    HasSum (fun n : ℕ => ((n + N : ℕ) + 1 : ℝ) * (CB * (2 / 3 : ℝ) ^ (n + N + 1))) (tailQ N : ℝ) := by
  have hq : ‖(2 / 3 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hq
  have h2 := hasSum_geometric_of_norm_lt_one hq
  have h := (h1.add (h2.mul_left ((N : ℝ) + 1))).mul_left (CB * (2 / 3 : ℝ) ^ (N + 1))
  unfold tailQ
  simp only [CB] at h ⊢
  convert h using 1
  · funext n; push_cast; ring
  · norm_num; ring

theorem summable_d1 {k A : ℝ} (hb : Box k A) : Summable (fun n => d1 (ab k A) n) := by
  have hs := (hasSum_tail 0).summable
  refine Summable.of_norm_bounded hs (fun n => ?_)
  rw [Real.norm_eq_abs, d1, abs_mul, abs_of_nonneg (by positivity)]
  simp only [add_zero]
  exact mul_le_mul_of_nonneg_left (ab_geom hb (n + 1)) (by positivity)

theorem g_eq {k A : ℝ} : g k A = ∑' n, d1 (ab k A) n := by
  simp [g, Ms]

/-- g differs from its partial sum Sₙ by at most the tail bound. -/
theorem tail_le {k A : ℝ} (hb : Box k A) (N : ℕ) : |g k A - S k A N| ≤ tailQ N := by
  have hs := summable_d1 hb
  rw [g_eq, ← hs.sum_add_tsum_nat_add N]
  have hS : S k A N = ∑ i ∈ Finset.range N, d1 (ab k A) i := by simp [S, d1]
  rw [hS, add_sub_cancel_left]
  have hT := hasSum_tail N
  have hs' : Summable (fun n => d1 (ab k A) (n + N)) := (summable_nat_add_iff N).mpr hs
  calc |∑' n, d1 (ab k A) (n + N)| ≤ ∑' n, |d1 (ab k A) (n + N)| := by
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs'.norm
    _ ≤ ∑' n : ℕ, ((n + N : ℕ) + 1 : ℝ) * (CB * (2 / 3 : ℝ) ^ (n + N + 1)) := by
        refine hs'.abs.tsum_le_tsum (fun n => ?_) hT.summable
        rw [d1, abs_mul, abs_of_nonneg (by positivity)]
        push_cast
        exact mul_le_mul_of_nonneg_left (ab_geom hb (n + N + 1)) (by positivity)
    _ = tailQ N := hT.tsum_eq

/-- The Boolean checks. -/
def checkNeg (K : Iv) (A : ℚ) (N : ℕ) : Bool := decide ((run K ⟨A, A⟩ ⟨1, 1⟩ N).gs.hi + tailQ N < 0)
def checkPos (K : Iv) (A : ℚ) (N : ℕ) : Bool := decide (0 < (run K ⟨A, A⟩ ⟨1, 1⟩ N).gs.lo - tailQ N)

theorem g_neg_of_check {K : Iv} {A : ℚ} {N : ℕ} (h : checkNeg K A N = true) {k : ℝ} (hk : Iv.mem k K)
    (hb : Box k A) : g k A < 0 := by
  have hs := (run_sound K ⟨A, A⟩ ⟨1, 1⟩ (x := 1) hk ⟨le_refl _, le_refl _⟩ (by simp [Iv.mem]) N).2.2.2.1
  have ht := tail_le hb N
  have hc : (((run K ⟨A, A⟩ ⟨1, 1⟩ N).gs.hi + tailQ N : ℚ) : ℝ) < 0 := by
    exact_mod_cast (of_decide_eq_true h)
  push_cast at hc
  linarith [hs.2, (abs_le.mp ht).2]

theorem g_pos_of_check {K : Iv} {A : ℚ} {N : ℕ} (h : checkPos K A N = true) {k : ℝ} (hk : Iv.mem k K)
    (hb : Box k A) : 0 < g k A := by
  have hs := (run_sound K ⟨A, A⟩ ⟨1, 1⟩ (x := 1) hk ⟨le_refl _, le_refl _⟩ (by simp [Iv.mem]) N).2.2.2.1
  have ht := tail_le hb N
  have hc : (0 : ℝ) < (((run K ⟨A, A⟩ ⟨1, 1⟩ N).gs.lo - tailQ N : ℚ) : ℝ) := by
    exact_mod_cast (of_decide_eq_true h)
  push_cast at hc
  linarith [hs.1, (abs_le.mp ht).1]

/-- The tail bound of M on [−1, 1]: ∑_{n ≥ N} CB (2/3)ⁿ = 3 CB (2/3)ᴺ. -/
def tailMQ (N : ℕ) : ℚ := 3 * (9 / 4) ^ 9 * (2 / 3) ^ N

theorem hasSum_tailM (N : ℕ) : HasSum (fun n : ℕ => CB * (2 / 3 : ℝ) ^ (n + N)) (tailMQ N : ℝ) := by
  have hq : ‖(2 / 3 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num
  have h := (hasSum_geometric_of_norm_lt_one hq).mul_left (CB * (2 / 3 : ℝ) ^ N)
  unfold tailMQ
  simp only [CB] at h ⊢
  push_cast
  convert h using 1
  · funext n; ring
  · norm_num; ring

/-- M differs from its partial sum by at most the tail bound, for |x| ≤ 1. -/
theorem tailM_le {k A x : ℝ} (hb : Box k A) (hx : |x| ≤ 1) (N : ℕ) : |M k A x - SM k A x N| ≤ tailMQ N := by
  have hbd : ∀ n, |ab k A n * x ^ n| ≤ CB * (2 / 3 : ℝ) ^ n := fun n => by
    rw [abs_mul, abs_pow]
    calc |ab k A n| * |x| ^ n ≤ CB * (2 / 3 : ℝ) ^ n * 1 := by
          gcongr
          · exact le_trans (abs_nonneg _) (ab_geom hb n)
          · exact ab_geom hb n
          · exact pow_le_one₀ (abs_nonneg x) hx
      _ = _ := mul_one _
  have hs : Summable (fun n => ab k A n * x ^ n) := by
    have := (hasSum_tailM 0).summable
    simp only [add_zero] at this
    exact Summable.of_norm_bounded this (fun n => by rw [Real.norm_eq_abs]; exact hbd n)
  unfold M
  rw [← hs.sum_add_tsum_nat_add N]
  have hS : SM k A x N = ∑ i ∈ Finset.range N, ab k A i * x ^ i := rfl
  rw [hS, add_sub_cancel_left]
  have hT := hasSum_tailM N
  have hs' : Summable (fun n => ab k A (n + N) * x ^ (n + N)) := (summable_nat_add_iff N).mpr hs
  calc |∑' n, ab k A (n + N) * x ^ (n + N)| ≤ ∑' n, |ab k A (n + N) * x ^ (n + N)| := by
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs'.norm
    _ ≤ ∑' n : ℕ, CB * (2 / 3 : ℝ) ^ (n + N) := hs'.abs.tsum_le_tsum (fun n => hbd (n + N)) hT.summable
    _ = tailMQ N := hT.tsum_eq

/-- The Boolean check of M > 0 on X ⊆ [−1, 1]. -/
def checkM (K AI X : Iv) (N : ℕ) : Bool := decide (0 < (run K AI X N).ms.lo - tailMQ N)

theorem M_pos_of_check {K AI X : Iv} {N : ℕ} (h : checkM K AI X N = true) {k A x : ℝ} (hk : Iv.mem k K)
    (hA : Iv.mem A AI) (hx : Iv.mem x X) (hx1 : |x| ≤ 1) (hb : Box k A) : 0 < M k A x := by
  have hs := (run_sound K AI X hk hA hx N).2.2.2.2.1
  have ht := tailM_le hb hx1 N
  have hc : (0 : ℝ) < (((run K AI X N).ms.lo - tailMQ N : ℚ) : ℝ) := by
    exact_mod_cast (of_decide_eq_true h)
  push_cast at hc
  linarith [hs.1, (abs_le.mp ht).1]

/-! The window and the bracket. -/

def Kw : Iv := ⟨22052684289898 / 10 ^ 13, 22052684289900 / 10 ^ 13⟩
def aQ : ℚ := 811729584623719 / 10 ^ 15
def bQ : ℚ := 811729584625801 / 10 ^ 15

theorem check_lo : checkNeg Kw aQ 130 = true := by decide +kernel
theorem check_hi : checkPos Kw bQ 130 = true := by decide +kernel
theorem check_M : checkM Kw ⟨aQ, bQ⟩ ⟨0, 1⟩ 60 = true := by decide +kernel

theorem mem_Kw {k : ℝ} (hk : k ∈ Icc H2PlusConditional.k₁ H2PlusConditional.k₂) : Iv.mem k Kw := by
  unfold Iv.mem Kw; unfold H2PlusConditional.k₁ H2PlusConditional.k₂ at hk; push_cast; exact hk

theorem box_of {k : ℝ} (hk : k ∈ Icc H2PlusConditional.k₁ H2PlusConditional.k₂) {A : ℝ} (hA : 0 ≤ A)
    (hA' : A ≤ 1) : Box k A := by
  unfold H2PlusConditional.k₁ H2PlusConditional.k₂ at hk
  obtain ⟨h1, h2⟩ := hk
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- Hypothesis `hlo` of `RegularUnique.freeze_of_IVP_certificate` at a = 0.811729584623719. -/
theorem g_lo : ∀ k ∈ Icc H2PlusConditional.k₁ H2PlusConditional.k₂, g k (aQ : ℝ) < 0 := fun k hk =>
  g_neg_of_check check_lo (mem_Kw hk) (box_of hk (by unfold aQ; norm_num) (by unfold aQ; norm_num))

/-- Hypothesis `hhi` of `RegularUnique.freeze_of_IVP_certificate` at b = 0.811729584625801. -/
theorem g_hi : ∀ k ∈ Icc H2PlusConditional.k₁ H2PlusConditional.k₂, 0 < g k (bQ : ℝ) := fun k hk =>
  g_pos_of_check check_hi (mem_Kw hk) (box_of hk (by unfold bQ; norm_num) (by unfold bQ; norm_num))

/-- Hypothesis `hM` of `RegularUnique.freeze_of_IVP_certificate`: M > 0 on [0, 1] for every (k, A) of the box
(one interval for s, N = 60; the emulation `runs/2026-11-27T0828Z/scripts/m_interval.py` gives M ≥ 0.12). -/
theorem M_pos : ∀ k ∈ Icc H2PlusConditional.k₁ H2PlusConditional.k₂, ∀ A ∈ Icc (aQ : ℝ) (bQ : ℝ),
    ∀ s ∈ Icc (0 : ℝ) 1, 0 < M k A s := fun k hk A hA s hs =>
  M_pos_of_check check_M (mem_Kw hk) (by unfold Iv.mem; exact hA) (by unfold Iv.mem; push_cast; exact hs)
    (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩)
    (box_of hk (le_trans (by unfold aQ; norm_num) hA.1) (le_trans hA.2 (by unfold bQ; norm_num)))

/-- The H₂⁺ freeze with the whole angular part of the certificate discharged (step 4 (i) `M_pos`, step 4 (ii)
`g_lo`, `g_hi`): what remains is the pair of radial shooting events (step 4 (iii)). -/
theorem freeze_of_radial_events
    (hunder : ∀ A ∈ Icc (aQ : ℝ) (bQ : ℝ), RegularUnique.UnderIVP H2PlusConditional.k₁ A)
    (hover : ∀ A ∈ Icc (aQ : ℝ) (bQ : ℝ), RegularUnique.OverIVP H2PlusConditional.k₂ A) :
    H2PlusBlindClosed.Freeze :=
  RegularUnique.freeze_of_IVP_certificate (by unfold aQ; norm_num) (by unfold aQ bQ; norm_num)
    (by unfold bQ; norm_num) M_pos g_lo g_hi hunder hover

end Work.Quantum.AngularCert
