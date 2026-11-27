import Mathlib
import Readings.elliott
import ComparatorChallenges.OrdinaryTwoPointCorrelations
import ComparatorChallenges.OrdinaryElliott

/-! # Target O, family O60 (ordinary two-point correlations): closures against `OrdinaryTwoPointCorrelations`
(run 2026-11-27T1628Z).

Frozen statements (challenge `OrdinaryTwoPointCorrelations`, taken by name, never retyped):
`liouville_log_saving` (Theorem 1.1), `binary_corrected_elliott` (Theorem 1.2), `affine_corrected_elliott`
(Corollary 1.3). Their uniform nonpretentiousness is "for every `K`, eventually (in `N : ℕ`) every `|t| ≤ N` has
`K ≤ squaredDistance f (χ · exp(i t log ·)) N`", the squared distance over primes `≤ N`, without a square root.

Links proved here:
* Liouville: every reader's `(-1)^Ω` (A, C real; B complex; C's `Ω` is `primeFactorsList.length`) is Mathlib's
  `liouville` at `n ≥ 1`; the readers' determinant `≠ 0` in `ℤ` is the frozen `a₁b₂ ≠ a₂b₁` in `ℕ`; real absolute
  value of a real sum is the norm of its complex cast; `x ^ c` is `Real.rpow`.
* distance: `p^{it}` as the complex power `(p : ℂ) ^ (t I)` equals the frozen `exp(i t log p)` for `p > 0`
  (`twist_eq`); the readers' prime ranges (`Icc 1 ⌊N⌋₊`, `range (⌊N⌋₊ + 1)`) are the frozen `primesUpTo N`.
* nonpretentiousness: the readers' "inf of the distance → ∞" (A: for every `M` eventually `M ≤ D`; B: `⨅` over the
  subtype `Icc`; C: `sInf` of the image) gives the frozen form at `K` by taking `M = |K| + 1` (then `K ≤ M² ≤ D²`).
  Reader B conjugated only `χ(p)` and not `p^{it}` (the text conjugates the product); B's distance at `t` is the
  frozen one at `−t` (`distB_eq`), and `[−N, N]` is symmetric, so B's condition still gives the frozen one.
* averages: `(N)⁻¹ * Σ` and `(1/N) * Σ` are the frozen `Σ / N`.

The family's second challenge, `OrdinaryElliott` (`OAI.OrdinaryCorrelations.binary_corrected_elliott`), states
Theorem 1.2 again with its own definitions: one-boundedness at every `n` including `0`, the distance as a square root
over primes in `Icc 2 ⌊N⌋₊`, and nonpretentiousness as `sInf` of the distance over `[−N, N]` tending to `∞`. Each
reader's Theorem 1.2 is closed against it too (section `OrdinaryElliott`); reader A bounds `f` only at `n ≥ 1`, so
its functions are first set to `0` at `0`, which changes no hypothesis and no average (`zeroAt0`). -/

namespace TargetO.Elliott

open Filter Topology OAI.TwoPointCorrelations OAI.OrdinaryTwoPointCorrelations
open scoped ComplexConjugate

/-! ## Liouville -/

theorem lam_eq (n : ℕ) (hn : n ≠ 0) :
    OAI.TwoPointCorrelations.liouville n = ((ReaderA.liouville n : ℝ) : ℂ) := by
  simp [OAI.TwoPointCorrelations.liouville, ReaderA.liouville, ArithmeticFunction.liouville_apply hn]

theorem lamB_eq (n : ℕ) (hn : n ≠ 0) : OAI.TwoPointCorrelations.liouville n = ReaderB.liouville n := by
  simp [OAI.TwoPointCorrelations.liouville, ReaderB.liouville, ArithmeticFunction.liouville_apply hn]

theorem lamC_eq (n : ℕ) : ReaderC.liouville n = ReaderA.liouville n := by
  simp [ReaderC.liouville, ReaderA.liouville, ArithmeticFunction.cardFactors_apply]

theorem det_nat (a₁ a₂ b₁ b₂ : ℕ) (h : (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0) : a₁ * b₂ ≠ a₂ * b₁ := by
  intro e; apply h; have : ((a₁ * b₂ : ℕ) : ℤ) = ((a₂ * b₁ : ℕ) : ℤ) := by rw [e]
  push_cast at this; linarith

theorem sumA_eq (a₁ a₂ b₁ b₂ : ℕ) (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂) (N : ℕ) :
    affineSum OAI.TwoPointCorrelations.liouville OAI.TwoPointCorrelations.liouville a₁ a₂ b₁ b₂ N =
      ((∑ n ∈ Finset.Icc 1 N, ReaderA.liouville (a₁ * n + b₁) * ReaderA.liouville (a₂ * n + b₂) : ℝ) : ℂ) := by
  unfold affineSum
  push_cast
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  rw [lam_eq _ (by positivity), lam_eq _ (by positivity)]

theorem thm_A_core (frozen : type_of% @liouville_log_saving) :
    ∃ c : ℝ, 0 < c ∧ ∀ a₁ a₂ b₁ b₂ : ℕ, 1 ≤ a₁ → 1 ≤ a₂ → (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0 →
      ∃ C : ℝ, ∀ X : ℝ, 3 ≤ X →
        |∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ReaderA.liouville (a₁ * n + b₁) * ReaderA.liouville (a₂ * n + b₂)|
          ≤ C * (X / Real.log X ^ c) := by
  obtain ⟨c, hc, h⟩ := frozen
  refine ⟨c, hc, fun a₁ a₂ b₁ b₂ ha₁ ha₂ hdet => ?_⟩
  obtain ⟨C, _, hC⟩ := h a₁ a₂ b₁ b₂ (by omega) (by omega) (det_nat a₁ a₂ b₁ b₂ hdet)
  refine ⟨C, fun X hX => ?_⟩
  have := hC X hX
  rw [sumA_eq a₁ a₂ b₁ b₂ ha₁ ha₂, Complex.norm_real, Real.norm_eq_abs] at this
  rw [← mul_div_assoc]
  exact this

theorem closure_A_thm1 (frozen : type_of% @liouville_log_saving) : type_of% @ReaderA.reading_thm_1_1 :=
  thm_A_core frozen

theorem closure_C_thm1 (frozen : type_of% @liouville_log_saving) :
    type_of% @ReaderC.reading_liouville_affine_saving := by
  obtain ⟨c, hc, h⟩ := thm_A_core frozen
  refine ⟨c, hc, fun a₁ a₂ b₁ b₂ ha₁ ha₂ hdet => ?_⟩
  obtain ⟨C, hC⟩ := h a₁ a₂ b₁ b₂ ha₁ ha₂ hdet
  refine ⟨C, fun X hX => ?_⟩
  simp only [lamC_eq]
  rw [mul_div_assoc]; exact hC X hX

theorem closure_B_thm1 (frozen : type_of% @liouville_log_saving) : type_of% @ReaderB.readingThm1_1 := by
  obtain ⟨c, hc, h⟩ := frozen
  refine ⟨c, hc, fun a₁ a₂ b₁ b₂ ha₁ ha₂ hdet => ?_⟩
  obtain ⟨C, _, hC⟩ := h a₁ a₂ b₁ b₂ (by omega) (by omega) (det_nat a₁ a₂ b₁ b₂ hdet)
  refine ⟨C, fun X hX => ?_⟩
  have := hC X hX
  unfold affineSum at this
  rw [← mul_div_assoc]
  convert this using 2
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  rw [lamB_eq _ (by positivity), lamB_eq _ (by positivity)]

/-! ## The distance -/

theorem twist_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (p : ℕ) (hp : 0 < p) :
    characterTwist χ t p = χ (p : ZMod q) * (p : ℂ) ^ ((t : ℂ) * Complex.I) := by
  unfold characterTwist
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne')]
  congr 1
  have : (p : ℂ) = ((p : ℝ) : ℂ) := by push_cast; rfl
  rw [this, ← Complex.ofReal_log (by positivity)]
  push_cast; ring

theorem primes_eq (N : ℕ) : (Finset.Icc 1 N).filter Nat.Prime = primesUpTo N := by
  ext p; simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨h, hp⟩; exact ⟨⟨hp.one_lt.le, by omega⟩, hp⟩

theorem distA_eq (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) :
    ReaderA.distSq f χ t (N : ℝ) = squaredDistance f (characterTwist χ t) N := by
  unfold ReaderA.distSq squaredDistance
  rw [Nat.floor_natCast, primes_eq]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : 0 < p := (Finset.mem_filter.1 hp).2.pos
  rw [twist_eq χ t p hp']

theorem distC_eq (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) :
    ReaderC.distSq f χ t (N : ℝ) = squaredDistance f (characterTwist χ t) N := by
  unfold ReaderC.distSq squaredDistance primesUpTo
  rw [Nat.floor_natCast]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : 0 < p := (Finset.mem_filter.1 hp).2.pos
  rw [twist_eq χ t p hp']

/-- Reader B conjugates `χ(p)` only: its distance at `t` is the frozen one at `−t`. -/
theorem distB_eq (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) :
    ReaderB.distSq f χ t N = squaredDistance f (characterTwist χ (-t)) N := by
  unfold ReaderB.distSq squaredDistance primesUpTo
  refine Finset.sum_congr rfl fun p hp => ?_
  congr 3
  unfold characterTwist
  rw [map_mul, mul_assoc, ← Complex.exp_conj,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Finset.mem_filter.1 hp).2.pos.ne')]
  congr 2
  have : (p : ℂ) = ((p : ℝ) : ℂ) := by push_cast; rfl
  rw [this, ← Complex.ofReal_log (by positivity)]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

theorem sq_bound (K d : ℝ) (h : |K| + 1 ≤ Real.sqrt d) : K ≤ d := by
  have hM : 0 < |K| + 1 := by positivity
  have hd : 0 < d := Real.sqrt_pos.1 (lt_of_lt_of_le hM h)
  have h2 : (|K| + 1) ^ 2 ≤ d := by
    calc (|K| + 1) ^ 2 ≤ Real.sqrt d ^ 2 := by gcongr
      _ = d := Real.sq_sqrt hd.le
  nlinarith [le_abs_self K, abs_nonneg K]

theorem unpA (f : ℕ → ℂ) (h : ReaderA.UniformlyNonpretentious f) : UniformlyNonpretentious f := by
  intro q hq χ K
  obtain ⟨N₀, hN₀⟩ := h q hq χ (|K| + 1)
  filter_upwards [eventually_ge_atTop ⌈N₀⌉₊] with N hN t ht
  have hN' : N₀ ≤ (N : ℝ) := (Nat.le_ceil N₀).trans (by exact_mod_cast hN)
  have := hN₀ N hN' t ht
  rw [← distA_eq]
  exact sq_bound _ _ this

theorem unpC (f : ℕ → ℂ) (h : ReaderC.IsUnifNonpretentious f) : UniformlyNonpretentious f := by
  intro q hq χ K
  have h1 := (h q hq χ).comp tendsto_natCast_atTop_atTop
  filter_upwards [h1.eventually_ge_atTop (|K| + 1)] with N hN t ht
  simp only [Function.comp] at hN
  rw [← distC_eq]
  refine sq_bound _ _ (hN.trans (csInf_le ⟨0, ?_⟩ ⟨t, ⟨by linarith [neg_abs_le t], (le_abs_self t).trans ht⟩, rfl⟩))
  rintro _ ⟨s, _, rfl⟩; exact Real.sqrt_nonneg _

theorem unpB (f : ℕ → ℂ) (h : ReaderB.UniformlyNonpretentious f) : UniformlyNonpretentious f := by
  intro q hq χ K
  have : NeZero q := ⟨hq.ne'⟩
  filter_upwards [(h q χ).eventually_ge_atTop (|K| + 1)] with N hN t ht
  have hmem : (-t) ∈ Set.Icc (-(N : ℝ)) (N : ℝ) :=
    ⟨by linarith [le_abs_self t], by linarith [neg_abs_le t]⟩
  have hle := ciInf_le (f := fun s : Set.Icc (-(N : ℝ)) (N : ℝ) => ReaderB.dist' f χ s N)
    ⟨0, by rintro _ ⟨s, rfl⟩; exact Real.sqrt_nonneg _⟩ ⟨-t, hmem⟩
  have := sq_bound _ _ (hN.trans hle)
  rw [show (ReaderB.distSq f χ (-t) N) = squaredDistance f (characterTwist χ t) N by
    rw [distB_eq, neg_neg]] at this
  exact this

/-! ## Theorem 1.2 and Corollary 1.3 -/

theorem avg_eq (s : ℕ → ℂ) : (fun N : ℕ => (N : ℂ)⁻¹ * s N) = fun N => s N / (N : ℂ) := by
  funext N; rw [div_eq_mul_inv, mul_comm]

theorem avg_eq' (s : ℕ → ℂ) : (fun N : ℕ => (1 / (N : ℂ)) * s N) = fun N => s N / (N : ℂ) := by
  funext N; rw [one_div, div_eq_mul_inv, mul_comm]

theorem closure_A_thm2 (frozen : type_of% @binary_corrected_elliott) : type_of% @ReaderA.reading_thm_1_2 := by
  intro f₁ f₂ hf₁ hf₂ hd₁ hd₂ hunp h₁ h₂ hh
  rw [avg_eq (fun N => ∑ n ∈ Finset.Icc 1 N, f₁ (n + h₁) * f₂ (n + h₂))]
  exact frozen f₁ f₂ hf₁ hf₂ hd₁ hd₂ (hunp.imp (unpA f₁) (unpA f₂)) h₁ h₂ hh

theorem closure_A_cor (frozen : type_of% @affine_corrected_elliott) : type_of% @ReaderA.reading_cor_1_3 := by
  intro f₁ f₂ hf₁ hf₂ hd₁ hd₂ hunp a₁ a₂ b₁ b₂ ha₁ ha₂ hdet
  rw [avg_eq (fun N => ∑ n ∈ Finset.Icc 1 N, f₁ (a₁ * n + b₁) * f₂ (a₂ * n + b₂))]
  exact frozen f₁ f₂ hf₁ hf₂ hd₁ hd₂ (hunp.imp (unpA f₁) (unpA f₂)) a₁ a₂ b₁ b₂ (by omega) (by omega)
    (det_nat a₁ a₂ b₁ b₂ hdet)

theorem closure_B_thm2 (frozen : type_of% @binary_corrected_elliott) : type_of% @ReaderB.readingThm1_2 := by
  intro f₁ f₂ hf₁ hf₂ hunp h₁ h₂ hh
  rw [avg_eq' (fun N => ∑ n ∈ Finset.Icc 1 N, f₁ (n + h₁) * f₂ (n + h₂))]
  exact frozen f₁ f₂ hf₁.2 hf₂.2 (fun n _ => hf₁.1 n) (fun n _ => hf₂.1 n)
    (hunp.imp (unpB f₁) (unpB f₂)) h₁ h₂ hh

theorem closure_B_cor (frozen : type_of% @affine_corrected_elliott) : type_of% @ReaderB.readingCor1_3 := by
  intro f₁ f₂ hf₁ hf₂ hunp a₁ a₂ b₁ b₂ ha₁ ha₂ hdet
  rw [avg_eq' (fun N => ∑ n ∈ Finset.Icc 1 N, f₁ (a₁ * n + b₁) * f₂ (a₂ * n + b₂))]
  exact frozen f₁ f₂ hf₁.2 hf₂.2 (fun n _ => hf₁.1 n) (fun n _ => hf₂.1 n)
    (hunp.imp (unpB f₁) (unpB f₂)) a₁ a₂ b₁ b₂ (by omega) (by omega) (det_nat a₁ a₂ b₁ b₂ hdet)

theorem closure_C_thm2 (frozen : type_of% @binary_corrected_elliott) :
    type_of% @ReaderC.reading_binary_corrected_elliott := by
  intro f₁ f₂ hd₁ hd₂ hf₁ hf₂ hunp h₁ h₂ hh
  rw [avg_eq' (fun N => ∑ n ∈ Finset.Icc 1 N, f₁ (n + h₁) * f₂ (n + h₂))]
  exact frozen f₁ f₂ hf₁ hf₂ (fun n _ => hd₁ n) (fun n _ => hd₂ n) (hunp.imp (unpC f₁) (unpC f₂)) h₁ h₂ hh

theorem closure_C_cor (frozen : type_of% @affine_corrected_elliott) :
    type_of% @ReaderC.reading_affine_correlations := by
  intro f₁ f₂ hd₁ hd₂ hf₁ hf₂ hunp a₁ a₂ b₁ b₂ ha₁ ha₂ hdet
  rw [avg_eq' (fun N => ∑ n ∈ Finset.Icc 1 N, f₁ (a₁ * n + b₁) * f₂ (a₂ * n + b₂))]
  exact frozen f₁ f₂ hf₁ hf₂ (fun n _ => hd₁ n) (fun n _ => hd₂ n) (hunp.imp (unpC f₁) (unpC f₂))
    a₁ a₂ b₁ b₂ (by omega) (by omega) (det_nat a₁ a₂ b₁ b₂ hdet)

/-! ## Against the second challenge, `OrdinaryElliott` -/

section OrdinaryElliott

theorem oe_distSq_eq (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) :
    OAI.OrdinaryCorrelations.distanceSq f χ t N = squaredDistance f (characterTwist χ t) N := by
  unfold OAI.OrdinaryCorrelations.distanceSq squaredDistance
  rw [Nat.floor_natCast]
  have hset : (Finset.Icc 2 N).filter Nat.Prime = primesUpTo N := by
    ext p; simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨by omega, hp⟩
    · rintro ⟨h, hp⟩; exact ⟨⟨hp.two_le, by omega⟩, hp⟩
  rw [hset]
  rfl

/-- The strong form every reader's hypothesis gives: for every `M`, eventually every `|t| ≤ N` has
`M ≤ √(squared distance)`. -/
def Strong (f : ℕ → ℂ) : Prop :=
  ∀ q : ℕ, 0 < q → ∀ χ : DirichletCharacter ℂ q, ∀ M : ℝ,
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, |t| ≤ N → M ≤ Real.sqrt (squaredDistance f (characterTwist χ t) N)

theorem oe_of_strong (f : ℕ → ℂ) (h : Strong f) : OAI.OrdinaryCorrelations.UniformlyNonpretentious f := by
  intro q hq χ
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [h q hq χ M] with N hN
  refine le_csInf ⟨_, ⟨0, ⟨by simp, by positivity⟩, rfl⟩⟩ ?_
  rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
  unfold OAI.OrdinaryCorrelations.distance
  beta_reduce
  rw [oe_distSq_eq]
  exact hN t (abs_le.2 ⟨ht1, ht2⟩)

theorem strongA (f : ℕ → ℂ) (h : ReaderA.UniformlyNonpretentious f) : Strong f := by
  intro q hq χ M
  obtain ⟨N₀, hN₀⟩ := h q hq χ M
  filter_upwards [eventually_ge_atTop ⌈N₀⌉₊] with N hN t ht
  have hN' : N₀ ≤ (N : ℝ) := (Nat.le_ceil N₀).trans (by exact_mod_cast hN)
  have := hN₀ N hN' t ht
  unfold ReaderA.dist at this
  rwa [distA_eq] at this

theorem strongC (f : ℕ → ℂ) (h : ReaderC.IsUnifNonpretentious f) : Strong f := by
  intro q hq χ M
  have h1 := (h q hq χ).comp tendsto_natCast_atTop_atTop
  filter_upwards [h1.eventually_ge_atTop M] with N hN t ht
  simp only [Function.comp] at hN
  have := hN.trans (csInf_le ⟨0, by rintro _ ⟨s, _, rfl⟩; exact Real.sqrt_nonneg _⟩
    ⟨t, ⟨by linarith [neg_abs_le t], (le_abs_self t).trans ht⟩, rfl⟩)
  unfold ReaderC.dist' at this
  beta_reduce at this
  rwa [distC_eq] at this

theorem strongB (f : ℕ → ℂ) (h : ReaderB.UniformlyNonpretentious f) : Strong f := by
  intro q hq χ M
  have : NeZero q := ⟨hq.ne'⟩
  filter_upwards [(h q χ).eventually_ge_atTop M] with N hN t ht
  have hmem : (-t) ∈ Set.Icc (-(N : ℝ)) (N : ℝ) :=
    ⟨by linarith [le_abs_self t], by linarith [neg_abs_le t]⟩
  have hle := ciInf_le (f := fun s : Set.Icc (-(N : ℝ)) (N : ℝ) => ReaderB.dist' f χ s N)
    ⟨0, by rintro _ ⟨s, rfl⟩; exact Real.sqrt_nonneg _⟩ ⟨-t, hmem⟩
  have := hN.trans hle
  simp only [ReaderB.dist'] at this
  rwa [distB_eq, neg_neg] at this

/-- Setting a function to `0` at `0`. -/
def zeroAt0 (f : ℕ → ℂ) : ℕ → ℂ := fun n => if n = 0 then 0 else f n

theorem zeroAt0_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) : zeroAt0 f n = f n := by
  simp [zeroAt0, hn.ne']

theorem zeroAt0_mult (f : ℕ → ℂ) (h : ReaderA.IsMultiplicative f) :
    OAI.OrdinaryCorrelations.Multiplicative (zeroAt0 f) := by
  intro m n hm hn hmn
  rw [zeroAt0_pos f (Nat.mul_pos hm hn), zeroAt0_pos f hm, zeroAt0_pos f hn]
  exact h m n hm hn hmn

theorem zeroAt0_bdd (f : ℕ → ℂ) (h : ReaderA.DiscValued f) : OAI.OrdinaryCorrelations.OneBounded (zeroAt0 f) := by
  intro n
  by_cases hn : n = 0
  · simp [zeroAt0, hn]
  · rw [zeroAt0_pos f (Nat.pos_of_ne_zero hn)]; exact h n (Nat.pos_of_ne_zero hn)

theorem zeroAt0_sq (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) :
    squaredDistance (zeroAt0 f) (characterTwist χ t) N = squaredDistance f (characterTwist χ t) N := by
  unfold squaredDistance primesUpTo
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [zeroAt0_pos f (Finset.mem_filter.1 hp).2.pos]

theorem zeroAt0_strong (f : ℕ → ℂ) (h : Strong f) : Strong (zeroAt0 f) := by
  intro q hq χ M
  filter_upwards [h q hq χ M] with N hN t ht
  rw [zeroAt0_sq]; exact hN t ht

theorem closure_A_oe (frozen : type_of% @OAI.OrdinaryCorrelations.binary_corrected_elliott) :
    type_of% @ReaderA.reading_thm_1_2 := by
  intro f₁ f₂ hf₁ hf₂ hd₁ hd₂ hunp h₁ h₂ hh
  have := frozen (zeroAt0 f₁) (zeroAt0 f₂) (zeroAt0_bdd f₁ hd₁) (zeroAt0_bdd f₂ hd₂)
    (zeroAt0_mult f₁ hf₁) (zeroAt0_mult f₂ hf₂)
    (hunp.imp (fun h => oe_of_strong _ (zeroAt0_strong _ (strongA _ h)))
      (fun h => oe_of_strong _ (zeroAt0_strong _ (strongA _ h)))) h₁ h₂ hh
  unfold OAI.OrdinaryCorrelations.shiftAverage at this
  convert this using 2 with N
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  rw [zeroAt0_pos f₁ (by omega), zeroAt0_pos f₂ (by omega)]

theorem closure_B_oe (frozen : type_of% @OAI.OrdinaryCorrelations.binary_corrected_elliott) :
    type_of% @ReaderB.readingThm1_2 := by
  intro f₁ f₂ hf₁ hf₂ hunp h₁ h₂ hh
  have := frozen f₁ f₂ hf₁.1 hf₂.1 hf₁.2 hf₂.2
    (hunp.imp (fun h => oe_of_strong _ (strongB _ h)) (fun h => oe_of_strong _ (strongB _ h))) h₁ h₂ hh
  unfold OAI.OrdinaryCorrelations.shiftAverage at this
  convert this using 2 with N
  rw [one_div]

theorem closure_C_oe (frozen : type_of% @OAI.OrdinaryCorrelations.binary_corrected_elliott) :
    type_of% @ReaderC.reading_binary_corrected_elliott := by
  intro f₁ f₂ hd₁ hd₂ hf₁ hf₂ hunp h₁ h₂ hh
  have := frozen f₁ f₂ hd₁ hd₂ hf₁ hf₂
    (hunp.imp (fun h => oe_of_strong _ (strongC _ h)) (fun h => oe_of_strong _ (strongC _ h))) h₁ h₂ hh
  unfold OAI.OrdinaryCorrelations.shiftAverage at this
  convert this using 2 with N
  rw [one_div]

end OrdinaryElliott

end TargetO.Elliott

#print axioms TargetO.Elliott.closure_A_thm1
#print axioms TargetO.Elliott.closure_A_thm2
#print axioms TargetO.Elliott.closure_A_cor
#print axioms TargetO.Elliott.closure_B_thm1
#print axioms TargetO.Elliott.closure_B_thm2
#print axioms TargetO.Elliott.closure_B_cor
#print axioms TargetO.Elliott.closure_C_thm1
#print axioms TargetO.Elliott.closure_C_thm2
#print axioms TargetO.Elliott.closure_C_cor
#print axioms TargetO.Elliott.closure_A_oe
#print axioms TargetO.Elliott.closure_B_oe
#print axioms TargetO.Elliott.closure_C_oe
