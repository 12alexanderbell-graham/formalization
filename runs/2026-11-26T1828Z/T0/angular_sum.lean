import Mathlib

/-!
# Target 0, the sum over angular harmonics (PROMPT standing instruction 11, Alexander 2026-11-26 ~17:45Z)

Chandrasekaran, "An algebraic quantization of gravity from the null cone", arXiv 2611.34924v1 (the only
version; source `main.tex` read in full by run 2026-11-26T1828Z, see `README.md` of that run).

The certified (4.33) (`runs/2026-11-26T1529Z/T0/closure_a.lean`) is for one polarization and one angular
harmonic: Sec. 4.4, "At fixed corner area 𝒜, we select one polarization and one real valued angular
harmonic." This file asks what the paper's own definitions give when the same pair insertion runs over
every radiative harmonic.

Paper inputs used (each is a definition or a sentence of the paper, not a choice of this file):
* Mode labels. Sec. 4.2, footnote to (4.7): "products of angular and radial basis functions provide a
  countable basis"; the Gaussian state is the product over *all* modes, (4.7).
  App. D.3: "tensor harmonics normalized on the unit sphere ... I = (j,m,p), with p distinguishing the two
  polarizations"; "The radiative harmonics start at j = 2". So for j ≤ L the labels are
  {(j, m, p) : 2 ≤ j ≤ L, −j ≤ m ≤ j, p ∈ {0,1}} (`harmonics`).
* Variance per mode. Sec. 4.4: "The variance has the short wavelength dependence of the squared amplitude
  of one graviton", (4.32) (Δq_k)² = 1/(2sk). App. D.3, before (D.31): "For one graviton of radial
  frequency |k|, the symplectic form fixes s|k| |h_I|² at a given radial profile": the one-graviton
  normalization carries no dependence on the harmonic I (the symplectic form (D.33a) has no j-dependent
  factor; j enters only the focusing cost Q[h], which bounds states of the clock-restricted diamond space,
  not the fixed-area Fock space 𝒦_𝒜 of Sec. 4.4). No sentence of the paper gives a variance depending on j.
  So the paper's variance in harmonic I, radial mode k, is `variance s k` for every I.
* Mode independence. The first equality of (4.33) (certified: `single_mode`, connected value zero between
  different modes) applied with the mode index running over (I, k): the connected two-point function of
  the summed insertions is the sum of the per-mode values 2 (Δq_k)⁴ e^{−2ik/s}.
* The phase. The boundary unitary of (4.32) rotates radial mode k by e^{−ik/s}: an affine shift along the
  generators, the same in every harmonic.

Definitions `variance`, `pairPhase`, `Li2` are copied verbatim from the blind reading
`runs/2026-11-26T1529Z/T0/reading.lean` (namespace `T0`).
-/

open Complex Filter Topology Finset

noncomputable section

namespace T0

/-- "(Δq_k)^2 = 1/(2sk)"  (4.32). The variance as a function of s and the mode number k. -/
def variance (s : ℝ) (k : ℕ) : ℝ := 1 / (2 * s * k)

/-- "yielding the pair phase e^{−2ik/s}" (Figure 20) / "the two phases multiply, yielding
exp(−2ik/s)" (4.33 text). -/
def pairPhase (s : ℝ) (k : ℕ) : ℂ := Complex.exp (-(2 * Complex.I * k / s))

/-- Dilogarithm for |z| ≤ 1, as instructed: Li₂(z) = Σ_{k≥1} z^k / k². -/
def Li2 (z : ℂ) : ℂ := ∑' k : ℕ, z ^ (k + 1) / ((k : ℂ) + 1) ^ 2

end T0

namespace ExternalT0.Angular

open T0

/-! ## The labels of the radiative harmonics -/

/-- Radiative tensor-harmonic labels I = (j, m, p) with j ≤ L: 2 ≤ j ≤ L, −j ≤ m ≤ j, p ∈ Fin 2. -/
def harmonics (L : ℕ) : Finset (Σ _ : ℕ, ℤ × Fin 2) :=
  (Finset.Icc 2 L).sigma fun j => Finset.Icc (-(j : ℤ)) j ×ˢ (Finset.univ : Finset (Fin 2))

/-- Number of radiative harmonics with j ≤ L, both polarizations: Σ_{j=2}^{L} 2(2j+1). -/
theorem card_harmonics (L : ℕ) : (harmonics L).card = ∑ j ∈ Finset.Icc 2 L, 2 * (2 * j + 1) := by
  unfold harmonics
  rw [Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.card_product, Int.card_Icc, Finset.card_univ, Fintype.card_fin]
  omega

theorem le_card_harmonics (L : ℕ) : L - 1 ≤ (harmonics L).card := by
  rw [card_harmonics]
  calc L - 1 = ∑ _j ∈ Finset.Icc 2 L, 1 := by simp
    _ ≤ ∑ j ∈ Finset.Icc 2 L, 2 * (2 * j + 1) := Finset.sum_le_sum fun j _ => by omega

/-! ## One harmonic: the certified radial sum (proof as in `closure_a.lean`) -/

lemma sum_Icc_shift {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, f k = ∑ k ∈ Finset.range N, f (k + 1) := by
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' f 0 N 1]
  rfl

lemma norm_pairPhase (s : ℝ) (k : ℕ) : ‖pairPhase s k‖ = 1 := by
  unfold pairPhase
  rw [Complex.norm_exp]
  have : (-(2 * Complex.I * (k : ℂ) / (s : ℂ))).re = 0 := by
    simp [Complex.div_re, Complex.mul_re]
  rw [this, Real.exp_zero]

lemma pairPhase_pow (s : ℝ) (k : ℕ) :
    pairPhase s k = Complex.exp (-(2 * Complex.I / s)) ^ k := by
  unfold pairPhase; rw [← Complex.exp_nat_mul]; congr 1; ring

lemma summable_inv_sq_succ : Summable (fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr one_lt_two)
  simpa using this

lemma summable_Li2_terms {z : ℂ} (hz : ‖z‖ = 1) :
    Summable (fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1) ^ 2) := by
  refine Summable.of_norm_bounded summable_inv_sq_succ (fun k => ?_)
  rw [norm_div, norm_pow, hz, one_pow, norm_pow]
  have : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
    have := Complex.norm_natCast (k + 1); push_cast at this; exact this
  rw [this]; exact le_of_eq (one_div _)

/-- The radial sum of one harmonic, (4.33): Σ_{k=1}^N 2(Δq_k)⁴ e^{−2ik/s} → Li₂(e^{−2i/s})/(2s²). -/
theorem radial_sum (s : ℝ) (hs : 0 < s) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, 2 * ((variance s k) ^ 2 : ℝ) * pairPhase s k)
      atTop (𝓝 (Li2 (Complex.exp (-(2 * Complex.I / s))) / (2 * (s : ℂ) ^ 2))) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  set z := Complex.exp (-(2 * Complex.I / s)) with hz
  have hzn : ‖z‖ = 1 := by
    have := norm_pairPhase s 1; rw [pairPhase_pow, pow_one] at this; exact this
  have hterm : ∀ k : ℕ, (2 * ((variance s (k + 1)) ^ 2 : ℝ) * pairPhase s (k + 1) : ℂ)
      = z ^ (k + 1) / ((k : ℂ) + 1) ^ 2 / (2 * (s : ℂ) ^ 2) := by
    intro k
    rw [pairPhase_pow, ← hz]; unfold variance; push_cast
    have : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    field_simp
  have hL : HasSum (fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1) ^ 2 / (2 * (s : ℂ) ^ 2))
      (Li2 z / (2 * (s : ℂ) ^ 2)) := (summable_Li2_terms hzn).hasSum.div_const _
  refine hL.tendsto_sum_nat.congr (fun N => ?_)
  rw [sum_Icc_shift (fun k => (2 * ((variance s k) ^ 2 : ℝ) * pairPhase s k : ℂ))]
  apply Finset.sum_congr rfl; intro k _
  rw [hterm]

/-! ## Li₂ has no zero on the circle points e^{−2i/s}

Real part: Σ cos(2πnx)/n² = π² B₂(x) on [0,1] (Mathlib `hasSum_one_div_nat_pow_mul_cos`), with
x the fractional part of 1/(πs). If it vanishes, x(1−x) = 1/6, so |sin 2πx| ≥ √3/2; the imaginary part
is −Σ sin(2πnx)/n², within π²/6 − 1 < √3/2 of −sin 2πx, hence nonzero. -/

lemma bernoulli_two_eval (x : ℝ) :
    (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2)).eval x = x ^ 2 - x + 1 / 6 := by
  simp [Polynomial.bernoulli, Finset.sum_range_succ, bernoulli_two, Polynomial.eval_monomial]
  ring

/-- On x(1−x) = 1/6 with x ≤ 1/2: sin 2πx ≥ √3/2. -/
lemma sin_ge_of_B2_zero (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) (hq : x ^ 2 - x + 1 / 6 = 0) :
    √3 / 2 ≤ Real.sin (2 * Real.pi * x) := by
  have hpi := Real.pi_pos
  have hxl : 1 / 6 ≤ x := by nlinarith
  have hxu : x ≤ 1 / 3 := by nlinarith
  rw [← Real.sin_pi_div_three]
  by_cases ht : 2 * Real.pi * x ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith) ht (by nlinarith)
  · rw [← Real.sin_pi_sub (2 * Real.pi * x)]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith) (by linarith) (by nlinarith)

lemma abs_sin_ge_of_B2_zero (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (hq : x ^ 2 - x + 1 / 6 = 0) :
    √3 / 2 ≤ |Real.sin (2 * Real.pi * x)| := by
  by_cases hx : x ≤ 1 / 2
  · exact (sin_ge_of_B2_zero x h0 hx hq).trans (le_abs_self _)
  · have h := sin_ge_of_B2_zero (1 - x) (by linarith) (by linarith) (by nlinarith)
    have : Real.sin (2 * Real.pi * x) = - Real.sin (2 * Real.pi * (1 - x)) := by
      rw [← Real.sin_two_pi_sub]; congr 1; ring
    rw [this, abs_neg]; exact h.trans (le_abs_self _)

lemma zeta_two_tail : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
  have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
  simp [Finset.sum_range_succ] at h
  convert h using 1
  funext n; ring

/-- The terms of Li₂(e^{−2i/s}) in real and imaginary parts. -/
lemma term_re_im (s : ℝ) (k : ℕ) :
    ((Complex.exp (-(2 * Complex.I / s))) ^ (k + 1) / ((k : ℂ) + 1) ^ 2).re
        = Real.cos (2 * ((k : ℝ) + 1) / s) / ((k : ℝ) + 1) ^ 2 ∧
    ((Complex.exp (-(2 * Complex.I / s))) ^ (k + 1) / ((k : ℂ) + 1) ^ 2).im
        = - (Real.sin (2 * ((k : ℝ) + 1) / s) / ((k : ℝ) + 1) ^ 2) := by
  have he : (Complex.exp (-(2 * Complex.I / s))) ^ (k + 1)
      = Complex.exp (((-(2 * ((k : ℝ) + 1) / s) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hd : ((k : ℂ) + 1) ^ 2 = ((((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [he, hd, Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
  exact ⟨rfl, by ring⟩

/-- Periodicity: with y = 1/(πs) and x its fractional part, 2n/s ≡ 2πnx mod 2π. -/
lemma angle_fract (s : ℝ) (hs : 0 < s) (n : ℝ) (hn : ∃ m : ℕ, (m : ℝ) = n) :
    (Real.cos (2 * n / s) = Real.cos (2 * Real.pi * n * Int.fract (1 / (Real.pi * s)))) ∧
    (Real.sin (2 * n / s) = Real.sin (2 * Real.pi * n * Int.fract (1 / (Real.pi * s)))) := by
  obtain ⟨m, rfl⟩ := hn
  set y := 1 / (Real.pi * s)
  have hpi := Real.pi_pos
  have hy : 2 * (m : ℝ) / s = 2 * Real.pi * m * Int.fract y + ((m * ⌊y⌋ : ℤ) : ℝ) * (2 * Real.pi) := by
    have := Int.floor_add_fract y
    have h2 : 2 * (m : ℝ) / s = 2 * Real.pi * m * y := by
      simp only [y]; field_simp
    rw [h2]; push_cast; linear_combination (-(2 * Real.pi * (m : ℝ))) * this
  rw [hy, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
  exact ⟨rfl, rfl⟩

/-- **Li₂(e^{−2i/s}) ≠ 0 for every s > 0**: each harmonic's pair amplitude (4.33) is nonzero. -/
theorem Li2_ne_zero (s : ℝ) (hs : 0 < s) : Li2 (Complex.exp (-(2 * Complex.I / s))) ≠ 0 := by
  set z := Complex.exp (-(2 * Complex.I / s)) with hz
  have hzn : ‖z‖ = 1 := by
    have := norm_pairPhase s 1; rw [pairPhase_pow, pow_one] at this; exact this
  have hsum : HasSum (fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1) ^ 2) (Li2 z) :=
    (summable_Li2_terms hzn).hasSum
  set x := Int.fract (1 / (Real.pi * s)) with hx
  have hx0 : 0 ≤ x := Int.fract_nonneg _
  have hx1 : x ≤ 1 := (Int.fract_lt_one _).le
  -- real part
  have hcos := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero (x := x) ⟨hx0, hx1⟩
  rw [bernoulli_two_eval] at hcos
  have hcos1 := (hasSum_nat_add_iff' 1).mpr hcos
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero] at hcos1
  have hre := Complex.hasSum_re hsum
  have hre' : HasSum (fun k : ℕ => (z ^ (k + 1) / ((k : ℂ) + 1) ^ 2).re)
      ((-1 : ℝ) ^ (1 + 1) * (2 * Real.pi) ^ (2 * 1) / 2 / (2 * 1).factorial * (x ^ 2 - x + 1 / 6)
        - 1 / (0 : ℝ) ^ (2 * 1) * Real.cos (2 * Real.pi * 0 * x)) := by
    convert hcos1 using 1
    funext k
    rw [hz, (term_re_im s k).1, (angle_fract s hs ((k : ℝ) + 1) ⟨k + 1, by push_cast; rfl⟩).1]
    push_cast; ring
  have hReEq := hre.unique hre'
  -- imaginary part
  set g : ℕ → ℝ := fun k => Real.sin (2 * Real.pi * ((k : ℝ) + 1) * x) / ((k : ℝ) + 1) ^ 2 with hg
  have hgs : Summable g := by
    refine Summable.of_norm_bounded summable_inv_sq_succ (fun k => ?_)
    simp only [hg, Real.norm_eq_abs, abs_div]
    rw [abs_of_pos (by positivity : (0 : ℝ) < ((k : ℝ) + 1) ^ 2), ← one_div]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
  have him := Complex.hasSum_im hsum
  have him' : HasSum (fun k : ℕ => (z ^ (k + 1) / ((k : ℂ) + 1) ^ 2).im) (-(∑' k, g k)) := by
    convert hgs.hasSum.neg using 1
    funext k
    rw [hz, (term_re_im s k).2, (angle_fract s hs ((k : ℝ) + 1) ⟨k + 1, by push_cast; rfl⟩).2]
  have hImEq := him.unique him'
  -- tail bound
  have htail : |∑' k, g k - Real.sin (2 * Real.pi * x)| ≤ Real.pi ^ 2 / 6 - 1 := by
    rw [hgs.tsum_eq_zero_add]
    have h0 : g 0 = Real.sin (2 * Real.pi * x) := by simp [hg]
    rw [h0, add_sub_cancel_left]
    have hgs1 : Summable (fun k => g (k + 1)) := (summable_nat_add_iff 1).mpr hgs
    calc |∑' k, g (k + 1)| ≤ ∑' k, |g (k + 1)| := by
          simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hgs1.norm
      _ ≤ ∑' k : ℕ, 1 / ((k : ℝ) + 2) ^ 2 := by
          refine hgs1.abs.tsum_le_tsum (fun k => ?_) zeta_two_tail.summable
          simp only [hg, abs_div, abs_pow]
          push_cast
          have : ((k : ℝ) + 1 + 1) = (k : ℝ) + 2 := by ring
          rw [this, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 2)]
          exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
      _ = Real.pi ^ 2 / 6 - 1 := zeta_two_tail.tsum_eq
  have hnum : Real.pi ^ 2 / 6 - 1 < √3 / 2 := by
    have h1 := Real.pi_lt_d2
    have h2 := Real.pi_pos
    have h3 : (1.7 : ℝ) < √3 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    nlinarith
  intro hzero
  rw [hzero, Complex.zero_re] at hReEq
  rw [hzero, Complex.zero_im] at hImEq
  have hre0 : x ^ 2 - x + 1 / 6 = 0 := by
    have hpi2 : (0 : ℝ) < Real.pi ^ 2 := by positivity
    norm_num at hReEq
    nlinarith [hReEq]
  have him0 : ∑' k, g k = 0 := by linarith
  have hsin := abs_sin_ge_of_B2_zero x hx0 hx1 hre0
  rw [him0, zero_sub, abs_neg] at htail
  linarith

/-! ## The sum over harmonics -/

/-- The pair amplitude of one harmonic, the right side of (4.33). -/
def pairAmp (s : ℝ) : ℂ := Li2 (Complex.exp (-(2 * Complex.I / s))) / (2 * (s : ℂ) ^ 2)

theorem pairAmp_ne_zero (s : ℝ) (hs : 0 < s) : pairAmp s ≠ 0 := by
  unfold pairAmp
  have : (2 * (s : ℂ) ^ 2) ≠ 0 := by
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    exact mul_ne_zero two_ne_zero (pow_ne_zero 2 this)
  exact div_ne_zero (Li2_ne_zero s hs) this

/-- The connected two-point function of the pair insertions of (4.32), summed over the radiative
harmonics I with j ≤ L and the radial modes k ≤ N: by the first equality of (4.33) over the modes (I, k),
the sum of the per-mode values 2(Δq_{I,k})⁴ e^{−2ik/s}, with the paper's (Δq_{I,k})² = 1/(2sk) in every
harmonic. -/
def harmonicCorr (s : ℝ) (L N : ℕ) : ℂ :=
  ∑ _I ∈ harmonics L, ∑ k ∈ Finset.Icc 1 N, 2 * ((variance s k) ^ 2 : ℝ) * pairPhase s k

lemma tendsto_card_harmonics : Tendsto (fun L : ℕ => ((harmonics L).card : ℝ)) atTop atTop := by
  refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop_atTop.mpr fun b => ⟨b + 1, fun a ha => ?_⟩)
  have := le_card_harmonics a
  omega

/-- **Case (iii) for target 0.** Under the paper's own definitions the pair amplitude summed over
angular harmonics diverges, for every s > 0: at each harmonic cutoff L the radial sum converges (to
L-many copies of (4.33)), each copy is the same nonzero number, and the norm grows without bound as
L → ∞. -/
theorem harmonic_sum_diverges (s : ℝ) (hs : 0 < s) :
    (∀ L : ℕ, Tendsto (fun N : ℕ => harmonicCorr s L N) atTop
        (𝓝 (((harmonics L).card : ℂ) * pairAmp s))) ∧
    pairAmp s ≠ 0 ∧
    Tendsto (fun L : ℕ => ‖((harmonics L).card : ℂ) * pairAmp s‖) atTop atTop := by
  refine ⟨fun L => ?_, pairAmp_ne_zero s hs, ?_⟩
  · have h := (radial_sum s hs).const_mul ((harmonics L).card : ℂ)
    refine h.congr (fun N => ?_)
    unfold harmonicCorr
    rw [Finset.sum_const, nsmul_eq_mul]
  · have hc : 0 < ‖pairAmp s‖ := norm_pos_iff.mpr (pairAmp_ne_zero s hs)
    have := tendsto_card_harmonics.atTop_mul_const hc
    refine this.congr (fun L => ?_)
    rw [norm_mul, Complex.norm_natCast]

/-- The squared norm of the pair state the summed insertion creates from the Gaussian state (amplitude
√2(Δq_k)² per mode, Sec. 4.4): finite in one harmonic (π²/(12s²)), unbounded over harmonics. So the
created state is not in the Hilbert space, and the paper's general bound (4.30) (absolute convergence for
normalizable states, certified in `runs/2026-11-26T1529Z/T0/sewing.lean`) does not reach it. -/
theorem pair_state_norm_diverges (s : ℝ) (hs : 0 < s) :
    (∀ L : ℕ, Tendsto
        (fun N : ℕ => ∑ _I ∈ harmonics L, ∑ k ∈ Finset.Icc 1 N, 2 * (variance s k) ^ 2) atTop
        (𝓝 (((harmonics L).card : ℝ) * (Real.pi ^ 2 / (12 * s ^ 2))))) ∧
    Tendsto (fun L : ℕ => ((harmonics L).card : ℝ) * (Real.pi ^ 2 / (12 * s ^ 2))) atTop atTop := by
  have hone : HasSum (fun k : ℕ => 2 * (variance s (k + 1)) ^ 2) (Real.pi ^ 2 / (12 * s ^ 2)) := by
    have h1 := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, div_zero, sub_zero] at h1
    have h2 := h1.mul_left (1 / (2 * s ^ 2))
    convert h2 using 1
    · funext k; unfold variance; push_cast; field_simp
    · field_simp; ring
  refine ⟨fun L => ?_, tendsto_card_harmonics.atTop_mul_const (by positivity)⟩
  have h := hone.tendsto_sum_nat.const_mul ((harmonics L).card : ℝ)
  refine h.congr (fun N => ?_)
  rw [Finset.sum_const, nsmul_eq_mul, sum_Icc_shift (fun k => 2 * (variance s k) ^ 2)]

/-- What case (i) would need: if the widths depended on the harmonic, (Δq_{I,k})² = w_I/(2sk), each
harmonic would contribute w_I² times (4.33), and the sum over harmonics would converge exactly when
Σ_I w_I² < ∞. The paper gives w_I = 1 (no dependence on I). -/
theorem weighted_sum_iff (s : ℝ) (hs : 0 < s) (w : (Σ _ : ℕ, ℤ × Fin 2) → ℝ) :
    Summable (fun I => ((w I ^ 2 : ℝ) : ℂ) * pairAmp s) ↔ Summable (fun I => w I ^ 2) := by
  rw [summable_mul_right_iff (pairAmp_ne_zero s hs)]
  exact Complex.summable_ofReal

/-- The per-harmonic radial term with width w_I: 2(w_I/(2sk))² e^{−2ik/s} = w_I² · 2(Δq_k)⁴ e^{−2ik/s}. -/
theorem weighted_term (s w : ℝ) (k : ℕ) :
    (2 * ((w * variance s k) ^ 2 : ℝ) * pairPhase s k : ℂ)
      = ((w ^ 2 : ℝ) : ℂ) * (2 * ((variance s k) ^ 2 : ℝ) * pairPhase s k) := by
  push_cast; ring

end ExternalT0.Angular

#print axioms ExternalT0.Angular.harmonic_sum_diverges
#print axioms ExternalT0.Angular.pair_state_norm_diverges
#print axioms ExternalT0.Angular.weighted_sum_iff
#print axioms ExternalT0.Angular.card_harmonics
#print axioms ExternalT0.Angular.Li2_ne_zero
