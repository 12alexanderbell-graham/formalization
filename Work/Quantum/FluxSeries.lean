import Work.Quantum.PSeries
/-!
# Power-series solutions of ((w₀ + w₁ s + w₂ s²) M′)′ + (v₀ + v₁ s + v₂ s²) M = 0 (run 2026-11-26T1628Z)

Every piece of the H₂⁺ route has this form (R = 2, k = −2ε, ε the electronic energy):
* angular at its singular end, s = 1 − η: d/ds [s(2 − s) M′] + (k(1 − s)² − A) M = 0:
  w = (0, 2, −1), v = (k − A, −2k, k);
* radial at its singular end, u = ξ − 1: d/du [u(u + 2) L′] + (4(1 + u) − k(1 + u)² + A) L = 0:
  w = (0, 2, 1), v = (4 − k + A, 4 − 2k, −k);
* radial at a regular point ξ₀, x = ξ − ξ₀: w = (ξ₀² − 1, 2ξ₀, 1), v = (4ξ₀ − kξ₀² + A, 4 − 2kξ₀, −k).
The power series ∑ bₙ sⁿ solves it when (`Rec`) 2w₀b₂ + w₁b₁ + v₀b₀ = 0, 6w₀b₃ + 4w₁b₂ + (2w₂ + v₀)b₁ + v₁b₀ = 0
and w₀(n + 3)(n + 4) bₙ₊₄ + w₁(n + 3)² bₙ₊₃ + (w₂(n + 2)(n + 3) + v₀) bₙ₊₂ + v₁ bₙ₊₁ + v₂ bₙ = 0.
`flux_hasDerivAt`: for coefficients satisfying `Rec` with |bₙ| ≤ C qⁿ, on (−r, r) with r q < 1, the series M and
its termwise derivative M₁ satisfy M′ = M₁ and ((w₀ + w₁ s + w₂ s²) M₁)′ = −(v₀ + v₁ s + v₂ s²) M.
No numerics: the certificate (`runs/2026-11-26T1628Z/scripts/h2p_emulate.py`) supplies C and q.
-/

namespace Work.Quantum.FluxSeries
open Set Filter Topology
open Work.Quantum.PSeries

/-- Shift by one place: `sh a 0 = 0`, `sh a (n + 1) = a n` (multiplication of a power series by s). -/
def sh (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => a n

theorem hasSum_sh {a : ℕ → ℝ} {x S : ℝ} (h : HasSum (fun n => a n * x ^ n) S) :
    HasSum (fun n => sh a n * x ^ n) (x * S) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, sh, pow_zero, mul_one, sub_zero]
  convert h.mul_left x using 1
  funext n
  ring

/-- The recurrence of the series (weight w₀ + w₁ s + w₂ s², potential v₀ + v₁ s + v₂ s²). -/
structure Rec (w₀ w₁ w₂ v₀ v₁ v₂ : ℝ) (b : ℕ → ℝ) : Prop where
  r0 : 2 * w₀ * b 2 + w₁ * b 1 + v₀ * b 0 = 0
  r1 : 6 * w₀ * b 3 + 4 * w₁ * b 2 + (2 * w₂ + v₀) * b 1 + v₁ * b 0 = 0
  r : ∀ n : ℕ, w₀ * ((n : ℝ) + 3) * ((n : ℝ) + 4) * b (n + 4) + w₁ * ((n : ℝ) + 3) ^ 2 * b (n + 3) +
    (w₂ * ((n : ℝ) + 2) * ((n : ℝ) + 3) + v₀) * b (n + 2) + v₁ * b (n + 1) + v₂ * b n = 0

/-- First and second termwise derivative coefficients. -/
def d1 (b : ℕ → ℝ) : ℕ → ℝ := fun n => ((n : ℝ) + 1) * b (n + 1)

theorem coeff_zero {w₀ w₁ w₂ v₀ v₁ v₂ : ℝ} {b : ℕ → ℝ} (hb : Rec w₀ w₁ w₂ v₀ v₁ v₂ b) (n : ℕ) :
    w₁ * d1 b n + 2 * w₂ * sh (d1 b) n + w₀ * d1 (d1 b) n + w₁ * sh (d1 (d1 b)) n
      + w₂ * sh (sh (d1 (d1 b))) n + v₀ * b n + v₁ * sh b n + v₂ * sh (sh b) n = 0 := by
  rcases n with _ | _ | n
  · simp only [d1, sh]; push_cast; linear_combination hb.r0
  · simp only [d1, sh]; push_cast; linear_combination hb.r1
  · simp only [d1, sh]; push_cast
    have := hb.r n
    linear_combination this

theorem flux_hasDerivAt {w₀ w₁ w₂ v₀ v₁ v₂ C q r : ℝ} {b : ℕ → ℝ} (hb : Rec w₀ w₁ w₂ v₀ v₁ v₂ b)
    (hbound : ∀ n, |b n| ≤ C * q ^ n) (hq : 0 ≤ q) (hr : 0 < r) (hrq : r * q < 1)
    {s : ℝ} (hs : s ∈ Ioo (-r) r) :
    HasDerivAt (fun y => ∑' n, b n * y ^ n) (∑' n, d1 b n * s ^ n) s ∧
    HasDerivAt (fun y => (w₀ + w₁ * y + w₂ * y ^ 2) * ∑' n, d1 b n * y ^ n)
      (-((v₀ + v₁ * s + v₂ * s ^ 2) * ∑' n, b n * s ^ n)) s := by
  obtain ⟨C₁, q₁, hq₁, hrq₁, hb₁⟩ := bound_deriv hbound hq hr hrq
  obtain ⟨C₂, q₂, hq₂, hrq₂, hb₂⟩ := bound_deriv hb₁ hq₁ hr hrq₁
  have hd0 := hasDerivAt_series hbound hq hr hrq hs
  have hd1 := hasDerivAt_series (c := d1 b) hb₁ hq₁ hr hrq₁ hs
  refine ⟨hd0, ?_⟩
  have hsa : |s| * q < 1 := by
    have : |s| ≤ r := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
    nlinarith [abs_nonneg s]
  have hsa₁ : |s| * q₁ < 1 := by
    have : |s| ≤ r := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
    nlinarith [abs_nonneg s]
  have hsa₂ : |s| * q₂ < 1 := by
    have : |s| ≤ r := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
    nlinarith [abs_nonneg s]
  have h0 := (summable_of_bound hbound hq hsa).hasSum
  have h1 := (summable_of_bound (c := d1 b) hb₁ hq₁ hsa₁).hasSum
  have h2 := (summable_of_bound (c := d1 (d1 b)) hb₂ hq₂ hsa₂).hasSum
  set M := ∑' n, b n * s ^ n
  set M₁ := ∑' n, d1 b n * s ^ n
  set M₂ := ∑' n, d1 (d1 b) n * s ^ n
  -- the product rule
  have hprod : HasDerivAt (fun y => (w₀ + w₁ * y + w₂ * y ^ 2) * ∑' n, d1 b n * y ^ n)
      ((w₁ + 2 * w₂ * s) * M₁ + (w₀ + w₁ * s + w₂ * s ^ 2) * M₂) s := by
    have hp : HasDerivAt (fun y : ℝ => w₀ + w₁ * y + w₂ * y ^ 2) (w₁ + 2 * w₂ * s) s := by
      have := (((hasDerivAt_id' s).const_mul w₁).const_add w₀).add ((hasDerivAt_pow 2 s).const_mul w₂)
      convert this using 1
      push_cast
      ring
    have h2' : HasDerivAt (fun y => ∑' n, d1 b n * y ^ n) M₂ s := by
      have := hd1
      simpa [d1, M₂] using this
    convert hp.mul h2' using 1
  -- the series identity
  have hT : HasSum (fun n => (w₁ * d1 b n + 2 * w₂ * sh (d1 b) n + w₀ * d1 (d1 b) n + w₁ * sh (d1 (d1 b)) n
      + w₂ * sh (sh (d1 (d1 b))) n + v₀ * b n + v₁ * sh b n + v₂ * sh (sh b) n) * s ^ n)
      (w₁ * M₁ + 2 * w₂ * (s * M₁) + w₀ * M₂ + w₁ * (s * M₂) + w₂ * (s * (s * M₂)) + v₀ * M + v₁ * (s * M)
        + v₂ * (s * (s * M))) := by
    have := (((((((h1.mul_left w₁).add ((hasSum_sh h1).mul_left (2 * w₂))).add (h2.mul_left w₀)).add
      ((hasSum_sh h2).mul_left w₁)).add ((hasSum_sh (hasSum_sh h2)).mul_left w₂)).add (h0.mul_left v₀)).add
      ((hasSum_sh h0).mul_left v₁)).add ((hasSum_sh (hasSum_sh h0)).mul_left v₂)
    convert this using 1
    funext n
    ring
  have hz : (w₁ * M₁ + 2 * w₂ * (s * M₁) + w₀ * M₂ + w₁ * (s * M₂) + w₂ * (s * (s * M₂)) + v₀ * M
        + v₁ * (s * M) + v₂ * (s * (s * M))) = 0 := by
    refine hT.unique ?_
    convert hasSum_zero using 1
    funext n
    rw [coeff_zero hb n, zero_mul]
  convert hprod using 1
  linear_combination -hz

end Work.Quantum.FluxSeries
