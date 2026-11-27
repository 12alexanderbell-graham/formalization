import Mathlib

/-!
Blind reading A of O64, "Brennan's conjecture and sharp inverse-square integral means":
Theorem 1.1 (all four assertions) and Corollary 1.2 (the Koebe function).
-/

namespace ReaderA

open Complex MeasureTheory Filter Topology
open scoped ENNReal

/-- The open unit disk `𝔻 = {z : |z| < 1}`. -/
def UnitDisk : Set ℂ := Metric.ball 0 1

/-- A univalent map on `𝔻`: holomorphic and injective on `𝔻`. Maps `𝔻 → ℂ` are represented by
functions `ℂ → ℂ`; values off `𝔻` play no role in anything below. -/
def UnivalentOnDisk (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f UnitDisk ∧ Set.InjOn f UnitDisk

/-- The normalized schlicht class `𝒮 = {f : 𝔻 → ℂ univalent : f(0) = 0, f'(0) = 1}`. -/
def Schlicht : Set (ℂ → ℂ) :=
  {f | UnivalentOnDisk f ∧ f 0 = 0 ∧ deriv f 0 = 1}

/-- `M_t[f'](r) = (1/2π) ∫_{-π}^{π} |f'(r e^{iθ})|^t dθ`. -/
noncomputable def Mt (t : ℝ) (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  1 / (2 * Real.pi) *
    ∫ θ in (-Real.pi)..Real.pi, ‖deriv f ((r : ℂ) * exp ((θ : ℂ) * I))‖ ^ t

/-- `β_f(t) = limsup_{r ↑ 1} log M_t[f'](r) / log(1/(1-r))`, as an extended real
(the limsup is taken in `EReal`, so it is never a junk value). -/
noncomputable def betaF (f : ℂ → ℂ) (t : ℝ) : EReal :=
  limsup (fun r : ℝ => ((Real.log (Mt t f r) / Real.log (1 / (1 - r)) : ℝ) : EReal)) (𝓝[<] 1)

/-- `B_𝒮(t) = sup_{f ∈ 𝒮} β_f(t)` (in `EReal`). -/
noncomputable def BS (t : ℝ) : EReal :=
  ⨆ f ∈ Schlicht, betaF f t

/-- The Koebe function `z / (1 - z)^2`. -/
noncomputable def koebe (z : ℂ) : ℂ := z / (1 - z) ^ 2

/-- Theorem 1.1, assertion 1: uniform inverse-square integral means bound. -/
theorem reading_thm_1_1_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, ∀ f ∈ Schlicht, ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
      Mt (-2) f r ≤ Cε * (1 - r) ^ (-1 - ε) := sorry

/-- Theorem 1.1, assertion 2: `B_𝒮(-2) = 1`. -/
theorem reading_thm_1_1_BS : BS (-2) = 1 := sorry

/-- Theorem 1.1, assertion 3 (domain form, Brennan's conjecture). -/
theorem reading_thm_1_1_domain
    (W : Set ℂ) (hWo : IsOpen W) (hWc : IsConnected W) (hWsc : SimplyConnectedSpace W)
    (hbdry : (frontier (((↑) : ℂ → OnePoint ℂ) '' W)).Nontrivial)
    (φ : ℂ → ℂ) (hφ : DifferentiableOn ℂ φ W) (hbij : Set.BijOn φ W UnitDisk)
    (s : ℝ) (hs1 : 4 / 3 < s) (hs2 : s < 4) :
    ∫⁻ z in W, (‖deriv φ z‖₊ : ℝ≥0∞) ^ s < ∞ := sorry

/-- Theorem 1.1, assertion 4 (disk form). -/
theorem reading_thm_1_1_disk
    (f : ℂ → ℂ) (hf : UnivalentOnDisk f) (t : ℝ) (ht1 : -2 < t) (ht2 : t < 2 / 3) :
    ∫⁻ w in UnitDisk, (‖deriv f w‖₊ : ℝ≥0∞) ^ t < ∞ := sorry

/-- Corollary 1.2: the Koebe function is in `𝒮` and both endpoint area integrals diverge. -/
theorem reading_cor_1_2_koebe :
    koebe ∈ Schlicht ∧
      ∫⁻ w in UnitDisk, (‖deriv koebe w‖₊ : ℝ≥0∞) ^ (-2 : ℝ) = ∞ ∧
      ∫⁻ w in UnitDisk, (‖deriv koebe w‖₊ : ℝ≥0∞) ^ (2 / 3 : ℝ) = ∞ := sorry

/-- Corollary 1.2, last sentence: the inverse `φ = koebe⁻¹ : koebe(𝔻) → 𝔻` fails area
integrability at `s = 4` and at `s = 4/3`. -/
theorem reading_cor_1_2_inverse
    (φ : ℂ → ℂ) (hφ : ∀ z ∈ UnitDisk, φ (koebe z) = z) :
    ∫⁻ z in koebe '' UnitDisk, (‖deriv φ z‖₊ : ℝ≥0∞) ^ (4 : ℝ) = ∞ ∧
      ∫⁻ z in koebe '' UnitDisk, (‖deriv φ z‖₊ : ℝ≥0∞) ^ (4 / 3 : ℝ) = ∞ := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES

1. Maps on 𝔻 are functions `ℂ → ℂ`; "univalent" = `DifferentiableOn ℂ f 𝔻 ∧ InjOn f 𝔻`.
   `f'(0)` is `deriv f 0`, legitimate because f is differentiable on the open disk (no junk).
   The supremum over 𝒮 ranges over functions `ℂ → ℂ`, so many representatives of one map on 𝔻
   occur; β_f depends only on values on 𝔻 (r < 1), so this does not change B_𝒮.

2. M_t[f'](r): `1/(2π) ∫_{-π}^{π} ‖f'(r e^{iθ})‖^t dθ` with `Real.rpow`. For univalent f,
   f' has no zeros in 𝔻, so the base is positive (no `0^t` junk for t < 0), and the integrand
   is continuous on the circle, hence integrable (the interval integral is not the junk 0).
   For f ∈ 𝒮 and 0 < r < 1, M_t > 0, so `Real.log` is applied to a positive number.

3. β_f(t): limsup along `𝓝[<] 1` (r ↑ 1) of `log M_t / log(1/(1-r))`, computed in `EReal`
   to avoid the junk value of a real `limsup` of an unbounded function. Near r = 1 from
   below, 1/(1-r) > 1, so `log(1/(1-r)) > 0` and the division is not by 0. B_𝒮(t) is an
   `iSup` in `EReal` (complete lattice, no junk); `B_𝒮(-2) = 1` is an equality in `EReal`,
   which also asserts finiteness. The "equivalently ... infimum of b" characterization is
   not formalized separately (it is a remark).

4. Uniform bound: `∃ Cε : ℝ` (finite), for all f ∈ 𝒮 and 1/2 ≤ r < 1,
   `M_{-2}[f'](r) ≤ Cε (1-r)^{-1-ε}` with `Real.rpow` of the positive base `1 - r`.

5. Domain form: W ⊆ ℂ a domain = open and connected (`IsConnected` includes nonempty);
   simply connected = Mathlib `SimplyConnectedSpace W` on the subtype. "Boundary in the
   Riemann sphere contains at least two points": the Riemann sphere is `OnePoint ℂ`; the
   boundary is `frontier` of the image of W in `OnePoint ℂ`, required `Nontrivial` (≥ 2
   points). "Conformal bijection φ : W → 𝔻": φ holomorphic on W and `BijOn φ W 𝔻`
   (holomorphic + injective = conformal). `φ'` is `deriv φ`, legitimate on the open set W.

6. Area integrals "< ∞": lower Lebesgue integrals `∫⁻` of `‖·‖₊ ^ s` in `ℝ≥0∞` against Mathlib's
   `volume` on ℂ, which is planar Lebesgue measure dx dy. This avoids the Bochner-integral
   junk value for non-integrable functions, and "= ∞" in Cor 1.2 is literal. `ENNReal.rpow`
   of 0 with negative exponent is ⊤, but derivatives of univalent maps never vanish on 𝔻,
   so this case does not arise on the sets of integration.

7. Disk form: every univalent f (not necessarily normalized), -2 < t < 2/3. The text's
   "Equivalently" links assertions 3 and 4; both are stated as separate theorems.

8. Koebe function `z/(1-z)^2` as a function ℂ → ℂ (at z = 1, Lean's x/0 = 0, but z = 1 is
   outside 𝔻, so irrelevant). Corollary 1.2's displayed claim: `koebe ∈ 𝒮` and both area
   integrals over 𝔻 equal ∞. The final sentence (failure for the inverse at s = 4 and 4/3)
   is stated separately: for any φ with φ ∘ koebe = id on 𝔻, the integrals of
   `|φ'|^4` and `|φ'|^{4/3}` over koebe(𝔻) are ∞. φ is then the inverse on the open set
   koebe(𝔻), hence holomorphic there, so `deriv φ` is not junk.
-/
