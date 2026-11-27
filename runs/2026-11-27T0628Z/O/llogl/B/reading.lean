import Mathlib

open MeasureTheory Filter Topology

namespace ReaderB

instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- 𝕋 = ℝ/(2πℤ). -/
abbrev T : Type := AddCircle (2 * Real.pi)

/-- Normalized Lebesgue measure dμ = dx/(2π) (Mathlib's `volume` on `AddCircle (2π)` has mass 2π). -/
noncomputable def μ : Measure T := ENNReal.ofReal (1 / (2 * Real.pi)) • (volume : Measure T)

/-- e^{ikx} on 𝕋. Mathlib's `fourier k x = exp(2πi k x / (2π)) = exp(i k x)`. -/
noncomputable def e (k : ℤ) (x : T) : ℂ := fourier k x

/-- \hat f(k) = ∫ f(x) e^{-ikx} dμ(x). -/
noncomputable def fhat (f : T → ℂ) (k : ℤ) : ℂ := ∫ x, f x * e (-k) x ∂μ

/-- S_N f(x) = ∑_{k=-N}^{N} \hat f(k) e^{ikx}. -/
noncomputable def S (N : ℕ) (f : T → ℂ) (x : T) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) N, fhat f k * e k x

/-- f ∈ L log L: f measurable and ∫ |f| log(2+|f|) dμ < ∞. -/
def InLLogL (f : T → ℂ) : Prop :=
  AEStronglyMeasurable f μ ∧
    ∫⁻ x, ENNReal.ofReal (‖f x‖ * Real.log (2 + ‖f x‖)) ∂μ < ⊤

theorem reading_thm_1_1 (f : T → ℂ) (hf : InLLogL f) :
    ∃ Nf : Set T, MeasurableSet Nf ∧ μ Nf = 0 ∧
      ∀ x ∈ Nfᶜ, Tendsto (fun N : ℕ => S N f x) atTop (𝓝 (f x)) := sorry

end ReaderB

/-
Ambiguities / choices
- 𝕋 := AddCircle (2π); μ := (1/(2π)) • volume, a probability measure (volume has mass 2π).
- e^{ikx} realised as Mathlib's `fourier k x`; with period 2π this is exp(i k x). Not proved here.
- f is a genuine function T → ℂ (not an a.e. class). L log L membership: AEStronglyMeasurable
  plus finite lintegral of ofReal(|f| log(2+|f|)). Integrand is nonnegative so ofReal loses nothing.
- Junk values: the Bochner integral defining f̂ is 0 for non-integrable f; but L log L ⊂ L¹ (|f| ≤ C + |f|log(2+|f|)),
  so under the hypothesis f is integrable and f̂ is the true coefficient. No integrability hypothesis added.
- Conclusion: exists measurable null set Nf with convergence off Nf, full sequence N = 0,1,2,... (N : ℕ, atTop).
  Pointwise value f x is the one of the chosen representative; modifying f on a null set changes only Nf.
- Sum over k ∈ Icc (-N) N in ℤ, symmetric.
-/
