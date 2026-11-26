import Mathlib

open Complex Filter Topology Finset
open scoped BigOperators Matrix

noncomputable section

namespace T0

/-- "we choose the Gaussian wavefunction (4.7) with q_k^0 = p_k^0 = 0, and write
s = 𝒜/(4 G_N ħ)."  `area` is the corner area 𝒜. -/
def sOf (area GN hbar : ℝ) : ℝ := area / (4 * GN * hbar)

/-- "(Δq_k)^2 = 1/(2sk)"  (4.32). The variance as a function of s and the mode number k. -/
def variance (s : ℝ) (k : ℕ) : ℝ := 1 / (2 * s * k)

/-- "A Fourier mode proportional to exp(−ikω₁u), ... acquires the phase exp(−ik/s) when we
advance the affine parameter u by 1/(sω₁)": the phase of one graviton in mode k. -/
def phase (s : ℝ) (k : ℕ) : ℂ := Complex.exp (-(Complex.I * k / s))

/-- "yielding the pair phase e^{−2ik/s}" (Figure 20) / "the two phases multiply, yielding
exp(−2ik/s)" (4.33 text). -/
def pairPhase (s : ℝ) (k : ℕ) : ℂ := Complex.exp (-(2 * Complex.I * k / s))

/-- Dilogarithm for |z| ≤ 1, as instructed: Li₂(z) = Σ_{k≥1} z^k / k². -/
def Li2 (z : ℂ) : ℂ := ∑' k : ℕ, z ^ (k + 1) / ((k : ℂ) + 1) ^ 2

/-- (4.7), one factor: ⟨q|Ω_j⟩ = [2π(Δq)²]^{-1/4} exp[ −(q−q⁰)²/(4(Δq)²) + (i/ħ) p⁰ (q−q⁰) ].
Here `v` is (Δq)². (Not used in the matrix model below, which is built from the
occupation-number basis; included for the record.) -/
def gaussian (v q0 p0 hbar : ℝ) (q : ℝ) : ℂ :=
  ((2 * Real.pi * v) ^ (-(1 / 4 : ℝ)) : ℝ) *
    Complex.exp (-(((q - q0) ^ 2 / (4 * v) : ℝ) : ℂ) + Complex.I * ((p0 / hbar * (q - q0) : ℝ) : ℂ))

/-! ### One-mode model: first 6 occupation-number states |0>,...,|5>, coefficient vectors. -/

abbrev Fock := Fin 6

/-- Annihilation operator 𝔞|n⟩ = √n |n−1⟩ ("[𝔞_j,𝔞_k†]=δ_jk", 𝔞|Ω⟩=0), on coefficient vectors. -/
def ann : Matrix Fock Fock ℂ :=
  Matrix.of fun i j => if (i : ℕ) + 1 = (j : ℕ) then ((Real.sqrt (j : ℕ) : ℝ) : ℂ) else 0

/-- Creation operator 𝔞† = conjugate transpose of `ann`. -/
def cre : Matrix Fock Fock ℂ := ann.conjTranspose

/-- Number operator 𝔞†𝔞 (diagonal n). -/
def num : Matrix Fock Fock ℂ := cre * ann

/-- "q̂_k": from (4.9), with centre q⁰ = 0, p⁰ = 0:
𝔞 = q̂/(2Δq) + iΔq p̂/ħ, 𝔞† = q̂/(2Δq) − iΔq p̂/ħ, hence q̂ = Δq (𝔞 + 𝔞†). `σ` is Δq_k. -/
def qop (σ : ℝ) : Matrix Fock Fock ℂ := (σ : ℂ) • (ann + cre)

/-- The boundary unitary exp[ i θ 𝔞†𝔞 ] (diagonal), θ real. -/
def rot (θ : ℝ) : Matrix Fock Fock ℂ :=
  Matrix.diagonal fun n => Complex.exp (Complex.I * θ * ((n : ℕ) : ℂ))

/-- The vacuum |Ω⟩ = |0⟩ of the mode. -/
def vac : Fock → ℂ := Pi.single 0 1

/-- Expectation value ⟨Ω|M|Ω⟩. -/
def expect (M : Matrix Fock Fock ℂ) : ℂ := star vac ⬝ᵥ (M *ᵥ vac)

/-- Connected expectation ⟨A B⟩_c = ⟨AB⟩ − ⟨A⟩⟨B⟩ for a single mode. -/
def conn1 (A B : Matrix Fock Fock ℂ) : ℂ := expect (A * B) - expect A * expect B

/-- Two-mode space (|n_j⟩ ⊗ |n_k⟩), for j ≠ k. -/
abbrev Fock2 := Fock × Fock

def vac2 : Fock2 → ℂ := Pi.single (0, 0) 1

def expect2 (M : Matrix Fock2 Fock2 ℂ) : ℂ := star vac2 ⬝ᵥ (M *ᵥ vac2)

def conn2 (A B : Matrix Fock2 Fock2 ℂ) : ℂ := expect2 (A * B) - expect2 A * expect2 B

/-- Operator on mode j (first tensor factor) of the two-mode space. -/
def onFirst (M : Matrix Fock Fock ℂ) : Matrix Fock2 Fock2 ℂ :=
  Matrix.kroneckerMap (· * ·) M (1 : Matrix Fock Fock ℂ)

/-- Operator on mode k (second tensor factor) of the two-mode space. -/
def onSecond (M : Matrix Fock Fock ℂ) : Matrix Fock2 Fock2 ℂ :=
  Matrix.kroneckerMap (· * ·) (1 : Matrix Fock Fock ℂ) M

/-- The connected correlator of (4.33) for modes j,k as the paper evaluates it (Figure 21):
"Each line carries δ_jk (Δq_k)² e^{−ik/s}, so the two connected Wick contractions have
equal weight":  = 2 δ_jk (Δq_k)⁴ e^{−2ik/s}. -/
def connValue (s : ℝ) (j k : ℕ) : ℂ :=
  if j = k then 2 * ((variance s k) ^ 2 : ℝ) * pairPhase s k else 0

/-- "⟨(e^{ij𝔞†𝔞/s} q̂_j² e^{−ij𝔞†𝔞/s}) q̂_k² ⟩_c" with q⁰=p⁰=0, Gaussian |Ω⟩ and
(Δq_k)² = 1/(2sk): the j = k case is computed on one mode, the j ≠ k case on a product of
two modes (mode j carries the rotation and q̂_j², mode k carries q̂_k²).
For j=k (the rotation uses j = k in the exponent): value 2(Δq_k)⁴ e^{−2ik/s};
for j≠k: 0. -/
theorem single_mode (s : ℝ) (hs : 0 < s) :
    (∀ k : ℕ, 1 ≤ k →
      conn1 (rot ((k : ℝ) / s) * qop (Real.sqrt (variance s k)) * qop (Real.sqrt (variance s k)) *
              (rot ((k : ℝ) / s)).conjTranspose)
            (qop (Real.sqrt (variance s k)) * qop (Real.sqrt (variance s k)))
        = 2 * ((variance s k) ^ 2 : ℝ) * pairPhase s k) ∧
    (∀ j k : ℕ, 1 ≤ j → 1 ≤ k → j ≠ k →
      conn2 (onFirst (rot ((j : ℝ) / s) * qop (Real.sqrt (variance s j)) * qop (Real.sqrt (variance s j)) *
              (rot ((j : ℝ) / s)).conjTranspose))
            (onSecond (qop (Real.sqrt (variance s k)) * qop (Real.sqrt (variance s k)))) = 0) := by
  sorry

/-- (4.33): "lim_{N→∞} Σ_{j,k=1}^N ⟨…⟩_c = lim_{N→∞} 2 Σ_{k=1}^N (Δq_k)⁴ e^{−2ik/s}
= Li₂(e^{−2i/s}) / (2 s²).  This sum converges absolutely for every s > 0."
Both the double sum of the connected values and the diagonal sum are given. -/
theorem eq_4_33 (s : ℝ) (hs : 0 < s) :
    Summable (fun k : ℕ => ‖2 * ((variance s (k + 1)) ^ 2 : ℝ) * pairPhase s (k + 1)‖) ∧
    (∀ N : ℕ, ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, connValue s j k
        = ∑ k ∈ Finset.Icc 1 N, 2 * ((variance s k) ^ 2 : ℝ) * pairPhase s k) ∧
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, 2 * ((variance s k) ^ 2 : ℝ) * pairPhase s k)
      atTop (𝓝 (Li2 (Complex.exp (-(2 * Complex.I / s))) / (2 * (s : ℂ) ^ 2))) := by
  sorry

/-- (4.34): "(G_N³/3!) ∂³/∂G_N³ [ Σ_{k=1}^N (1/(2s²)) e^{−ik/s}... e^{−2ik/s}/k² ]|_{G_N=0}
= −(i/s³) Σ_{k=1}^N 1/k".  With s = 𝒜/(4 G_N ħ), i.e. 1/s = c G with c = 4ħ/𝒜, the summand is
(c² G²/2)·e^{−2ikcG}/k² (the 1/(2 s² k²) = 2 (Δq_k)⁴ of (4.33)).
Exact finite-N identity: (1/3!) ∂³_G f_N (0) = −i c³ H_N, i.e. after multiplying by G³ (G>0, s = 1/(cG))
it equals −i/s³ · H_N. -/
theorem eq_4_34 (area hbar : ℝ) (hA : 0 < area) (hh : 0 < hbar) (N : ℕ) :
    let c : ℝ := 4 * hbar / area
    let f : ℝ → ℂ := fun G =>
      ∑ k ∈ Finset.Icc 1 N, (((c ^ 2 * G ^ 2 / 2 : ℝ) : ℂ) / ((k : ℂ) ^ 2)) *
        Complex.exp (-(2 * Complex.I * k * (c * G : ℝ)))
    iteratedDeriv 3 f 0 / 6 = -(Complex.I * (c : ℂ) ^ 3) * ∑ k ∈ Finset.Icc 1 N, (1 : ℂ) / k ∧
    (∀ G : ℝ, 0 < G →
      (G : ℂ) ^ 3 * (iteratedDeriv 3 f 0 / 6)
        = -(Complex.I / ((sOf area G hbar : ℝ) : ℂ) ^ 3) * ∑ k ∈ Finset.Icc 1 N, (1 : ℂ) / k) := by
  sorry

/-- "= −(i/s³)[log N + O(1)]": the harmonic numbers are log N + O(1). -/
theorem harmonic_log :
    (fun N : ℕ => (∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / k) - Real.log N) =O[atTop] (fun _ => (1 : ℝ)) := by
  sorry

/-- "Summing before expanding converts the log N divergence in (4.34) into the finite term
−i log s / s³ in (4.33)."  Stated as: as s → ∞ (G_N → 0 at fixed area) the imaginary part of
the right side of (4.33), R(s) = Li₂(e^{−2i/s})/(2s²), satisfies Im R(s) = −log s / s³ + O(1/s³),
and so Im R(s) / (−log s / s³) → 1. -/
theorem finite_term :
    let R : ℝ → ℂ := fun s => Li2 (Complex.exp (-(2 * Complex.I / s))) / (2 * (s : ℂ) ^ 2)
    ((fun s : ℝ => (R s).im + Real.log s / s ^ 3) =O[atTop] (fun s : ℝ => 1 / s ^ 3)) ∧
    Tendsto (fun s : ℝ => (R s).im / (-(Real.log s) / s ^ 3)) atTop (𝓝 1) := by
  sorry

end T0

/-
(i) AMBIGUITIES AND CHOICES

* The mode sum in (4.33): the first operator is written e^{ij 𝔞†𝔞/s} q̂_j² e^{−ij 𝔞†𝔞/s} with a bare
  "𝔞†𝔞"; I read it as the number operator of mode j (same mode as q̂_j), rotation phase j/s.
  For j = k this gives e^{−2ik/s}, matching the text "yielding exp(−2ik/s)". Sign convention
  e^{iθn} 𝔞 e^{−iθn} = e^{−iθ} 𝔞 fixes the −2ik/s.
* "Connected" ⟨AB⟩_c = ⟨AB⟩ − ⟨A⟩⟨B⟩ (Gaussian vacuum, centres 0). The text also says "after subtracting
  its Gaussian expectation value, the quadratic insertion..." -- same thing here since ⟨q̂²⟩ is subtracted.
* The Gaussian centres and widths: q_k^0 = p_k^0 = 0 for all k (text, p.33), widths (Δq_k)² = 1/(2sk)
  (4.32), so q̂ = Δq(𝔞+𝔞†) from (4.9). I did NOT derive 𝔞 from the differential form of p̂; the Fock
  matrices (truncated at 6 levels, ample since only levels ≤ 2 enter) are taken as the definition,
  with ħ-dependence absorbed (q̂ is dimensionless: "dimensionless canonical coordinates q_k").
* Mode index range: k starts at 1; the paper writes j,k = 1..N.
* Li₂ series definition per the brief; for z = e^{−2i/s} |z| = 1 so it is the boundary of convergence
  (converges absolutely since Σ1/k² < ∞).
* (4.34): the left side is written with G_N³ times ∂³ at G_N = 0 while s depends on G_N; it is only
  an identity as a coefficient statement: coefficient of G³ in the expansion of
  Σ e^{−2ik/s}/(2s²k²) with 1/s = cG. I also give the version "G³ · coefficient = −i H_N/s³" at s = 1/(cG).
  The "−ik/s" linear term expansion and factor 2 (Figure 22) are consistent with this.
  Real G differentiation of a ℂ-valued function (iteratedDeriv over ℝ).
* "finite term −i log s/s³" is only the leading term as s→∞; the exact imaginary part of the RHS also
  has O(1/s³) corrections (e.g. −(1 − log 2)/s³). I state it as Im R = −log s/s³ + O(1/s³).
  The paper does not say "s → ∞" explicitly; I read "as G_N → 0" with fixed 𝒜 as s → ∞.
  The real part of R(s) (≈ ζ(2)/(2s²)) is not discussed by the paper.
* The sign/identification of log N in "−i/s³[log N + O(1)]" is for fixed s as N→∞ (harmonic numbers).

(ii) ASSUMPTIONS BEHIND "FINITE"

1. Fixed corner area 𝒜 ("At fixed corner area 𝒜, we select one polarization..."; "At fixed 𝒜 each variance 1/(2sk) is of order G_N"), so s = 𝒜/(4G_Nħ) with s>0.
2. One graviton polarization and one real-valued angular harmonic ("we select one polarization and one real valued angular harmonic").
3. Radial modes k=1,2,... of the profile along null generators (Appendix D.3); mode number k labels wavelength.
4. The Gaussian state (4.7) with centres q_k^0 = p_k^0 = 0 and widths (Δq_k)² = 1/(2sk) ("we choose the Gaussian wavefunction (4.7) with q_k^0 = p_k^0 = 0").
5. The chosen relative phase exp(−ik/s) per mode, i.e. affine shift 1/(sω₁) ("We choose this relative phase for radial mode k at the second insertion by rotating the modes with a boundary unitary" (4.32)).
6. The particular observable: a connected two-point function of two quadratic insertions q̂² ("the quadratic insertion creates a pair in mode k with amplitude √2(Δq_k)²"), with annihilation phase chosen to cancel creation ("By choosing the phase with which the second insertion annihilates the pair").
7. Cutoff N on the mode number (sum Σ_{k=1}^N), with the limit N→∞ taken at fixed G_N (fixed s) ("The sum ... at finite G_N"; "Removing the cutoff at fixed G_N"); order of limits: sum first (N→∞ at fixed s>0), then s→∞ i.e. G_N→0 ("Summing before expanding"); expanding in G_N before summing gives the log N divergence in (4.34).
8. G_N > 0 ("finite amplitude at every positive G_N"); the finiteness is not uniform in G_N: "its third derivative diverges as G_N→0⁺".
9. Absolute convergence of Σ 1/k² for every s>0 (footnote 17 / sentence "This sum converges absolutely for every s > 0").
-/
