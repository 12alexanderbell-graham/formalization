import Mathlib

open Filter Topology

namespace Blind

/-- Hubble rate H ≡ (1/a) da/dt (Eq. 3). -/
noncomputable def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- Redshift: 1 + z = a0 / a(t), with a0 = a(t0) (source text after Eq. 15). -/
noncomputable def redshift (a : ℝ → ℝ) (t0 t : ℝ) : ℝ := a t0 / a t - 1

/-- Generic cosmographic ratio (1/(a Hⁿ)) dⁿa/dtⁿ, evaluated at time t. -/
noncomputable def cosmo (n : ℕ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  iteratedDeriv n a t / (a t * hubble a t ^ n)

/-- Eq. (3), subscript 0 = evaluated at t = t0. Note the minus sign on q only. -/
noncomputable def q0 (a : ℝ → ℝ) (t0 : ℝ) : ℝ := -cosmo 2 a t0
noncomputable def j0 (a : ℝ → ℝ) (t0 : ℝ) : ℝ := cosmo 3 a t0
noncomputable def s0 (a : ℝ → ℝ) (t0 : ℝ) : ℝ := cosmo 4 a t0
noncomputable def l0 (a : ℝ → ℝ) (t0 : ℝ) : ℝ := cosmo 5 a t0
noncomputable def m0 (a : ℝ → ℝ) (t0 : ℝ) : ℝ := cosmo 6 a t0

/-- Flat ΛCDM as stated before Eq. (15): H = H0 √(Ωm (1+z)³ + 1 − Ωm). -/
structure FlatLCDM (a : ℝ → ℝ) (t0 H0 Ωm : ℝ) : Prop where
  /-- Eqs. (1)-(2) Taylor-expand a to 6th order, so a must be (at least) C⁶. -/
  smooth : ContDiff ℝ 6 a
  /-- Scale factor is positive (needed for 1/a, 1+z); only near t0 matters. -/
  pos : ∀ᶠ t in 𝓝 t0, 0 < a t
  /-- "a0 = 1 without loss of generality" (Eq. 1-2); results do not depend on it. -/
  norm : a t0 = 1
  /-- Expanding universe, H0 > 0 (H0 is the present Hubble rate; sign needed for √). -/
  H0_pos : 0 < H0
  /-- The model equation must hold on a neighbourhood of t0: derivatives at t0
      are only determined by the equation on an open set around t0. -/
  friedmann : ∀ᶠ t in 𝓝 t0, hubble a t = H0 * √(Ωm * (1 + redshift a t0 t) ^ 3 + 1 - Ωm)

/-- Eq. (15) for l0, exactly as printed. Ωm restricted to the physical range [0,1]
    (the identities themselves do not need it). -/
def PrintedL0 : Prop :=
  ∀ (a : ℝ → ℝ) (t0 H0 Ωm : ℝ), 0 ≤ Ωm → Ωm ≤ 1 → FlatLCDM a t0 H0 Ωm →
    l0 a t0 = 1 + 3 * Ωm - 27 / 2 * Ωm ^ 2

/-- Eq. (15) for m0, exactly as printed (note: two Ωm² terms, 81/2 on Ωm³). -/
def PrintedM0 : Prop :=
  ∀ (a : ℝ → ℝ) (t0 H0 Ωm : ℝ), 0 ≤ Ωm → Ωm ≤ 1 → FlatLCDM a t0 H0 Ωm →
    m0 a t0 = 1 - 27 / 2 * Ωm ^ 2 - 81 * Ωm ^ 2 - 81 / 2 * Ωm ^ 3

/-- True value (sympy): l0 = 1 + 3Ωm + (27/2)Ωm²  (printed has the wrong sign on Ωm²). -/
theorem lcdm_l0 (a : ℝ → ℝ) (t0 H0 Ωm : ℝ) (h0 : 0 ≤ Ωm) (h1 : Ωm ≤ 1)
    (h : FlatLCDM a t0 H0 Ωm) :
    l0 a t0 = 1 + 3 * Ωm + 27 / 2 * Ωm ^ 2 := by
  sorry

/-- True value (sympy): m0 = 1 − (27/2)Ωm − 81Ωm² − (81/4)Ωm³
    (printed has Ωm² for Ωm in the 2nd term and 81/2 for 81/4). -/
theorem lcdm_m0 (a : ℝ → ℝ) (t0 H0 Ωm : ℝ) (h0 : 0 ≤ Ωm) (h1 : Ωm ≤ 1)
    (h : FlatLCDM a t0 H0 Ωm) :
    m0 a t0 = 1 - 27 / 2 * Ωm - 81 * Ωm ^ 2 - 81 / 4 * Ωm ^ 3 := by
  sorry

end Blind
