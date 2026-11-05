import Mathlib.Data.Real.Basic

namespace Checked.Trust.SecondReading

/-- Cattoën & Visser, Class. Quantum Grav. 24, 5985 (2007), arXiv:0710.1887 (only v1 exists),
Eq. (5), p. 3: "The 'deceleration distance': d_Q = d_L/(1+z)^{3/2}."  This is the exponent p
in d_Q = d_L/(1+z)^p. -/
noncomputable def cvdQExponent : ℝ := 3 / 2

/-- Bamba, Capozziello, Nojiri, Odintsov, arXiv:1205.3421 (v1 p.117, v2 p.118, v3 p.120, identical),
Eq. (11.39), flat ΛCDM: "j₀ = 1". -/
noncomputable def bambaJLCDM : ℝ := 1

end Checked.Trust.SecondReading
