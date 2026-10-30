import Mathlib

/-!
Independent second transcription of Bamba–Capozziello–Nojiri–Odintsov (2012),
arXiv:1205.3421v3, Section XI, Eqs. (11.25)–(11.31), (11.39), (11.42)–(11.43).
Read from the typeset PDF (v3 pp. 116, 120, 121; visually identical in v1/v2).
Variables: q j s l stand for q₀ j₀ s₀ l₀; Ω stands for Ω_M^(0).
Printed grouping is kept literally.
-/

namespace Checked.Trust.SecondReading

/-- Eq. (11.25), 𝒫₀. -/
def P0 (q j s l : ℝ) : ℝ :=
  (j - q - 2) * l - (3 * s + 7 * j + 6 * q ^ 2 + 41 * q + 22) * s
    - ((3 * q + 16) * j + 20 * q ^ 2 + 64 * q + 12) * j
    - (3 * q ^ 4 + 25 * q ^ 3 + 96 * q ^ 2 + 72 * q + 20)

/-- Eq. (11.26), 𝒬₀. -/
def Q0 (q j s l : ℝ) : ℝ :=
  (q ^ 2 - j * q + 2 * q) * l
    + (3 * q * s + (4 * q + 6) * j + 6 * q ^ 3 + 44 * q ^ 2 + 22 * q - 12) * s
    + (2 * j ^ 2 + (3 * q ^ 2 + 10 * q - 6) * j + 17 * q ^ 3 + 52 * q ^ 2 + 54 * q + 36) * j
    + 3 * q ^ 5 + 28 * q ^ 4 + 118 * q ^ 3 + 72 * q ^ 2 - 76 * q - 64

/-- Eq. (11.27), 𝒫₂. -/
def P2 (q j s : ℝ) : ℝ :=
  9 * s + 6 * j + 9 * q ^ 2 + 66 * q + 42

/-- Eq. (11.28), 𝒬₂. -/
def Q2 (q j s : ℝ) : ℝ :=
  -(6 * (q + 1) * s + (2 * j - 2 * (1 - q)) * j + 6 * q ^ 3 + 50 * q ^ 2 + 74 * q + 32)

/-- Eq. (11.29), 𝒫₃. -/
def P3 (q j s l : ℝ) : ℝ :=
  3 * l + 3 * s - 9 * (q + 4) * j - (45 * q ^ 2 + 78 * q + 12)

/-- Eq. (11.30), 𝒬₃. -/
def Q3 (q j s l : ℝ) : ℝ :=
  -(2 * (1 + q) * l + 2 * (j + q) * s - (2 * j + 4 * q ^ 2 + 12 * q + 6) * j
      - (30 * q ^ 3 + 84 * q ^ 2 + 78 * q + 24))

/-- Eq. (11.31), ℛ (printed; note no q₀² term in the last parenthesis). -/
def printedR (q j s l : ℝ) : ℝ :=
  (j - q - 2) * l - (3 * s - 2 * j + 6 * q ^ 2 + 50 * q + 40) * s
    + ((3 * q + 10) * j + 11 * q ^ 2 + 4 * q + 18) * j
    - (3 * q ^ 4 + 34 * q ^ 3 + 246 * q + 104)

/-- Eq. (11.39), q₀ in ΛCDM. -/
noncomputable def qL (Ω : ℝ) : ℝ := 1 / 2 - 3 / 2 * (1 - Ω)

/-- Eq. (11.39), s₀ in ΛCDM. -/
noncomputable def sL (Ω : ℝ) : ℝ := 1 - 9 / 2 * Ω

/-- Eq. (11.39), l₀ in ΛCDM. -/
noncomputable def lL (Ω : ℝ) : ℝ := 1 + 3 * Ω + 27 / 2 * Ω ^ 2

/-- Eqs. (11.42)–(11.43), common printed denominator. -/
def printedDen (Ω : ℝ) : ℝ :=
  (3 * (9 * Ω + 74) * Ω - 556) * Ω ^ 2 + 16

/-- Eq. (11.42): η₂₀ = [64 − 6Ω(9Ω+8)] / printedDen × ε/27; this is the ε-coefficient. -/
noncomputable def printed20 (Ω : ℝ) : ℝ :=
  (64 - 6 * Ω * (9 * Ω + 8)) / printedDen Ω * (1 / 27)

/-- Eq. (11.43): η₃₀ = {6[(81Ω−110)Ω+40]Ω + 16} / printedDen × ε/(243 Ω²). -/
noncomputable def printed30 (Ω : ℝ) : ℝ :=
  (6 * ((81 * Ω - 110) * Ω + 40) * Ω + 16) / printedDen Ω * (1 / (243 * Ω ^ 2))

end Checked.Trust.SecondReading
