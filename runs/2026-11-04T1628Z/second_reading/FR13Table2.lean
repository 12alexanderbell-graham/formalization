import Mathlib
namespace SecondReading.FR13
/-- Farooq & Ratra 2013 Table 1, second reading: rows (z, H, σ_H) in printed order. -/
noncomputable def fr13Table : Fin 28 → ℝ × ℝ × ℝ :=
  ![
    (0.070, 69, 19.6), -- ref 5 Zhang+2012
    (0.100, 69, 12), -- ref 1 Simon+2005
    (0.120, 68.6, 26.2), -- ref 5 Zhang+2012
    (0.170, 83, 8), -- ref 1 Simon+2005
    (0.179, 75, 4), -- ref 3 Moresco+2012
    (0.199, 75, 5), -- ref 3 Moresco+2012
    (0.200, 72.9, 29.6), -- ref 5 Zhang+2012
    (0.270, 77, 14), -- ref 1 Simon+2005
    (0.280, 88.8, 36.6), -- ref 5 Zhang+2012
    (0.350, 76.3, 5.6), -- ref 7 Chuang&Wang 2012b
    (0.352, 83, 14), -- ref 3 Moresco+2012
    (0.400, 95, 17), -- ref 1 Simon+2005
    (0.440, 82.6, 7.8), -- ref 6 Blake+2012
    (0.480, 97, 62), -- ref 2 Stern+2010
    (0.593, 104, 13), -- ref 3 Moresco+2012
    (0.600, 87.9, 6.1), -- ref 6 Blake+2012
    (0.680, 92, 8), -- ref 3 Moresco+2012
    (0.730, 97.3, 7.0), -- ref 6 Blake+2012
    (0.781, 105, 12), -- ref 3 Moresco+2012
    (0.875, 125, 17), -- ref 3 Moresco+2012
    (0.880, 90, 40), -- ref 2 Stern+2010
    (0.900, 117, 23), -- ref 1 Simon+2005
    (1.037, 154, 20), -- ref 3 Moresco+2012
    (1.300, 168, 17), -- ref 1 Simon+2005
    (1.430, 177, 18), -- ref 1 Simon+2005
    (1.530, 140, 14), -- ref 1 Simon+2005
    (1.750, 202, 40), -- ref 1 Simon+2005
    (2.300, 224, 8) -- ref 4 Busca+2012
  ]
end SecondReading.FR13
