### `fit_direction` (full name `B1Fit.fit_direction`)

Hypotheses (numbered as on the generated claims page):

1. `0 ≤ Ω`
2. `Ω ≤ 1`
3. `t₅ ≤ t₃`
4. `t₃ ≤ t₁`
5. `t₁ ≤ t₀`
6. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `0 < a s`
7. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `DifferentiableAt ℝ a s`
8. `0 < hubble a t₀`
9. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)`
10. `redshift a t₀ t₁ = √2 - 1`
11. `redshift a t₀ t₃ = 2 * √2 - 1`
12. `redshift a t₀ t₅ = 4 * √2 - 1`
13. `0 < H`
14. `0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)`
15. `0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)`
16. `0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)`
17. `|5 * Real.logb 10 (lumDistFlat a t₀ t₁ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)) - c| ≤ 1 / 20`
18. `|5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c| ≤ 1 / 20`
19. `|5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) - c| ≤ 1 / 20`

Classification (generated page TRUST_MAP.md): needed 2, 3, 4, 5, 9, 10, 11, 12, 17, 18, 19; redundant (each alone, not together) 6, 7, 8; open 1, 13, 14, 15, 16

### `fs_separation_equal` (full name `FalknerSkan.SeparationEqual.fs_separation_equal`)

Hypotheses (numbered as on the generated claims page):

1. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f₁ (p₁ η) (Set.Ici 0) η`
2. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p₁ (q₁ η) (Set.Ici 0) η`
3. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q₁ (-(f₁ η * q₁ η) - β₁ * (1 - p₁ η ^ 2)) (Set.Ici 0) η`
4. `f₁ 0 = 0`
5. `p₁ 0 = 0`
6. `q₁ 0 = 0`
7. `Filter.Tendsto p₁ Filter.atTop (nhds 1)`
8. for every `η : ℝ`, if `η ∈ Set.Ioi 0`, then `0 < q₁ η`
9. for every `M : ℝ`, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p₁ η) ≤ q₁ η`
10. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f₂ (p₂ η) (Set.Ici 0) η`
11. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p₂ (q₂ η) (Set.Ici 0) η`
12. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - β₂ * (1 - p₂ η ^ 2)) (Set.Ici 0) η`
13. `f₂ 0 = 0`
14. `p₂ 0 = 0`
15. `q₂ 0 = 0`
16. `Filter.Tendsto p₂ Filter.atTop (nhds 1)`
17. for every `η : ℝ`, if `η ∈ Set.Ioi 0`, then `0 < q₂ η`
18. for every `M : ℝ`, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p₂ η) ≤ q₂ η`

Classification (generated page TRUST_MAP.md): needed 1, 2, 3, 6, 9, 10, 11, 12, 15, 18; redundant (each alone, not together) 7, 16; open 4, 5, 8, 13, 14, 17

### `fs_neg_tenth_monotone_lt` (full name `FalknerSkan.NegWindow.fs_neg_tenth_monotone_lt`)

Hypotheses (numbered as on the generated claims page):

1. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f (p η) (Set.Ici 0) η`
2. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p (q η) (Set.Ici 0) η`
3. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q (-(f η * q η) - -1 / 10 * (1 - p η ^ 2)) (Set.Ici 0) η`
4. `f 0 = 0`
5. `p 0 = 0`
6. `Filter.Tendsto p Filter.atTop (nhds 1)`
7. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `0 < q η`

Classification (generated page TRUST_MAP.md): needed 1, 2, 3, 5; redundant 6; open 4, 7

### `F12_separation` (full name `Records.F12_separation`)

Hypotheses (numbered as on the generated claims page):

1. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f (p η) (Set.Ici 0) η`
2. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p (q η) (Set.Ici 0) η`
3. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Set.Ici 0) η`
4. `f 0 = 0`
5. `p 0 = 0`
6. `q 0 = 0`
7. `Filter.Tendsto p Filter.atTop (nhds 1)`
8. for every `η : ℝ`, if `η ∈ Set.Ioi 0`, then `0 < q η`
9. for every `M : ℝ`, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`

Classification (generated page TRUST_MAP.md): needed 1, 2, 3, 6; redundant 7; open 4, 5, 8, 9
