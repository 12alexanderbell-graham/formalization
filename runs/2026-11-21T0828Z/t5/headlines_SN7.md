### `rl19_box_unmatched` (full name `B1FitRL19.rl19_box_unmatched`)

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
13. `343 / 100 ≤ a₂`
14. `a₂ ≤ 349 / 100`
15. `157 / 100 ≤ a₃`
16. `a₃ ≤ 169 / 100`
17. `0 < H`
18. `0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)`
19. `0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)`
20. `0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)`

Classification (generated page TRUST_MAP.md): needed 3, 4, 5, 11, 12; redundant (each alone, not together) 6, 7, 8, 17, 18, 19, 20; open 1, 2, 9, 10, 13, 14, 15, 16

### `l19_sq_curved` (full name `B1L19Curved.l19_sq_curved`)

Hypotheses (numbered as on the generated claims page):

1. `1 / 10 ≤ Ω`
2. `Ω ≤ 1`
3. `t₅ ≤ t₃`
4. `t₃ ≤ t₀`
5. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `0 < a s`
6. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `DifferentiableAt ℝ a s`
7. `0 < hubble a t₀`
8. `1 ≤ omega0 K a t₀`
9. `omega0 K a t₀ ≤ 11 / 10`
10. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + (1 - omega0 K a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 K a t₀ - Ω)`
11. `redshift a t₀ t₃ = 2 * √2 - 1`
12. `redshift a t₀ t₅ = 4 * √2 - 1`
13. `0 < H`

Classification (generated page TRUST_MAP.md): needed 2, 3, 4, 9, 10, 11, 12, 13; redundant (each alone, not together) 5, 6, 7; open 1, 8

### `eta_ratios` (full name `FREta.eta_ratios`)

Hypotheses (numbered as on the generated claims page):

1. `IsFRCosmo Ω a F t₀`
2. `F (curv a t₀) ≠ 0`
3. `correctR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) ≠ 0`
4. `cosmoCoeff 3 a t₀ - decel a t₀ - 2 ≠ 0`

Classification (generated page TRUST_MAP.md): needed 1; redundant 2; open 3, 4

### `fs_neg_reversed_printed_overshoots` (full name `FalknerSkan.NegReversedWallShear.fs_neg_reversed_printed_overshoots`)

Hypotheses (numbered as on the generated claims page):

1. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f (p η) (Set.Ici 0) η`
2. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p (q η) (Set.Ici 0) η`
3. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q (-(f η * q η) - -1988 / 10000 * (1 - p η ^ 2)) (Set.Ici 0) η`
4. `f 0 = 0`
5. `p 0 = 0`
6. `q 0 = -5158e-6`

Classification (generated page TRUST_MAP.md): needed 1, 2, 3, 6; open 4, 5
