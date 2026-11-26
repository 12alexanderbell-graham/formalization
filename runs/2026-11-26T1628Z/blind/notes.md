# Notes (blind restatement, H2+ ground state, R = 2)

## Derivation
1. r1 = R(ξ+η)/2, r2 = R(ξ-η)/2; with R = 2: r1 = ξ+η, r2 = ξ-η.
2. 1/r1 + 1/r2 = (r1+r2)/(r1 r2) = 2ξ/(ξ²-η²).
3. For m = 0 (no φ dependence), Δ = 4/(R²(ξ²-η²)) [∂ξ((ξ²-1)∂ξ) + ∂η((1-η²)∂η)]; R = 2 gives 1/(ξ²-η²)[...] (standard formula, recalled, not rederived).
4. Hψ = εψ: -½Δψ - 2ξ/(ξ²-η²) ψ = εψ. Multiply by -2(ξ²-η²):
   [∂ξ((ξ²-1)∂ξ) + ∂η((1-η²)∂η)]ψ + 4ξψ + 2ε(ξ²-η²)ψ = 0.
5. Put ψ = L M, divide by LM:
   [((ξ²-1)L')'/L + 4ξ + 2εξ²] + [((1-η²)M')'/M - 2εη²] = 0.
   First bracket depends only on ξ, second only on η, so first = A, second = -A.
6. Result: ((ξ²-1)L')' + (4ξ + 2εξ² - A)L = 0 and ((1-η²)M')' + (A - 2εη²)M = 0.
   Expanded: (ξ²-1)L'' + 2ξL' + ..., (1-η²)M'' - 2ηM' + ...
7. Total energy E = ε + 1/R = ε + 1/2, so ε = E - 1/2 in the file.

## Choices
- Sign convention: A enters the ξ equation as -A·L and the η equation as +A·M.
- E is existentially quantified in [-0.6026342144950, -0.6026342144949]; ε = E - 1/2.
- Derivatives are supplied as witness functions L', L'', M', M'' with HasDerivAt on the open intervals (ξ>1, |η|<1), so the equations are classical C² statements there.
- Regularity: the endpoints ξ=1, η=±1 are regular singular points; the second solution diverges logarithmically, so continuity of L on [1,∞) and M on [-1,1] selects the regular solution.
- Bound: L → 0 at infinity and ∫ L² ξ² dξ < ∞ (IntegrableOn on Ici 1). The volume element is (R/2)³(ξ²-η²)dξdηdφ, and ξ²-η² ≤ ξ² gives the weight, with M bounded by continuity.
- Ground state: L > 0 on [1,∞) and M > 0 on [-1,1] (no nodal surface). This also rules out the trivial solution.

## Not captured
- That E is actually the lowest eigenvalue of the 3D operator (only that a nodeless separated solution exists at E; nodelessness implies ground state in the real theory but this is not proved or stated via the 3D operator).
- Self-adjointness, the 3D operator, and the formula for Δ are not formalized; the separated ODEs are taken as the definition.
- m ≠ 0 and gerade/ungerade symmetry are not stated (M > 0 and nodeless imply even M, but this is not asserted).
- Normalizability is only checked in ξ, not as a full 3D integral.
- A is not pinned to a value; the interval check is only on E.
