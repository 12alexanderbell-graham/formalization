# Referee report: `GelfandPDEMany.lean` (run 2026-11-15T1828Z)

(Relayed by the run from the referee's final message: the referee's Write was refused. Script: `scripts/gelfand_count.py`; Lean not run.)

**Verdict: FALLS as frozen.** All three conjuncts are true, but the distinctness conditions can be met trivially, so the statement says nothing about multiplicity. A one-line change to each distinctness clause fixes it, and the planned route then proves the corrected statement. Solution class, quantifiers, constants and IVT steps are sound.

## 1. Attack on the statement
**Main defect: distinctness can be satisfied trivially.** `Function.Injective u` in (i) and (ii), and `u ≠ v` in (iii), compare functions on all of `EuclideanSpace ℝ (Fin 3)`. Every other condition only looks at the closed ball: `ContDiffOn … (ball 0 1)` and `ContinuousOn … (closedBall 0 1)` depend only on values there; the sphere and radial conditions only on ‖x‖ ≤ 1; `Δ (u i) x` at a point of the open ball only on the germ at x (`Filter.EventuallyEq.iteratedFDeriv`). So from one radial solution u₀, `u i x = if ‖x‖ ≤ 1 then u₀ x else (i : ℝ)` is injective and meets every condition. (i) follows from one solution at λ = 2, (ii) with ε = 1 from one solution for each λ in (1, 3), (iii) from one solution for each λ in [2, 3.321992118): all from `gelfand_pde_radial_exists`.

**Correction.** Compare inside the ball: in (i), (ii) `∀ i j, (∀ x ∈ ball 0 1, u i x = u j x) → i = j`, or the stronger `Function.Injective (fun i => u i 0)` (distinct centre values), which the route also delivers; in (iii) `∃ x ∈ ball 0 1, u x ≠ v x`.

**Other checks (fine):** solution class is the standard classical radial class; no junk values (`Real.exp` total, no division or log); ∃ε before ∀λ in (ii), N = 0 trivial; 3.321992118 < λ* ≈ 3.3219921183, and the bracket λ(ζ₀) ≥ 3.321992118 makes (iii)'s upper end strict.

## 2. Planned route, by hand
- u(r) = W(sr) + c: u'' + (2/r)u' = −s² e^{W(sr)}, λeᵘ = λe^c e^{W(sr)}; c = log(s²/λ) (λ > 0) cancels; u(1) = 0 iff s² e^{W(s)} = λ. Correct.
- u(0) = log(s²/λ) strictly increasing in s > 0: distinct radii give solutions differing at the centre (proves the corrected distinctness).
- (i): endpoint values straddle 2 strictly on every [ζ_k, ζ_{k+1}]; IVT radius in the open interval; disjoint intervals → injective.
- (ii): 0 < ε ≤ min(1, min_{k ≤ N} |λ(ζ_k) − 2|) → λ > 0 and λ strictly between the endpoint values for each k < N. Correct.
- (iii): on [0, ζ₀], λ(0) = 0 < λ < λ(ζ₀); on [ζ₀, ζ₁], λ(ζ₁) < 2 ≤ λ < λ(ζ₀). Correct (λ = 2 included).
- Work item, not a flaw: the cited construction covers s < 41/10 only; redo it for every s > 0 with the global W.

## 3. Independent computation
v = log λ(s), t = log s gives v'' + v' − 2 + e^v = 0; scipy DOP853, rtol 1e-13, atol 1e-15, series start at s = 10⁻³, to s = 10¹².

| k | ζ_k | λ(ζ_k) | type |
|---|---|---|---|
| 0 | 4.0714968443 | 3.3219921183 | max |
| 1 | 37.5267987393 | 1.6641561898 | min |
| 2 | 428.9125290822 | 2.1085411021 | max |
| 3 | 4532.1486191161 | 1.9674655587 | min |
| 4 | 48978.3931096925 | 2.0099764050 | max |
| 5 | 525619.5981252041 | 1.9969620363 | min |

12 turning points up to 10¹² (λ(ζ₁₁) ≈ 1.9999975530); ratio ζ_{k+1}/ζ_k ≈ 10.7.

Radii (= radial solutions) found for s ≤ 10¹²: λ = 2.0: 12 (one per segment; infinitely many); 2.05: 4; 2.5: 2; 3.3: 2; 3.321992117: 2; 1.95: 3; 1.9: 3; 1.5: 1; 1.0: 1. The count drops to one below λ(ζ₁) ≈ 1.6641561898: (iii) could be extended to λ(ζ₁) ≤ λ < λ*; 2 is conservative but correct.

## 4. Prior art (brief)
D. D. Joseph and T. S. Lundgren, "Quasilinear Dirichlet problems driven by positive sources", Arch. Rational Mech. Anal. (1973), DOI 10.1007/BF00250508 (read through WebFetch of the MaRDI portal: UNVERIFIED; vol. 49, pp. 241–269 from memory): infinitely many solutions at λ = 2(N − 2) for 3 ≤ N ≤ 9, oscillation of λ(s), Emden–Fowler phase plane. Earlier: Gel'fand (1959/1963), crediting N = 3 to Barenblatt. Later work seen as search titles only (not read): Dolbeault–Flores (Trans. AMS), arXiv 2512.14577, a Proc. Roy. Soc. Edinburgh p-Laplacian paper, Castro EJDE 2007.

## 5. Verdict
FALLS as frozen (distinctness outside the ball). With distinctness on the open ball or at the centre, the statement is the right formalization and the planned route proves it.
