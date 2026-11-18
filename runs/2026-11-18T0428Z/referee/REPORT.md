# Referee report: run 2026-11-18T0428Z, GelfandPDECount

Verdict: STANDS-WITH-CORRECTIONS. Each conjunct is true and the reduction route is sound, but lam1 and lam2 are only constrained by 0 < lam1 < 2 < lam2 < lamStar. So the theorem is weaker than "exactly one for 0 < λ < λ(ζ₁), exactly two for λ(ζ₂) < λ < λ*".

## 1. Statement
- What the statement gets right: the solution class matches the classical one (C² on the open ball, C⁰ on the closed ball, u = 0 on the sphere, radial on the closed ball). Δ is Mathlib's basis-free Laplacian; it is evaluated at interior points of an open set where u is C², so no junk values arise. λ > 0 in every band. Equality is required only on the closed ball, which is correct because u is arbitrary outside. In the two-solution band, u 0 ≠ v 0 makes the two solutions genuinely different. The bands cannot be empty (0 < lam1 and lam2 < lamStar), and existence is required in each band, so no clause holds vacuously. lamStar is fixed by its 1e-9 enclosure together with the "none above, one at" clauses.
- Main defect: lam1 and lam2 are existential and only bounded by 2. A proof may pick lam1 tiny and lam2 just below lamStar. The formal statement then implies only "exactly one for small λ" and "exactly two for λ near λ*". It does not imply the sharp bands, and it does not imply the docstring's "lam1 is the first minimum, lam2 the second maximum".
- Fix, either of:
  - (a) add numeric enclosures for lam1 and lam2, e.g. 1.664156 ≤ lam1 ≤ 1.664157 and 2.108541 ≤ lam2 ≤ 2.108542 (values computed in §3);
  - (b) add sharpness clauses: exactly two solutions at lam1 and exactly three at lam2.
- Minor: "radial" is assumed, not proved. Gidas–Ni–Nirenberg would make all solutions radial, but this class is only C⁰ up to the boundary. The statement is right for what it says.

## 2. Route (checked by hand)
- Step (2), reduction to the ODE:
  - Put g(t) = u(t e₁). Then t ↦ g(|t|) is C² and even on (-1, 1), so g'(0) = 0 and Δu = g'' + (2/r) g' for r > 0.
  - Choose s = sqrt(λ e^{u(0)}) and set w(ρ) = g(ρ/s) − log(s²/λ). Then w(0) = 0, w'(0) = 0, w' is continuous at 0, and w'' + (2/ρ) w' + e^w = 0 on (0, s).
  - Uniqueness (the new result) on [0, T] for every T < s gives w = W on [0, s).
  - u is continuous on the closed ball, so g is continuous at 1. Hence w(s) = W(s), and g(1) = 0 gives s² e^{W(s)} = λ.
  - The scaling is also correct the other way: Δ[W(s|x|)] = −s² e^{W(s|x|)} and λ e^{log(s²/λ)} = s², so the PDE holds.
  - The centre value is log(s²/λ), so distinct radii give distinct centre values.
  - No gap, provided the formal uniqueness covers w on [0, T] with T < s (it does, by the stated class).
- Step (4), counting radii in each band:
  - λ > λ*: no radius, since λ(s) ≤ λ(ζ₀) everywhere.
  - λ = λ*: only s = ζ₀ (strict maximum).
  - λ(ζ₂) < λ < λ*: one radius in (0, ζ₀) (increasing from 0 to λ*) and one in (ζ₀, ζ₁) (decreasing to λ₁ < 2 < λ). On [ζ₁, ∞), λ(s) ≤ λ(ζ₂) < λ. Total 2.
  - 0 < λ < λ(ζ₁): one radius in (0, ζ₀). On [ζ₀, ∞), λ(s) ≥ λ(ζ₁) > λ. Total 1.
  - Ends: open bands, so the endpoints never need counting. The step is correct; it needs the route to take lam1 = λ(ζ₁) and lam2 = λ(ζ₂), which it does.

## 3. Independent computation (scripts/count.py)
Method: DOP853 integration (rtol 1e-13) from a series start at s = 1e-3; turning points located where 2 + sW' = 0.

| k | ζ_k | λ(ζ_k) |
|---|---|---|
| 0 | 4.0714968443 | 3.3219921183 |
| 1 | 37.5267987 | 1.6641561898 (λ₁) |
| 2 | 428.912529 | 2.1085411021 (λ₂) |
| 3 | 4532.14862 | 1.9674655587 |
| 4 | 48978.393 | 2.0099764050 |
| 5 | 525619.6 | 1.99696204 |

ζ₀ and λ* agree with the given enclosures.

Radii with λ(s) = λ (beyond 1e6 the extrema lie within (1.9969, 2.0100), so no further roots for these λ):

| λ | radii | count |
|---|---|---|
| 1 | 1.0998 | 1 |
| 1.5 | 1.4300 | 1 |
| λ₁ − 0.01 | 1.5334 | 1 |
| λ₂ + 0.01 | 1.8667, 12.7471 | 2 |
| 3 | 2.7969, 6.2678 | 2 |
| 3.3 | 3.6887, 4.5091 | 2 |

All counts match the claims.

## 4. Prior art (brief; no pages fetched, so nothing below was read)
- I. M. Gel'fand, "Some problems in the theory of quasilinear equations", AMS Transl. (2) 29 (1963): the 3-D ball, radial reduction via the isothermal (Emden) equation, and numerics for λ* ≈ 3.32.
- D. D. Joseph & T. S. Lundgren, "Quasilinear Dirichlet problems driven by positive sources", Arch. Rational Mech. Anal. 49 (1973): for 3 ≤ N ≤ 9 the solution curve oscillates around λ = 2(N − 2) (= 2 in 3-D), giving infinitely many solutions at λ = 2, a finite but arbitrarily large number near 2, and the turning-point values. The WebSearch only confirmed the title (mardi4nfdi / scilit listing).
- Later work: P. Korman, "Global solution curves for self-similar equations" (arXiv 1610.05152; the search returned only ar5iv mirrors, which the rules exclude, so not read). Standard texts treat the multiplicity picture: Dupaigne, "Stable solutions of elliptic PDEs" (2011), and Bandle's monographs.
- The exact counts per band follow directly from the bifurcation diagram these works describe. I found no published sharp numeric value for λ₁ or λ₂ in this search.

## 5. Verdict
STANDS-WITH-CORRECTIONS:
- Every conjunct is true (with the true λ(ζ₁) and λ(ζ₂) as witnesses), it is not vacuous, and the route is correct.
- Correction: as frozen, lam1 and lam2 are not pinned, so the bands are not the sharp ones. Add enclosures or sharpness clauses (§1) if the claim is meant to be "exactly one/two on the maximal bands".
