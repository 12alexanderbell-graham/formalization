# Referee report (run 2026-11-15T0028Z): `bonnor_ebert_all_extrema`

Copied by the main session from the referee subagent's final message (its own write to this file was refused by the harness). Model output, unchecked prose.

**Verdict: STANDS.** Statement faithful and true; the planned route closes. Two optional improvements: (1) "every extremum" is literal only with StrictMonoOn/StrictAntiOn conjuncts on [0, ξ₀] and each [ξ_k, ξ_{k+1}] (the statement as frozen forces the sequence uniquely — each ξ_{k+1} is the unique strict argmin/argmax of a tail — but does not itself exclude other critical points between them; there are none, the critical points of m are the simple zeros of 2u − v); (2) the module doc's "states every extremum at once" slightly overclaims.

## Independent computation (two methods: own mpmath Taylor integrator in t = log ξ, orders 30/40 at 32/40 digits; scipy DOP853 rtol 1e-13 on (w, φ) and on (u, v); agree to ≈ 1e-13 in m)

| k | ξ_k | m(ξ_k) | type |
|---|---|---|---|
| 0 | 6.450751444174073658 | 1.182226588499599725 | max |
| 1 | 67.00754871959523972 | 0.6943665211285553788 | min |
| 2 | 733.7692436865978120 | 0.8306900582755193384 | max |
| 3 | 7849.632048500426931 | 0.7879941879276726972 | min |
| 4 | 84506.32897574492584 | 0.8009119500784999699 | max |
| 5 | 907946.1931537093181 | 0.7969621752385025307 | min |
| 6 | 9760974.981040021166 | 0.7981659905960546687 | max |
| 7 | 104917043.8187439459 | 0.7977987305175917470 | min |

Limit √(2/π) = 0.79788456080286535588; (iv) holds for all eight; spacing ≈ e^{2π/√7} = 10.74. N at ξ = 300000: 3.2313241407964889e-5 (u = 0.998005548042333, v = 2.002054152079357).

Route claims on N ≤ 1/400 (sympy identities; grid 500 radii × 200001 angles): dN/dt = −N − 4e₁(4e₁² + 4e₁e₂ − e₂²) ≤ −0.9596 N analytically (grid −0.96419); cross product e₁ė₂ − e₂ė₁ = 2e₁² + e₁e₂ + e₂² + e₁e₂(2e₁ + e₂) ≥ 0.7615 (e₁² + e₂²) analytically (grid 0.791258); d(2u − v)/dt = 8u(1 − u), m = u²√(2/π) and N = 32(u − 1)² at zeros of 2u − v: exact. After 300000, |u − 1| ≤ 1.005e-3 at every zero, so every later extremum mass lies in [0.79628, 0.79949] ⊂ (m(ξ₃), m(ξ₄)).

## Prior art (WebFetch summaries UNVERIFIED)
Chandrasekhar (1939/1942) homology plane and spiral to (1, 2) (not read directly); Ebert 1955, Bonnor 1956 critical sphere (not read). Chavanis, arXiv astro-ph/0207080 (arxiv.org/pdf, UNVERIFIED): fixed-pressure case with 𝒫 = u₀v₀³ = 4πm², extrema at 2u₀ − v₀ = 0, spiral towards (𝒱, 𝒫) = (1/8, 8), i.e. m → √(2/π) — the infinite alternating sequence and the limit are in print in equivalent units, by phase-portrait/asymptotic arguments, not a proof; only the first critical point numerically. Chavanis astro-ph/0103159 (fixed box, asymptotic). Joseph & Lundgren 1972/73 (cited in arXiv 2507.06760; original not read): rigorous infinitely many turning points of the Gelfand curve λ = uv for 3 ≤ N ≤ 9 — same ODE and spiral, different quantity; does not give the strict band property. Not found: any rigorous proof of the band/envelope property or a certified enclosure of ξ₀ to seven decimals (search limited).
