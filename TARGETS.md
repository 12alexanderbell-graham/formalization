# TARGETS

Ranked candidates (annex XLII). Every candidate ever considered stays here with its reason for selection, deferral or rejection. Built in run 2026-10-30T0028Z from Physlib master `2725b6f` (142 `TODO` items, 18 files with `informal_lemma`/`informal_definition`) plus textbook/literature sources.

## 1. SELECTED — Cosmography: low-redshift expansions in FLRW (lookback time, χ, d_L, d_A)
- **Importance:** the Hubble series (Visser 2004/2005; Weinberg 1972 ch. 14) is how supernova and distance-ladder data are analysed model-independently (cosmography: q₀, j₀, s₀ fits). Taught in every cosmology course.
- **Checkability:** pure real analysis on the scale factor a(t): Taylor/Peano, local inversion, little-o algebra. All in Mathlib. Physlib already has the FLRW structure, `redshift`, `comovingDistance`, `transverseComovingDistance`, `decelerationParameter` (Distances.lean, Basic.lean), so results plug in upstream.
- **Error potential (the reason it outranks plain formalization):** published cosmographic series go to z⁴–z⁵ with jerk, snap, lerk and curvature terms and are copied between papers; higher-order coefficients and their stated validity (the z-series diverges for z > 1 in common models, Cattoen–Visser 2007) are where mistakes and hidden assumptions live. Plan: Lean-certified coefficients, then screen the published tables against them (sympy screen first, Lean for confirmation). Hidden-assumption angle already visible: how many derivatives of a(t) each order really needs, and whether "+ …" is asymptotic or convergent.
- **Prior art:** Physlib TODOs "Define the lookback time … prove its model-independent expansion" and "Prove the low-redshift expansions of χ, d_L and d_A … in terms of q₀" are open (Distances.lean). Cosmology in Physlib is actively developed by one contributor (P. Kevorkian, PRs #1634–#1861, Oct 2026): collision risk, mitigated by staying Mathlib-only until a contribution is prepared. No Lean/Isabelle/Coq cosmography found in a web search (2026-10-30).
- **First milestone:** lookback time to second order, o(z²) remainder. **DONE: PROVED this run** (see STATE).
- **Who it helps:** Physlib (closes two TODOs), cosmographers (machine-checked coefficients), anyone teaching the Hubble law.

## 2. Deferred — Simple pendulum: `periodFormula θ₀` is the period (Physlib TODO)
- Important, classic, Physlib has milestones 1–2 and half of 4 done; elliptic integral `Real.completeEllipticK` exists. Deferred: maintainers are actively on it (milestone list in the TODO, commits Oct 2026) — duplicating active human work; low error potential. Reopen if the TODO stalls for a month.

## 3. Deferred — Einstein static universe is an unstable equilibrium (Physlib TODO)
- Classic (Eddington 1930); a "settled question" angle exists (stability depends on perturbation class and fluid; Barrow et al. 2003 neutral stability to inhomogeneous modes). Homogeneous part is ODE linearisation, checkable. Deferred behind 1 because "unstable" must first be made precise (Underspecified) and the interesting inhomogeneous part needs perturbation theory Physlib lacks. Good second target.

## 4. Deferred — QHO: Hermite eigenstates orthonormal; ground state non-degenerate (Physlib TODOs)
- Useful, checkable (Mathlib has Hermite polynomials, Gaussian integrals). Low error potential: "known result now in Lean" only.

## 5. Deferred — Magnetic field of a circular current loop (Physlib TODO, NASA ref 20140002333)
- Engineering-relevant, possible typos in the reference (error potential). Needs Biot–Savart integration and complete elliptic integrals of the first and second kind (only K exists); larger infrastructure gap. Reopen after target 1 has its first finding screen.

## 6. Rejected for now — Hydrogen spectrum in d dimensions, essential self-adjointness (Physlib TODOs)
- Important but BLOCKED on unbounded-operator spectral theory far beyond a 5–15-run first result.

## 7. Rejected — Etherington duality d_L = (1+z)² d_A (Physlib TODO)
- With Physlib's definitions d_L = (1+z) r, d_A = r/(1+z) it is one line of algebra: trivial, no content (XLIII). Will be a free corollary inside target 1.

## 8. Noted, not ranked — Liouville–Arnold conclusion; Borel's lemma on spacetime; time-dependent div/curl results; Pöschl–Teller reflectionless; rigid-sphere cross section
- Large foundations (Liouville–Arnold, Borel) or modest content; revisit when target 1 parks.
