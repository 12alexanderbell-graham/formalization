# BLUEPRINT

Target 1: cosmographic (low-redshift) expansions. Nodes with statuses (annex XXXVIII). Mathlib-only; definitions mirror Physlib's.

- `peano2` (Peano 2nd-order Taylor at a point, a differentiable near, a′ differentiable at t₀): PROVED (helper, Checked).
- `peano3` (3rd order): PROVED in Work (helper; copy in Checked).
- M1 `lookback_second_order` (o(z²)): **PROVED** (Checked, AUDITED).
- M1b `lookback_second_order_bigO` (O(z³), C³): **PROVED** (Checked, AUDITED).
- M2 d_L = (c/H₀)[z + ½(1 − q₀)z² + o(z²)], needs χ = c∫dt/a expansion and r = S_k(χ): not started.
- M3 d_L z³ coefficient −(1/6)[1 − q₀ − 3q₀² + j₀ + kc²/(H₀²a₀²)] (curvature enters): not started.
- M4 series inversion to fifth order: **done for lookback time** (`Checked.Cosmography.CCS.inversion`: if u = A(x) + o(x⁵) with A the quintic of (A1), then x − P(1/u − 1) = o(x⁵); truncated-power method with sympy-generated remainder polynomials, `runs/2026-10-30T0628Z/scripts/gen2.py`). Reusable for d_L, d_Q, χ series (C1, M2, M3) by changing A and P.
- F1 (was C2) `flatLCDM_coeffs`, `avilesL0Claim_false`, `avilesM0Claim_false`, `printedL0_false_at`, `printedM0_false_at`: **PROVED** (Checked, AUDITED). Method reusable: polynomial Friedmann identity, repeated `step`, generated certificates.
- F2 (was C4) `Checked.Cosmography.CPL.flatCPL_coeffs` (q₀…l₀ of flat matter + CPL, every Ω, w₀, wₐ), `printedL0_ne`, `clsL0Claim_false`, `CPLExistence.exists_flatCPL`, `printedL0_false_at`: **PROVED** (Checked, AUDITED; CI in STATE). Reusable: `CPLExistence.exists_local_model` (any smooth law H/H₀ = E(a/a₀) has a C⁵ model near t₀; Picard–Lindelöf), and the two-identity generator `runs/2026-10-30T0430Z/scripts/gen_cpl.py` (auxiliary function for non-polynomial factors + chain-rule identity).
- F3 (was C3) `Checked.Cosmography.CCS.lookback_fifth_order` (general fifth-order lookback series, any C⁵ a), `printedD4_fails`, `printedD4_fails_past`, `ccsD4Claim_false`, `ccsD4ClaimPast_false`: **PROVED** (Checked, AUDITED; CI in STATE).
- R⁵_D (CCS 2008 A5, comoving distance in powers of H₀D/c, l₀/6 vs l₀/720): sympy only; would need χ(x) = ∫dx/A(x) expansion (Taylor of 1/a, integrate): not started.
- C1 refutation (d_Q(y) y² coefficient): needs d_L to O(z³) (M3) or an explicit model; not started.
