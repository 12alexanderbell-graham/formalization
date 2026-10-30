# BLUEPRINT

## Trust track T1 (definition fidelity), `Work/Fidelity/`
- Specs + `meets_spec`: LumDistSpec, LumDistSpec2, HubbleSpec, DecelSpec, AngDistSpec, FlatLCDMSpec: PROVED in Work (not audited for Checked).
- Pins: `lumDistSpec2_pins`, `hubbleSpec_pins`, `Gaps.decelSpec_pins`, `Gaps.angDistSpec_pins`: PROVED in Work. `flatLCDMSpec_pins`: not started.
- Mutation benchmark: 30/30 blind + 10/10 author refuted (Work). Spec gaps: 4 found, 4 closed.
- Next: promotion to Checked with audit; CI report of unpinned definitions; T2.

Target 1: cosmographic (low-redshift) expansions. Nodes with statuses (annex XXXVIII). Mathlib-only; definitions mirror Physlib's.

- `peano2` (Peano 2nd-order Taylor at a point, a differentiable near, a′ differentiable at t₀): PROVED (helper, Checked).
- `peano3` (3rd order): PROVED in Work (helper; copy in Checked).
- M1 `lookback_second_order` (o(z²)): **PROVED** (Checked, AUDITED).
- M1b `lookback_second_order_bigO` (O(z³), C³): **PROVED** (Checked, AUDITED).
- M2 d_L = (c/H₀)[z + ½(1 − q₀)z² + o(z²)], needs χ = c∫dt/a expansion and r = S_k(χ): **flat case done in y** (F4 node; to y³); z version and curved S_k not started.
- Tool `littleO_of_hasDerivAt` (R(t₀)=0, R′ = o((t−t₀)ⁿ) ⇒ R = o((t−t₀)ⁿ⁺¹); mean-value inequality) + FTC for χ = ∫dt/a: **PROVED** (Checked, in `BambaDLy`). Gives the comoving distance to any order from the Taylor polynomial of 1/a.
- M3 d_L z³ coefficient −(1/6)[1 − q₀ − 3q₀² + j₀ + kc²/(H₀²a₀²)] (curvature enters): not started.
- M4 series inversion to fifth order: **done for lookback time** (`Checked.Cosmography.CCS.inversion`: if u = A(x) + o(x⁵) with A the quintic of (A1), then x − P(1/u − 1) = o(x⁵); truncated-power method with sympy-generated remainder polynomials, `runs/2026-10-30T0628Z/scripts/gen2.py`). Reusable for d_L, d_Q, χ series (C1, M2, M3) by changing A and P.
- F1 (was C2) `flatLCDM_coeffs`, `avilesL0Claim_false`, `avilesM0Claim_false`, `printedL0_false_at`, `printedM0_false_at`: **PROVED** (Checked, AUDITED). Method reusable: polynomial Friedmann identity, repeated `step`, generated certificates.
- F2 (was C4) `Checked.Cosmography.CPL.flatCPL_coeffs` (q₀…l₀ of flat matter + CPL, every Ω, w₀, wₐ), `printedL0_ne`, `clsL0Claim_false`, `CPLExistence.exists_flatCPL`, `printedL0_false_at`: **PROVED** (Checked, AUDITED; CI in STATE). Reusable: `CPLExistence.exists_local_model` (any smooth law H/H₀ = E(a/a₀) has a C⁵ model near t₀; Picard–Lindelöf), and the two-identity generator `runs/2026-10-30T0430Z/scripts/gen_cpl.py` (auxiliary function for non-polynomial factors + chain-rule identity).
- F3 (was C3) `Checked.Cosmography.CCS.lookback_fifth_order` (general fifth-order lookback series, any C⁵ a), `printedD4_fails`, `printedD4_fails_past`, `ccsD4Claim_false`, `ccsD4ClaimPast_false`: **PROVED** (Checked, AUDITED; CI in STATE).
- R⁵_D (CCS 2008 A5, comoving distance in powers of H₀D/c, l₀/6 vs l₀/720): sympy only; would need χ(x) = ∫dx/A(x) expansion (Taylor of 1/a, integrate): not started.
- F5 (was C1) `Checked.Cosmography.CVdQ.dQ_y_third_order` (flat d_Q(y) to y³), `printedQ2_fails_past`, `cvdQClaim_false`, `cvdQClaimPast_false`: **PROVED** (Checked, AUDITED; CI in STATE). Tool `rpow_expansion` ((1−u)^{3/2} to u², by two MVT steps).
- F4 (was C5) `Checked.Cosmography.BambaY.lumDist_y_third_order` (flat d_L(y) to y³, any C³ a), `printedD2y_fails`, `printedD2y_fails_past`, `bambaD2yClaim_false`, `bambaD2yClaimPast_false`: **PROVED** (Checked, AUDITED; CI in STATE).
- F6 (was C6) `Checked.Cosmography.BambaK.lumDist_y_fifth_order` (curved d_L(y) to y⁵, every real K, any C⁵ a; d_L = a₀(1+z)S_K(∫dt/a)), `printedD3y_fails[_past]`, `printedD4y_fails[_past]`, `bambaD3yClaim[Past]_false`, `bambaD4yClaim[Past]_false`, Milne instances: **PROVED** (Checked, AUDITED; CI in STATE). Helper `Checked.Cosmography.Transverse.transverse_expansion` (S_K(χ) to χ⁵). Tool: truncated-series algebra `approx_mul`/`approx_pow` (f ≈ p means f − p(X) = o(X⁵)), generator `runs/2026-10-30T1028Z/scripts/gen_curved.py`.
- F7 (was C7) `Checked.Cosmography.BambaA.angDist_y_fifth_order` (curved d_A(y) to y⁵), `printedDA3_fails[_past]`, `printedDA4_fails[_past]`, `bambaDA*Claim*_false`, Milne D⁴ instance: **PROVED** (Checked, AUDITED; CI in STATE). Corollary: (1−y)²·F6 theorem + one `ring` identity.
- F8 (was C9) `Checked.Cosmography.BambaZ.lumDist_z_fifth_order`, `angDist_z_fifth_order` (curved d_L(z), d_A(z) to z⁵, every real K, any C⁵ a), `printedDL4z_fails_past`, `printedDA4z_fails_past`, `bamba*Claim*_false`, Milne instance: **PROVED** (Checked, AUDITED; CI in STATE). Method: exact identity (1+z)⁵[S_y(z/(1+z)) − S_z] = z⁶W (`runs/2026-10-30T1232Z/scripts/gen_z.py`) + `transfer` (o(y⁵) → o(z⁵)).
- F9 (was C13, C11) `Checked.Cosmography.FRCosmo.fR_values` (metric F(R) FLRW: F(R₀), F″(R₀), F‴(R₀) from q₀…l₀, every model, no nondegeneracy), `curv_derivs`, `exists_LCDM_model`, `printedR3Claim_false`, `printedF0Mul_false_at`, `printedF0ClaimMul_false`, `printedF0_false_at`, `printedF0Claim_false`: **PROVED** (Checked, AUDITED; CI in STATE). Method: differentiate the master equation as an eventual identity (derivative uniqueness), H-derivatives from cosmography (`hvals`), sympy certificates (`runs/2026-10-30T1428Z/scripts/cert_lean.py`).
- F10 (was C14) `Checked.Cosmography.FREta.eta_ratios`, `eta20_hasDerivAt`, `eta30_hasDerivAt`, `printedEta20_false_at`, `printedEta30_false_at`, `printedEta*Claim_false`, `eta_numbers`: **PROVED** (Checked, AUDITED; CI 41093965309). Tool: `hasDerivAt_mul_cont` (ε·K(ε) has derivative K(0) when K is only continuous at 0).
- F11 (was C15, C16) `Checked.Cosmography.DemianskiZ.flat_corrections`, `demDL4_fails_past`, `demDA4_fails_past`, `demD*zClaim*_false`: **PROVED** (Checked, AUDITED; CI in STATE). Pattern: any printed z-series to z⁵ is checked against `BambaZ.lumDist_z_fifth_order`/`angDist_z_fifth_order` in one subtraction (`not_isLittleO_self_past_z`).
- C10 (R⁴_D, R⁵_D): next; comoving distance in powers of H₀D/c via `littleO_of_hasDerivAt`, then S_K.
- C11–C14 (Sec. XI F(R) cosmography): algebraic relations between R-derivatives and (q₀, j₀, s₀, l₀); Lean route: R = −6(Ḣ + 2H²) derivatives at t₀ as polynomial identities in a⁽ⁿ⁾(t₀) (no asymptotics).
