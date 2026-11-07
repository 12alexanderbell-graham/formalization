# BLUEPRINT

## Trust track T1 (definition fidelity), `Checked/Fidelity/` (specs, pins) and `Work/Fidelity/` (benchmarks, blind originals)
- Specs + `meets_spec`: LumDistSpec, LumDistSpec2, HubbleSpec, DecelSpec, AngDistSpec, FlatLCDMSpec: **PROVED** (CI 41114284138). Run 2028Z: FlatLCDMSpec2 + FriedmannLCDM (blind), RedshiftSpecCore, CosmoCoeffSpecCore, YRedSpec, Omega0Spec, CurvKSpec (blind, verbatim): AUDITED (`runs/2026-10-30T2028Z/audit_friedmann.md`, `audit_pins2.md`), CI in STATE.
- Pins (17 definitions): `lumDistSpec2_pins`, `hubbleSpec_pins`, `decelSpec_pins`, `angDistSpec_pins` (PROVED); run 2028Z: `flatLCDMSpec2_pins` + `isFlatLCDM_iff_friedmann` (PROVED, CI 41125393349), `redshiftCore_pins`, `cosmoCoeffCore_pins`, `yRedSpec_pins`, `omega0Spec_pins`, `curvKSpec_pins`, `lumDistFlat_pins`, `comoving_pins`, `flatCPL_pins` + `isFlatCPL_iff_friedmannCPL`, `ricciSpec_pins`, `rhoM_eq_dust`, `friedmannEq_iff_blind`, `masterEq_iff_blind` (AUDITED; CI in STATE).
- Trust map (`scripts/trust/StatementDeps.lean`, `TRUST_MAP.md`, CI step): per headline, the definitions its statement rests on. 77 of 82 physics headlines rest only on pinned definitions. Unpinned: `dQFlat` (F5), `transverse` (helper).
- Mutation benchmark: 30/30 blind + 10/10 author refuted (Work). Spec gaps: 4 + 4 found, all closed by pins.
- Run 2228Z: `transverse` pinned (`Checked/Fidelity/TransverseSpec.lean`, blind ODE law, `transverseSpec_pins`); `dQFlat` PRINTED. 101/101 headlines on pinned definitions; CI-blocking.

## Trust track T2 (statement fidelity), `Checked/Trust/`
- `NonVacuity.lean` (obligation generator, `nonvacuity%`), `Witnesses.lean` (62 witnesses): **PROVED**-level checks in CI (blocking). Adversarial review `runs/2026-10-30T2228Z/nv_adversary.md`.
- Next: hypothesis necessity (T2b).
- Run 2026-11-04T2228Z: generated claims `scripts/trust/Claims.lean` → `CLAIMS.md` (151 headlines; phrases `scripts/trust/phrases.txt`, lint `scripts/trust/check_claims.py`), CI-blocking; red team J results `runs/2026-11-04T2228Z/t5/RESULTS.md`.

## Trust track T5 checks added run 2026-11-04T1028Z (after blind red team G, 8/8 accepted)
- Number rule (rule 5 of `scripts/trust/check_prose.py`): blocking; units read; citations only from `scripts/trust/citations.txt`.
- Frozen docstrings of every Checked declaration (`doc:` entries from `scripts/trust/StatementDeps.lean`).
- `scripts/trust/check_trusted_defs.py --base`: every new or changed TRUSTED_DEFINITIONS.md line disclosed.
- `scripts/trust/AuditClosed.lean` + `scripts/trust/audits.txt` (418 closed audit theorems) + `check_audits.py`: closed audits stay closed (CI work job).
- Next node: parameter-level prose (G02/E08).

## B1 (THE RESULT part 2), `Checked/Cosmography/B1Truncation.lean`
- Bridge `lumDistFlat_flatLCDM` (FTC, substitution v = (1+z)^{-1/2}): **PROVED** (AUDITED).
- Certified enclosures of ∫ 2/√(Ω+(1−Ω)v⁶) (Riemann sums, tangent/secant bounds; `J_lower`, `J_upper`, tool lemmas `rsum_le_integral`, `integral_le_lsum`, `tangent_le`, `le_secant`): **PROVED** (helpers).
- `cubic_misses_z3`, `cubic_misses_z7`, `cubic_shape_miss`: **PROVED** (AUDITED). Witness `exists_flatLCDM_on`: PROVED.
- `Checked.Cosmography.B1Sep.cubic_separation` (any cubic agreeing with exact ΛCDM within 0.05 mag at z = 3, 7 up to an offset lies > 5/4 from the ΛCDM point) and `cubic_direction` (on the side a₂ − a₂^ΛCDM < 7 log₁₀2 (a₃ − a₃^ΛCDM)): **PROVED** (AUDITED, run 0828Z; frozen first; both blind restatements closed in Lean; referee STANDS-WITH-CORRECTIONS; NV witness `B1SepWitness.hyps_satisfiable`).
- Run 2026-11-04T0228Z: second-order certified quadrature (`Checked/Cosmography/B1FitTools.lean`: `cell_lower`, `cell_upper`, `sum_lower`, `sum_upper`; certificates `B1FitCerts.lean`); `Checked.Cosmography.B1Fit.fit_direction` (fit level: three quasar-range redshifts, Ω ∈ [0, 1]) and `Checked.Cosmography.B1FitRL19.rl19_box_unmatched` (C27): **PROVED** (AUDITED; frozen first; blind restatements closed in Lean; referee STANDS-WITH-CORRECTIONS; NV witnesses `B1FitWitness.hyps_satisfiable`, `B1FitRL19.hyps_satisfiable`).
- Run 2026-11-04T1228Z: `Checked.Cosmography.B1L19.l19_sq_central`, `l19_sqg_central`, `l19_sq_box`, `l19_sqg_box` (Lusso et al. 2019 Table 2 quasar fits vs exact flat ΛCDM: residual rises > 7/20, > 3/10 mag between 1 + z = 2√2 and 4√2, and strictly beyond the 1σ ends, every Ω ∈ [0, 1]): **AUDITED** (frozen first 6dd5bc8; blind restatement closed in Lean; referee STANDS-WITH-CORRECTIONS; NV witnesses `B1L19.hyps_satisfiable_central`, `hyps_satisfiable_box`) and **PROVED** (promotion CI 41836943693 green). Certificates `B1L19Certs.lean` (ratio 2J₅/J₃ ≥ 2.84, 8 Ω-pieces).
- Run 2026-11-04T2028Z (Work, promotion next run): `Work/Cosmography/B1L19CurvedTools.lean` (integrand gC m k v = 2/√(m + k v² + (1−m−k)v⁶), positivity on the domain, bridge `comoving_eq` and `lumDist_eq` for the pinned `lumDist K`, tangent/chord cells linear in (m, k), `cell_y` side conditions from rational checks), certificates `B1L19CurvedCerts{0,1,2}.lean` + dispatch `B1L19CurvedRatio.lean` (42 boxes), reduction `B1L19CurvedProof.lean` (`S_ratio`: sin bounds; `delta_core`: shared with the audit), statements `B1L19Curved.lean`, audit `B1L19CurvedAudit.lean` (`comoving_eq_within`: one-sided derivatives, free H₀).
- Next node: the least-squares/minimax fit as a Lean object with certified residuals; σ comparison needs the RL19 covariance (not printed).

## Trust track T3 (transcription fidelity), `Checked/Trust/`
- `SecondReading.lean` (blind second transcription, 23 coefficients), `Transcriptions.lean` (23 agreement theorems). Next: remaining 15 PRINTED definitions.

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
- T5 (run 0028Z): false-acceptance benchmark `runs/2026-10-31T0028Z/t5/` (24 seeded defects, 3 red teams, judge harness). Checks added: frozen registry (`scripts/trust/frozen.txt`, `check_relock.py`), unused binders, pin shape, records citations, Work-import ban, stale map. Before 15/15 accepted, after 6/15 (A+B).
- Chemistry (run 0628Z) `Checked.Chemistry.CubicEOS.isCritical_iff`, `critCubic_existsUnique`, `exists_unique_critical`, `vdW_constants`, `rk_constants`, `pr_constants`: **PROVED** (Checked, AUDITED). Methods: critical conditions → one cubic by `linear_combination`; root uniqueness by the convexity identity; constants by reduction modulo the critical cubic (sympy quotient `runs/2026-10-31T0628Z/scripts/red.py`) + root enclosure (`root_bounds`). Pin `Checked.Fidelity.CriticalSpec.criticalSpec_pins`.
- Chemistry (runs 2026-10-31T1228Z/1428Z, 2026-11-04T0028Z) `Checked.Chemistry.Coexistence.vdW_coexistence_exists`, `vdW_coexistence_unique`: **PROVED** (Checked, AUDITED; frozen 1432f15). Methods: reduced variables; uniqueness window by Rolle, root localisation of g′ (divided difference) and rational brackets with one log bound per side (`CoexistenceReduced.reduced_window`); existence by continuity of compact suprema of ψ_π on two windows + IVT, interior maximizers lie on the isotherm (`CoexistenceExists.reduced_exists`); ω from the window (`acentric_window`). Pin `Checked.Fidelity.MaxwellSpec.maxwellSpec_pins` (equal-chemical-potential law); mutants 10/10 refuted (`Work/Fidelity/MaxwellMutantsReject.lean`).
- T2c prose and meaning (run 1028Z): `scripts/trust/check_prose.py` (blocking) checks docstrings, names and statement shape against `.lake/meaning.jsonl` (pinned definitions and written-out pinned laws each headline reaches; shape after unfolding the program's claims); docstrings of headlines and pinned definitions frozen. Closed T5 holes A04, A05, B04, D04; red team E judged in `runs/2026-10-31T1028Z/t5/RESULTS.md`.
- T5 blind round F (run 2026-11-04T0428Z): red team F (Sonnet, 8 defects against 7221e29) all accepted by the checks of 7221e29; new checks: independent second readings (StatementDeps), frozen `doc:`/`moduledoc:` entries, code-span decimals (`check_numbers.py`), `check_trusted_defs.py`. Table `runs/2026-11-04T0428Z/t5/RESULTS.md`. Open: STATE.md numbers and prose, fractions in FINDINGS.

- T5 blind round H (run 2026-11-04T1428Z): red team H (Sonnet, 8 defects against d714f04) all accepted by the checks on main; new: check_prose rule 6 (parameters: generalising words must name universally bound data; `bound`/`roles`/`fixed` in meaning.jsonl, equation-fixed parameters, registry `param_nouns.txt`, TRUST_MAP 'Fixed by the statement' column, packet line), rule 5 sign and per-headline citations (`citation_owners.txt`), rule 7 (module-doc numbers), guarded 'unchecked prose' banner in README/STATE; rule 6 blind on its class 3/4; after all fixes 1/8 (`runs/2026-11-04T1428Z/t5/RESULTS.md`).

## Rigorous simulation (THE RESULT part 1), `Work/Sim/` (run 2026-11-04T0628Z)
- Tools `ODETools.lean` (`evalQ`, `dEvalQ`, `hasDerivAt_evalQ`, `abs_evalQ_le`, `evalQ_ge`, `evalQ_le`, `gronwallBound_le_cell`): PROVED (Work).
- `DuffingCell.lean` (`lip_box`, `in_box`, `right_of_Icc`, one-cell Grönwall step): PROVED (Work). `DuffingCerts.lean` (24 generated steps): PROVED (Work).
- `DuffingExists.lean` (clamped Hamiltonian field, Picard–Lindelöf, exact invariant): PROVED (Work).
- `Duffing.lean`: core theorem for one-sided solutions, `duffing_first_zero`, `duffing_exists`: PROVED (Work), frozen 3cf671f. `DuffingAudit.lean`: blind closed, spec met.
- Promotion to Checked (run 0628Z): `Checked/Sim/`, `IsDuffingSolution` pinned; PROVED (CI 41795488679).
- Run 2026-11-04T0828Z: `Validated.lean` (`tube_cell`: confinement by the enclosure, continuous induction, any normed space): PROVED (Work). `MMCell.lean` (reduced Michaelis–Menten field, `lip_box`, cell step for any field equal to it on the box, `lower_of`/`upper_of`), generated `MMCerts.lean` (57 steps) and `MMEnclose.lean` (chaining): PROVED (Work). `MichaelisMenten.lean`: `mm_half_conversion`, `mm_solution_exists` (clamped field + same enclosure): PROVED (Work), frozen f764635. `MMAudit.lean`: blind closed, spec met. Checked copies on branch `wip/mm-checked`.
- Michaelis–Menten promotion: PROVED (main CI 41813186514, read run 1028Z).
- Run 2026-11-06T0428Z: logarithmic-norm cell step `OneSided.lean` (`onesided_cell`: weighted 2-D norm, touching-point comparison) and Robertson (`RobCell.lean`, generated `RobCerts{0..4}.lean`, `RobExists.lean`, `Robertson.lean`): PROVED (Work), blind closed (`RobAudit.lean`), spec + pin (`RobPin.lean`).
- Run 2026-11-06T0628Z: Robertson promoted (`Checked/Sim/{OneSided,RobCell,RobCerts0..4,RobExists,Robertson,RobPin}.lean`, `Checked/Fidelity/RobSpec.lean`, `Checked/Trust/SecondReadingRob.lean`); per-cell weight `Work/Sim/RobCellD.lean` (`cellD`, `stepD`, `weight_down`).
- Next node: shear-weight cell step (weight d²e₂² + (e₃ + c e₂)², μ ≈ −2/t) and Robertson at t = 10¹¹; n-dimensional one-sided step; generator for arbitrary polynomial fields.

## Data claims (THE RESULT part 1, "test suites"), `Checked/Data/` (run 2026-11-04T1628Z)
- `FR13Tools.lean`: generic over any H(z) table: closed form of the H₀-marginalised χ² (Gaussian integral), √ bounds without certificates, log comparison, group lemma. `FR13Certs.lean`, `FR13ValCerts.lean`: generated (`runs/2026-11-04T1628Z/scripts/gen_fr13.py`). `FR13Val.lean`: continuity, value and log bounds. `FR13.lean`: the eight headlines. PROVED (Work 8a6faf3; Checked: STATE).
- `Work/Data/FR13Audit.lean` (+ `FR13GapCerts.lean`, `gen_gap.py`): blind restatement closed. `Work/Data/FR13Transcription.lean`: second reading agrees.
- Next node: bridge to pinned `hubble`/`redshift` (`IsFlatLCDM`); profile-likelihood intervals; a second, larger data set.

## Chemistry: Redlich–Kwong coexistence, `Checked/Chemistry/RK*.lean` (run 2026-11-04T1828Z)
- `RKReduced.lean`: reduced isotherm g θ x = θ/(x−1) − 1/(x²+x), primitive ψ, critical-point quartic q θ (linear in θ), `reduced_window` for every θ in a rational interval; generated certificates (`runs/2026-11-04T1828Z/scripts/gen_rk.py`); `rk_unique_core` (θ and P_c from the critical point via `CubicEOS.reduced`, √0.7 and x_c enclosed).
- `RKExists.lean`: equal maxima on liquid [1.1, 1.5] and gas [60, 110] windows, IVT (`gen_rk_exists.py`). `RKAcentric.lean`: the two headlines.
- `Work/Chemistry/RKAcentricAudit.lean`: blind restatement closed.
- Next node: SRK/PR with Soave's κ(ω) on the same template (two α parameters enclosed instead of one).

## Mathematics: Lane–Emden n = 3 constants, `Work/Math/` (run 2026-11-05T0028Z)
- `LEStart.lean`: singular start (comparison from the singular end, `bound_from_zero`; continuous induction), interface `start`.
- `LECell.lean`: time-dependent tube cell (`tube_cell_t`), Lipschitz bound on a slab, Lane–Emden cell step. `LECerts.lean` (start instance), `LECerts1–3.lean` (90 cells, generated by `runs/2026-11-05T0028Z/scripts/emit_le.py` from `gen_le.py`), `LEChain.lean` (`chain`).
- `LaneEmden.lean`: `core` on [0, 69/10] and the frozen headline. `LaneEmdenBlind.lean` + `LEBlindBridge.lean`: blind restatement closed.
- `LEExistsLeft.lean` (Volterra fixed point on [0, 1/2]), `LEExistsRight.lean` (Picard–Lindelöf on [1/2, 7], clamped energy), `LEExists.lean` (`glue`, `exists_solution`); `LaneEmdenAudit.lean` (blind closure against Checked, non-vacuity).
- Promoted (run 2026-11-05T0228Z) to `Checked/Math/` (same module names, namespace `Checked.Math`), by `runs/2026-11-05T0228Z/scripts/promote_le.py`.
- Next node: uniqueness (Grönwall on the Volterra form); n = 3/2, Bonnor–Ebert on the same machinery.

## Data claims: Moresco et al. 2016 Table 5, `Work/Data/` (run 2026-11-05T0428Z)
- `Moresco16.lean`: `m16Table` (Table 4, PRINTED), `e2OL`, `chiSqOL`, `chiSqLine`; helpers `term_bound`, `log31_lt`, `log35_lt`; frozen `table5_{oL,pw,line}_inconsistent`, `oL_bic_exceeds`, `line_bic_exceeds`.
- `Moresco16Certs.lean`: generic step `term_le` (√y within ε of s ⇒ bound on (c√y − d)²/σ²) and certificate vectors (`runs/2026-11-05T0428Z/scripts/gen_m16.py`). `Moresco16Blind.lean` (Sonnet) + `Moresco16BlindClosed.lean`: blind restatement closed.

## Mathematics audit: `Work/Math/LaneEmdenNearMiss.lean` (run 2026-11-05T0428Z)
- `near_miss_initial` (scaling symmetry of the n = 3 equation applied to `Checked.Math.LEExists.exists_solution`), `mutant_n5` (θ5 = (1 + ξ²/3)^(−1/2)), `mutant_n1` (sinc; right derivative at 0 from `sin_lt`, `sin_gt_sub_cube`; φ continuity from `sin_bound`, `cos_bound`).


## Part 2: certified minimum of a fit statistic, `Work/Data/Moresco16Min*.lean` (run 2026-11-05T0628Z)
- `Moresco16MinTools.lean`: `Lf`, `alf`, `gam` (tangent bound of β, α, γ of the H₀-quadratic), `ge_of_point`, `box_bound` (corners ⇒ box), ℚ mirrors `tQ`, `LfQ`, `alfQ`, `gamQ` with cast bridges, `BoxOK` (decidable), `box_boundQ` (closes a box from `decide +kernel`).
- `Moresco16MinCerts0–3.lean` (leaves), `Moresco16MinCover.lean` (bisection tree, root `n` on [−1, 1] × [0, 4]): generated by `runs/2026-11-05T0628Z/scripts/emit_min.py` from `gen_min.py`'s tree.
- `Moresco16Min.lean`: the five frozen headlines. `Moresco16MinBlind.lean` (Sonnet) + `Moresco16MinBlindClosed.lean`: blind restatement closed.

## Part 3: definition labels with evidence, `Checked/Trust/{SecondFormulation,SecondFormulationCosmo,Formulations,FormulationsCond}.lean` (run 2026-11-05T0828Z)
- `SecondFormulation.lean` (blind, chemistry/data), `SecondFormulationCosmo.lean` (blind, sympy-derived series coefficients; uses `SecondReading.D1…`, `P0…Q3`): copied verbatim from `runs/2026-11-05T0828Z/blind/`.
- `Formulations.lean`: `agree_<name> : @program = @SecondFormulation.<name>` for 20 definitions (generated, `runs/2026-11-05T0828Z/scripts/gen_formulations.py`); `FormulationsCond.agree_margChiSq_pos` (σ > 0 only).
- Rules in `scripts/trust/StatementDeps.lean` (labels FORMULA/MATH/WITNESS/PRINTED need agreements or baseline; COMPOSITE/CLAIM structural; SPEC used by a pin; label whitelist), baseline guard `scripts/trust/check_formulas.py`, baseline `scripts/trust/formula_baseline.txt`; CLAIMS.md wording in `scripts/trust/Claims.lean` (`explain`).

## Moresco 2016 in Checked, `Checked/Data/Moresco16*.lean`, `Checked/Trust/*M16.lean` (run 2026-11-05T1028Z)
- `Moresco16Certs`, `Moresco16`, `Moresco16Lower`, `Moresco16MinTools`, `Moresco16MinCerts0–3`, `Moresco16MinCover`, `Moresco16Min`: the Work modules of runs 0428Z/0628Z, copied by `runs/2026-11-05T1028Z/scripts/promote_m16.py` (namespace Checked.Data, specific imports), module docs by `moddocs_m16.py`.
- `SecondReadingM16` (blind restater's table), `TranscriptionsM16.agree_m16Table`; `SecondFormulationM16` (blind, brief `runs/2026-11-05T1028Z/blind/briefM.md`), `FormulationsM16.agree_{e2OL,chiSqOL,chiSqLine}`.
- `Work/Data/Moresco16PromotionAudit.lean`: Work = Checked definitions (rfl); blind claims from the Checked headline.

## Peng–Robinson at ω = 1, `Checked/Chemistry/PR{Reduced,Core,Exists,Acentric}.lean` (run 2026-11-05T1228Z)
- `PRReduced`: reduced isotherm g θ x = θ/(x−1) − 1/(x²+2x−1), primitive ψ with (√2/4)(log(x+1+√2) − log(x+1−√2)), sign polynomial q; generated from `RKReduced` by `runs/2026-11-05T1228Z/scripts/emit_pr.py` (certificates `gen_pr.py`); `window_of_maxwell`.
- `PRCore`: θ_c = (x−1)²(2x+2)/(x²+2x−1)², Soave factor, p_s/P_c = π_s·α·(x²+2x−1)²/(x²−2x−1), certified logs; `pr_unique_core`.
- `PRExists`: from `RKExists` (`emit_pr_exists.py`); `theta_bounds`, `pr_exists_core`.
- `PRAcentric`: headlines `pr_omega1_unique`, `pr_omega1_exists`. Audit `Work/Chemistry/PRAcentricAudit.lean`.

## Peng–Robinson with the revised (1978) κ at ω = 1, `Checked/Chemistry/PR78{Reduced,Core,Exists,Acentric}.lean` (run 2026-11-05T1828Z)
- Same route as the 1228Z PR modules, regenerated for κ(1) = 1716915/10⁶ by `runs/2026-11-05T1828Z/scripts/` (gen_pr78.py, emit_pr78*.py); promoted by `promote_pr78.py`.
- `PR78Acentric`: headlines `pr78_omega1_unique`, `pr78_omega1_exists`. Audit `Work/Chemistry/PR78AcentricAudit.lean`. Work-only sibling `Work/Chemistry/PRCantera{Reduced,Core,Exists,Acentric}.lean` (Cantera coded κ; candidate C31).

## Soave–Redlich–Kwong with Soave's κ at ω = 1, `Checked/Chemistry/SRK{Reduced,Exists,Acentric}.lean` (run 2026-11-06T0028Z)
- `SRKReduced`: the RK isotherm and route (`RKReduced`) with certificates regenerated for θ = 0.7(3x − 9 − 9/x)/α, α = (1 + κ(1)(1 − √0.7))², κ(1) = 939/500 (`runs/2026-11-06T0028Z/scripts/gen_srk.py`, `emit_srk.py`); spinodal windows [7/5, 17/10], [19, 25]; `window_of_maxwell`; Soave-α core `srk_unique_core` (no sign of R or T_c assumed; `srk_core.lean.txt`).
- `SRKExists`: from `RKExists` (`emit_srk_exists.py`; windows [1.1, 1.4], [400, 1200]); `theta_bounds`, `srk_exists_core`.
- `SRKAcentric`: headlines `srk_omega1_unique`, `srk_omega1_exists`; promoted by `promote_srk.py`. Audit `Work/Chemistry/SRKAcentricAudit.lean`.
- Work-only sibling `Work/Chemistry/SRKGD{Reduced,Exists,Acentric}.lean` (Graboski–Daubert κ; 0.994), emitted by `variant.py variant_srkgd.json` from the SRK modules: any κ(1) whose spinodal windows and enclosures match SRK's is one config file.

## Second readings of source claims and the last baselined formulas, `Checked/Trust/` (run 2026-11-05T2028Z)
- `SecondReadingClaims{A,B,C}.lean`: blind readers' data (verbatim from `runs/2026-11-05T2028Z/second_reading_claims/`); `SecondReadingClaims.lean`: the 28 grandfathered CLAIMs and `dQFlat` with those data substituted (generated, `runs/2026-11-05T2028Z/scripts/gen_claim_readings.py`); `TranscriptionsClaims.lean`: 30 agreements.
- `SecondFormulation{D,E}.lean` (blind, briefs `runs/2026-11-05T2028Z/blind_formulation/brief{D,E}.md`); `Formulations{D,E}.lean`: `agree_{RoundsTo,coshBounce,eta20Of,eta30Of,Jfam,remA,correctR,margChiSq}`.
- `scripts/trust/claim_baseline.txt`, `formula_baseline.txt`: empty (headers only).

## Provenance of second versions, `scripts/trust/` (run 2026-11-05T2228Z)
- `check_provenance.py` (blocking): generated claim readings reproducible by `gen_claim_readings.py`; data-only substitution (token diff); no borrowed or aliased program constants in second versions; reader copy under `runs/` with a brief, committed first; `provenance_baseline.txt` (6, shrink-only).
- `StatementDeps.lean`: agreements of propositions without program theorems; CLAIMs with any inline arithmetic need a second reading.
- Part 3: blind round L, `runs/2026-11-05T2228Z/t5/RESULTS.md` (5/6 accepted before; 0/5 after, blind).

## Robertson at long horizons, `Work/Sim/{ChebBound,RobShear,RobLCerts*,RobLChain,RobExistsLong,RobLong,RobLongAudit}.lean` (run 2026-11-06T0828Z)
- `ChebBound`: `chebMono` (Clenshaw on ℚ lists), `scaleL`, `cheb_bound`, `cheb_range`, `bound_of_eq`, `range_of_eq` (kernel-checked list equalities via `decide +kernel`).
- `RobShear`: `Al`, `Be`, `Ga`, `Φ`, `CornerOK`, `Corners`, `shear_onesided`, `cellS`, `stepS`, `shear_switch`, `start_shear`, `shear_comp`, `exp_le_inv`.
- `RobLCerts{0..7}` (generated, 77 cells `stepL0`…`stepL76`), `RobLChain` (`chainL`, `finalL`), `RobExistsLong` (`exists_clamped_long`), `RobLong` (headlines `rob_state1e11`, `rob_printed_y3_low`, `rob_exists_1e11`), `RobLongBlind` + `RobLongAudit` (blind closure).

## Gelfand problem as a PDE, `Work/Math/{RadialLaplacian,GContFrom,GelfandODEBound,GelfandPDE,GelfandPDEBlind,GelfandPDEBlindClosed}.lean` (run 2026-11-06T1628Z)
- `RadialLaplacian`: `hasFDerivAt_norm` (x ≠ 0), `laplacian_radial` (Δ(f∘‖·‖)(x) = f'' + (finrank − 1)/‖x‖·f', any finite-dimensional real inner product space).
- `GContFrom`: `lipF'`, `normF'`, `contF'`, `exists_from` (Picard–Lindelöf for (w, s²φ) from any a > 0, clamps inactive by monotonicity).
- `GelfandODEBound`: `glue_at` (one-sided derivatives glued at any c), `ode_bound` (radial ODE on (0, 1) with f'(0) = 0, f(1) = 0 ⇒ λ ≤ 3.321992119 via `Checked.Math.Gelfand.gelfand_ball_critical`).
- `GelfandPDE`: headline `gelfand_pde_radial_bound`; `GelfandPDEBlindClosed`: `blind_closed`, `nonvacuous_zero`.
- `RadialC2`: `hasFDerivAt_zero_of_sq`, `IL`, `contDiffAt_zero_radial` (radial function C² at 0), `hasFDerivAt_radial_zero`, `laplacian_radial_zero` (Δ at 0 = n·L); `GProfile`: `profile_bounds` (centre bounds of any Gelfand solution); `GelfandPDEExists`: `contDiffOn_two_of_derivs`, headline `gelfand_pde_radial_exists`; `GelfandPDEExistsBlindClosed`: `blind_closed`, `bound_sharp`.

## Thomas–Fermi initial slope, `Work/Math/{TFCell,TFReduce,TFCerts*,TFChain,ThomasFermi,ThomasFermiBlind,ThomasFermiBlindClosed}.lean` (run 2026-11-06T1828Z)
- `TFCell`: `neg_left_of_deriv`, `nonneg_of_left`, `first_touch` (two functions positive at a, each with positive derivative wherever it vanishes while the other is ≥ 0, stay positive), `super_cell`, `sub_cell` (polynomial barriers for w' = tP/w, P' = 2w³), `hasDerivAt_evalQ_sub`, `continuous_evalQ_sub`, `cube_le`.
- `TFReduce` (from the headline's hypotheses): `phi_neg` (y' < 0 on [0, ∞)), `cont_W`, `cont_P`, `deriv_W`, `deriv_P` (t = √x, w = √y), `W_pos`, `W_zero`, `P_zero`, `zero_event` (small w with steep negative P forces a zero), `rpow_three_halves`.
- `TFCerts*`, `TFChain` (generated by `runs/2026-11-06T1828Z/scripts/emit_tf.py`): `sup_chain` (slope < −1.58807103 ⇒ w(27/4) < 13/625, P(27/4) < −771·10⁻⁷), `sup_event`, `sub_chain` (slope > −1.58807102 ⇒ P(15/2) > 0).
- `ThomasFermi`: headline `tf_initial_slope`; `ThomasFermiBlindClosed`: `deriv_near`, `blind_closed`.
- `TFExBase` (clamped field `F`, `g` = v^{3/2} extended by 0), `TFExFlow` (`lipschitz_F`, `norm_F_le`, `exists_flow`, `consistent`, `zero_backward`), `TFExEvents` (`phi_mono`, `excl`, `low_event`, `high_event`), `TFExConvert.convert` (t = √x back to x), `TFExAssemble.main` (shooting: supremum slope, positivity, decay), `ThomasFermiExists.tf_exists` (run 2026-11-06T2028Z; Work, and Checked copies on promotion).
- Part 3, closed-vocabulary paraphrases (run 2026-11-06T2228Z): `scripts/trust/check_claim_vocab.py` (V1 words ⊆ generated claim minus author names ∪ function words ∪ `scripts/trust/prose_vocab.txt`; V2 vocabulary without strength words; V3 baseline `claim_vocab_baseline.txt`; V4 vocabulary growth disclosed; V5 junk-value conclusions; V6 numerals), `scripts/trust/check_status_lines.py` (status lines name Checked headlines), goal guard LOCK rule. Blind rounds P, Q: `runs/2026-11-06T2228Z/t5/`.
