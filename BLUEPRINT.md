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
- Run 2026-11-08T2228Z: phrase roles, signs and names from blind readers — `scripts/trust/phrase_roles.txt` (copies of `runs/2026-11-08T2228Z/roles/ROLES.txt`, `names/NAMES.txt`), `check_claims.py` P3–P6, `scripts/trust/phrase_polar_baseline.txt` (shrink-only); round Z `runs/2026-11-08T2228Z/t5/`.
- Run 2026-11-09T0228Z: phrases generated from blind texts — clause reader `runs/2026-11-09T0228Z/clauses/CLAUSES.txt`, letter reader `symbols/SYMBOLS.txt` (copied into `scripts/trust/phrase_roles.txt`), exclusions `scripts/trust/phrase_clause_baseline.txt` (shrink-only), generator `runs/2026-11-09T0228Z/scripts/gen_phrases.py`; `check_claims.py` P7 `coverage` (`p7_tokens`, `_match`, `_verb_ok`, `registry_names`), P8 `registry_complete`, `registry_removals`, P9 `clause_baseline`; judge `runs/2026-11-09T0228Z/t5/judge_AA.py`.

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

## Gelfand problem as a PDE in Checked, `Checked/Math/{RadialLaplacian,GContFrom,GelfandODEBound,GelfandPDE,RadialC2,GProfile,GelfandPDEExists}.lean` (run 2026-11-07T0028Z)
- Copies of the Work modules of run 2026-11-06T1628Z (`runs/2026-11-07T0028Z/scripts/promote_gpde.py`): `RadialLaplacian.laplacian_radial`, `GContFrom.exists_from`, `GelfandODEBound.ode_bound`, `RadialC2.contDiffAt_zero_radial`, `GProfile.profile_bounds`; headlines `gelfand_pde_radial_bound`, `gelfand_pde_radial_exists`. Reader constants `Checked/Trust/SecondReadingGelfandPDE.lean` (gelfandPdeSpace, gelfandPdeBall, gelfandPdeClosedBall, gelfandPdeRegular, gelfandPdeContinuous, gelfandPdeLamRange).
- Part 3: `check_claim_vocab.py` V7 (quantifier kind order and binder scope), V8 (strength words in headline names).

## Townes soliton shooting bracket, `Work/Townes/{TStart,TCell,TCertsA*,TCertsB*,TChainA,TChainB,TownesShooting,TownesBlind,TownesBlindClosed}.lean` (run 2026-11-07T0228Z)
- `TStart`: `g_sub_le` (|(a − a³) − (b − b³)| ≤ (1 + 3(M + η)²)|a − b|), `core`, `start` (every solution with θ(0) = c₀ stays within r²/4·(Lη + R) of a polynomial reference whose residual (rq)' − r(p − p³) is ≤ rR, closed by continuous induction while r₀²L/4 < 1).
- `TCell`: field `tF`, `lip_slab` (K ≥ 1/t₀ + 1 + 3TH²), `cell` (one Grönwall step via `Work.Math.LECell.tube_cell_t`, defect (t₀+σ)p_φ' + p_φ − (t₀+σ)(p_θ − p_θ³) without division), `lower_of`, `upper_of`.
- `TCertsA*`/`TChainA` (θ(0) = 2.2062008646, θ > 0 invariant, φ(68/5) > 0) and `TCertsB*`/`TChainB` (θ(0) = 2.2062008647, φ < 0 invariant, θ(68/5) < 0), generated by `runs/2026-11-07T0228Z/scripts/emit_townes.py` from `gen_townes.py`: `startI`, `step0`–`step122`, `chain`.
- `TownesShooting`: headlines `townes_under`, `townes_over`; `TownesBlindClosed`: `left_end`, `right_end` (one-sided end derivatives from a continuous derivative), `hyps`, `blind_under`, `blind_over`.

## The judge's tooling, `scripts/ci_changes.py`, `scripts/nanoda_shard.sh`, `scripts/nanoda/ShardMain.lean` (run 2026-11-07T0428Z)
- `ci_changes.py`: base of every base-diff check = newest ancestor with a fully green run (Actions API, fail-closed); `lock_only`; `checked_hash` (memo key of the nanoda shards). `--selftest` runs in CI.
- `ShardMain.lean`: lean4export driver (built inside the pinned v4.35.0 clone) exporting shard i of k of the default constant list by module hash; `nanoda_shard.sh` = `nanoda_checked.sh` with that export. Partition tested on `Checked.Math.TFCell`, k = 2.

## Townes ground state existence, `Work/Townes/{TExLeft,TExFlow,TExLimit,TExAssemble,TownesExists,TownesExistsBlind,TownesExistsBlindClosed}.lean` (run 2026-11-07T0628Z)
- `TExLeft`: clamp `cl` to [−3, 3], `g y = cl y − cl y³`, kernel `Real.negMulLog`; `Tmap c` on `BoundedContinuousFunction (Icc 0 (1/5)) ℝ`, `contracting` (13/25), `θL`, `φL`, `A`, `B`, `J_subst`, `deriv_θL`, `deriv_φL`, `θL_lip`, `φL_lip`; `left` (the singular start for every c ∈ [2.2, 2.21], Lipschitz in c with K = 6).
- `TExFlow`: field `F t p = (cl 5 φ, −cl 5 φ / max t (1/5) + h(cl 3 θ))`, `lipF`, `normF`, `exists_flow` (Picard–Lindelöf from t = 1/5, Lipschitz in the initial state), `consistent`, `equilibrium_backward`, `F_zero`, `F_one`, `F_eq`; clamped energy `Ψ`, `W`, `start_energy`, `bounds` (clamps inactive from |θ| ≤ 5/2, |φ| ≤ 3).
- `TExLimit`: `right_lt`, `right_gt`, `left_gt` (local sign from a derivative), `pos_neg` (no event ⇒ θ > 0, φ < 0 on (0, ∞)), `limit` (… and θ → 0).
- `TExAssemble`: `glue` (one-sided derivatives at 1/5), `pos_near` (a positive event on a compact window persists under uniform Lipschitz dependence), `flow`, `core` (the existence theorem from the two shooting statements as hypotheses).
- `TownesExists`: headline `townes_exists` = `core townes_under townes_over`. `TownesExistsBlindClosed`: `of_program` (the frozen conclusion ⇒ the blind `IsRadialProfile` via the even extension), `closed`.
- `TownesSolutions`: `ivp_exists` (for every c ∈ [2.2, 2.21] and S > 1/5 a pair θ, φ satisfying every hypothesis of `townes_under`/`townes_over` with θ(0) = c: the non-vacuity witness for their promotion).
- `Work/Sim/QPoly.lean` (run 2026-11-07T0828Z): `qadd`, `qsmul`, `qsub`, `qmul`, `qderiv`, `qeval`, `qabs`; `evalQ_qadd`, `evalQ_qsmul`, `evalQ_qsub`, `evalQ_qmul`, `dEvalQ_eq`, `qeval_cast`, `abs_le_qabs`, `lower_q`, `upper_q`, `evalQ_zero_head`.
- `Work/Townes/TCellQ.lean`: `Cell`, `defect2`, `CellProp`/`cellOK`, `cellOK_basic`, `defect2_eval`, `cell_q`, `linkOK`, `posOK`, `negOK`, `chainTo`, `endOK`, `chainOK`, `segOK`, `chainTo_head`, `cell_facts`, `abs_link`, `chain_gen`, `chain_q`, `seg_q`; `Start`, `startRes`, `startC`, `StartProp`, `shootOK`, `evalQ_cons_zero_head`, `start_q`, `shoot_q`; `icc_glue`, `ioc_glue`. `TQDataA`/`TQDataB`: `start`, cells `c0`–`c122`, `start_ok`, `seg0_ok`–`seg4_ok`, `chain`.
- `Work/Townes/TownesPromotionAudit.lean`: `blind_under`, `blind_over`, `blind_exists` (from the Checked headlines; branch).

## Kernel-evaluated chains in Checked, `Checked/Math/{TFCellQ,TFQData,LECellQ,LEQData,LELast,GCellQ,GQData}.lean` (run 2026-11-07T1028Z)
- `TFCellQ`: `BCell` (t0, h, qw, qp), `d1`, `d2` (computed defects of the two barrier inequalities), `lo`, `hi`, `SupProp`, `SubProp`, `d1_eval`, `d2_eval`, `lo_le`, `le_hi`, `TFSol` (the hypotheses on (w, P) as one structure), `sup_q`, `sub_q`, `supLink`, `subLink`, `supChain`, `subChain`, `sup_chain_q`, `sub_chain_q`, `sup_seg_q`, `sub_seg_q`, `supEnd`, `subEnd`, `sup_end_q`, `sub_end_q`. `TFQData`: cells `u0–u53`, `l0–l59`, `useg0–5_ok`, `lseg0–5_ok`. `TFChain`: `sup_chain`, `sup_event`, `sub_chain` (statements as before).
- `LECellQ`: the Townes `TCellQ` chain layer for `LECell.cell` (`Cell`, `defect2`, `CellProp`, `cell_q`, `cell_facts`, `linkOK`, `chainTo`, `chain_gen`, `chain_q`, `seg_q`, `icc_glue`, `ioc_glue`). `LEQData`: `c0–c89`, `seg0–5_ok`, `c0_t0 …`, `c89_t0 …`. `LELast`: `step89`, `lastFacts` (verbatim). `LEChain.chain` (statement as before).
- `GCellQ`: `Cell` (with EH, PH), `defect1`, `defect2`, `invA`, `invB`, `CellProp`, `InvProp`, `Inv`, `cellOK`, `cell_q`, `cell_facts`, `linkOK`, `chainTo`, `endOK`, `chain_gen`, `seg_q`, `end_q`, `icc_glue`, `ioc_glue`. `GQData`: `c0–c91`, `seg0–6_ok`, `last_ok`. `GChain.chain` (statement as before).
- Converters `runs/2026-11-07T1028Z/scripts/conv_{tf,le,g}.py`, installer `install_tf.py`; old modules in `_archive/Checked/Math/`.

## Blasius boundary layer, `Work/Blasius/` (run 2026-11-07T1228Z)
- `Blasius.lean`: `blasius_wall_shear` (frozen 4db71de). `BlasiusExists.lean`: `blasius_exists` (frozen 4db71de). `BlasiusBlind.lean` (verbatim blind file), `BlasiusBlindClosed.lean`: `wall_shear_bounds`; `BlasiusExistsBlindClosed.lean`: `exists_blasius_solution`.
- `BTail.lean`: `IsSol`, `at_pos`, `contOn`, `lip_lin`, `bound_on`, `zero_back`, `zero_fwd`, `q_pos`, `q_neg`, `shear_pos`, `scale`, `tail`.
- `BCell.lean`: `blF`, `slab`, `lip_slab`, `cell` (3-D `tube_cell_t` step). `BCellQ.lean`: `Cell`, `defect3`, `CellProp`, `cellOK`, `cell_q`, `Sol`, `InBox`, `AtEnd`, `linkOK`, `chainTo`, `link_box`, `chain_gen`, `seg_q`, `endOK`, `end_q`, `chainTo_head`, `seg_q0`, `end_q0`. `BQData.lean` (generated): `c0–c287`, `seg0–47_ok`, `FG`, `FP`, `FQ`, `R`, `chain`.
- `BExBase.lean`: `cl`, `vF`, `cl_of_abs_le`. `BExFlow.lean`: `exists_flow` (Picard–Lindelöf on [0, n], glued). `BExBounds.lean`: `inactive` (clamps inactive, true system, monotone limit).
- Generator `runs/2026-11-07T1228Z/scripts/gen_blasius.py`, emitter `emit_blasius.py`, float study `blasius_float.py`.
- Promoted run 2026-11-07T1428Z: the same modules under `Checked/Blasius/` (namespace `Checked.Blasius…`), headlines `Checked.Blasius.blasius_wall_shear`, `Checked.Blasius.blasius_exists`; reading `Checked/Trust/SecondReadingBlasius.lean` (`blasiusRhs`, `blasiusHalfLineTyped`, `blasiusHalfLine`, `blasiusWall`, `blasiusEdge`, `blasiusShear`); NV witness in `Checked/Trust/Witnesses.lean`; promotion script `runs/2026-11-07T1428Z/scripts/promote_blasius.py`.

## Trust checks: controls (run 2026-11-07T1428Z)
- `scripts/trust/controls/prose_rule_controls.py`: `section`, `run_vocab`, `CASES` (V1, V6–V11 positive and clean controls), S2 controls; called first by `check_claim_vocab.main` and `check_status_lines.main`.
- `check_claim_vocab.py`: `unpinned_names` (V9), `bound_numerals`/`BIND`/`NUMWORD` (V10), `quoted_spans` (V11), `name_strength` (V8, heading excluded). `check_status_lines.py`: `NARROW`, `s2_words` (S2).

## Defect identities by kernel evaluation, `Checked/Sim/{QResid,QResidRob}.lean` (run 2026-11-07T1628Z)
- `QResid`: `allZero`, `evalQ_of_allZero`, `evalQ_eq_of_allZero`, `qscale`, `evalQ_qscale`; oscillator cells `dufA`, `dufB`, `duf_a`, `duf_b`; enzyme-kinetics cells `mmA`, `mmB`, `mm_a`, `mm_b`, `mm_sum`. `QResidRob`: `robA`, `robB`, `evalQ_robA`, `evalQ_robB`, `rob_a`, `rob_b`, `rob_a_s`, `rob_b_s` (rescaled variable u/R).
- Used by `Checked/Sim/{DuffingCerts,MMCerts,RobCerts0–4,RobLCerts0–7}.lean` (converter `runs/2026-11-07T1628Z/scripts/conv_ring.py`; statements unchanged).

## Weighted one-sided cells, `Work/Sim/OneSided3.lean`, `Work/Blasius/{BCellW,BWData}.lean` → `Checked/…` (run 2026-11-07T1628Z)
- `OneSided3`: `onesided3_cell` (three-component logarithmic-norm cell step in the norm w1·e1² + w2·e2² + e3²), `quad3_nonneg` (Sylvester/LDL for a symmetric 3×3 form), `wnorm_add` (weighted triangle inequality).
- `BCellW`: `Cell` (t0, h, δ, ε, B, μ, w1, w2, r1, pg, pp, pq), `defect3`, `det3`, `psdOK`, `mlo`, `qlo`, `qhi`, `CellProp`, `cellOK`, `cellOK_basic`, `defect3_eval`, `Sol`, `Sol.mono`, `V`, `InBox`, `AtEnd`, `exp_le_inv'`, `comp_le`, `os_blasius` (one-sided bound of the Blasius field from two Sylvester checks), `quad_of_psd`, `cell_w`, `Vq`, `linkOK`, `chainTo`, `link_box`, `chain_gen`, `seg_q`, `endOK`, `abs_link`, `end_q`, `chainTo_head`, `seg_q0`, `end_q0`.
- `BWData`: `c0–c35`, `seg0–5_ok`, `FG`, `FP`, `FQ`, `R` (same values as the archived `BQData`), `chain` (same statement). Generator `runs/2026-11-07T1628Z/scripts/gen_blasius_w.py` (args `9 4 24 19 1 10`), emitter `emit_blasius_w.py`, promotion `promote_bw.py`, float study `bl_study.py`; old `Checked/Blasius/BQData.lean` in `_archive/Checked/Blasius/`.

## Hiemenz stagnation-point flow (Falkner–Skan β = 1), `Work/Hiemenz/` (run 2026-11-07T2028Z)
- `Hiemenz.lean`: `hiemenz_under`, `hiemenz_over`, `hiemenz_exists` (frozen 41967e1). `HiemenzBlind.lean` (verbatim blind file), `HiemenzBlindClosed.lean`: `under_closed`, `over_closed`, `exists_closed`.
- Promoted (run 2026-11-07T2228Z, 5556e24) to `Checked/Hiemenz/` (same eleven modules, `runs/2026-11-07T2228Z/scripts/promote_hiemenz.py`) plus `HIVP.lean` (`box_spec`, `HUDataC.boxC`, `HODataC.boxC`, `ivp_lo`, `ivp_hi`: IVP solutions on [0, 15/2] for the NV witnesses); literal reading `Checked/Trust/SecondReadingHiemenz.lean`.
- `HCellW.lean`: weighted one-sided cells for (p, q, −g q − 1 + p²): `Cell` (… r1, r2 …), `defect3`, `psdOK` (μ, w1, w2, m, P3, s), `plo`, `phi`, `CellProp` (four Sylvester corners), `qf`, `os_hiemenz`, `quad_of_psd`, `cell_all` (whole-cell enclosure), `cell_w`, `sideU`/`sideO` + `_spec` (p < 1 / q > 0 on a cell), `chainS` (chain with a per-cell side condition), `chainS_gen`, `segS_q0`, `endU`, `endO`, `endS_q0`, `endSO_q0`. `HUData`, `HOData`: 60 cells each, `chain`.
- Existence: `HExBase.lean` (`cl`, `vH` clamped field, `Under`, `Over`, `not_under_and_over`); `HExFlow.lean` (`exists_sol`, `flow`, `flow_zero`, `flow_deriv`, `unique_left`, `unique_right`, `flow_cont`); `HCellWC.lean` (HCellW for the clamped field `SolC`, six box conditions per cell, `onesided3_cell_t`); `HUDataC`, `HODataC` (`chainC`: `Under`/`Over` of every clamped trajectory from the two start values); `HExLimit.lean` (`no_event`); `HExAssemble.lean` (`under_open`, `over_open`, `under_lo`, `over_hi`, `exists_bvp`).
- Generators `runs/2026-11-07T2028Z/scripts/gen_hiemenz_w.py` (args `A 15/2 8 12 20 1/2 2 under|over`), `gen_hiemenz_wc.py`, emitters `emit_hiemenz_w.py`, `emit_hiemenz_wc.py`, float study `hz_fast.py`.

## Certified-number selectors, `scripts/trust/StatementDeps.lean` + `scripts/trust/check_numbers.py` (run 2026-11-08T0028Z)
- StatementDeps: `letBinds`, `roundsSel` (selector of `x` in `RoundsTo x d k`: `@Def`, numeral arguments by binder, `let` arguments), `posRoundsToSels`, `posRoundsToXs` (pretty-printed quantity); `ratLits` reads `let` values. `.lake/records_numbers.tsv` columns: record, value, selector, quantity.
- check_numbers: `parse_sel_tsv`, `parse_sel_tag`, `check_text` (S1–S4, P1–P2), `generated_table` / `--write`, `selftest` (11 controls), shrink-only `scripts/trust/records_selector_baseline.txt`.

## Lane–Emden of any integer index; index 2, `Checked/Math/LEN*.lean`, `Checked/Math/LE2*.lean` (run 2026-11-08T0228Z)
- Generic in n: `LENStart.pow_sub_le_of`, `LENStart.start n`; `LENCell.leF n`, `pow_sub_le_slab`, `lip_slab n`, `cell n`; `LENCellQ.qpow`, `evalQ_qpow`, `defect2 n`, `CellProp n`, `cellOK`, `chainTo`, `segOK n`, `cell_q`, `chain_gen`, `seg_q n`.
- Index 2: `LE2Start.startI`, `LE2QData` (cells, `seg0_ok`–`seg4_ok`), `LE2Last.stepL`, `lastFacts`, `LE2Chain.chain`, `LaneEmden2.core`, headline `laneEmden2_constants`; existence `LE2ExistsLeft` (fixed point, clamped square), `LE2ExistsStart`, `LE2ExistsCell` (clamped field `Fc`, `cellC`, `boxOK`, `chainC`), `LE2ExistsData`, `LE2Exists.exists_solution`.
- Generators: `runs/2026-11-08T0228Z/scripts/gen_len.py <n>` (window table `WIN`), `emit_len.py <n> <T_num> <T_den> <ω_lo> <ω_hi>`, `gen_exists.py`, `promote_le2.py`. Audit: `Work/Math/LaneEmden2BlindClosed.lean`; reader `Checked/Trust/SecondReadingLE2.lean`.

## Homann axisymmetric stagnation-point flow, `Work/Homann/`, `Checked/Homann/` (run 2026-11-08T0428Z)
- Cells: `HmCellW` (`defect3` with 2·pg·pq, `os_homann`, `CellProp` with `psdOK` at 2·mlo and the doubled q-corners, `cell_all`, `sideU_spec`/`sideO_spec`, `chainS`, `segS_q0`, `endS_q0`, `endSO_q0`); data `HmUData.chain`, `HmOData.chain` (96 cells, 12 segments each).
- Existence: `HmExBase` (clamped field `vH`, `Under`, `Over`), `HmExFlow` (`lip` with 2T + 12, `norm_le` 4T + 13, `flow`, `flow_cont`), `HmExLimit.no_event`, `HmCellWC` + `HmUDataC.chainC`/`HmODataC.chainC`, `HmExAssemble.exists_bvp`; headlines `Homann.homann_under`, `homann_over`, `homann_exists`; NV helper `HmIVP` (`boxC`, `solves`, `ivp_lo`, `ivp_hi`).
- Generators: `runs/2026-11-08T0428Z/scripts/gen_homann_w.py`, `gen_homann_wc.py`, `emit_homann_w.py`, `emit_homann_wc.py`, `port_homann.py`, `promote_homann.py`, `emit_hmivp.py`. Audit: `Work/Homann/HomannBlindClosed.lean`; reader `Checked/Trust/SecondReadingHomann.lean`.

## Roles of certified numbers, `scripts/trust/check_numbers.py` + `Checked/Records/Findings.lean` (run 2026-11-08T0628Z)
- check_numbers: `load_kinds`, `_tokens`/`_parse`/`_outer` (outermost program definitions of a pretty-printed quantity), `role_of` (printed / derived / free / difference(A−B)), `head_of` and `SYMBOLS` (R4; guarded by the frozen phrases of `decel`, `cosmoCoeff`), rules R0–R4 in `check_text`, role selector items (`(printed)`, `(derived)`, `(difference)`) in S1/S2, role column of the generated table; `selftest` 22 controls. `--base` compares certified pairs without role items.
- Records: `Checked.Records.printedAvilesL0`, `printedCLSL0` (PRINTED); agreements `Checked/Trust/TranscriptionsRecords.lean` (`agree_printedAvilesL0`, `agree_printedCLSL0`, with the blind readings of run 2026-11-05T2028Z). `F9_values` through `FRCosmo.P0/Q0/printedR/correctR`, `FREta.qL/jL/sL/lL`.
- check_literals (a1): a negative RoundsTo value `(-d)` is a target. Migration script `runs/2026-11-08T0628Z/scripts_add_roles.py`; replay `runs/2026-11-08T0628Z/replay/make_defects.py`.
- Run 2026-11-12T1028Z: `Checked/Records/FalknerSkan.lean` (`F12_separation`, `F13_wall_shear`, `F14_reversed_wall_shear`): a record over an ODE solution is a corollary of the window headline with the hypotheses copied verbatim (same literal readings, same NV witness, same necessity profiles: `Checked/Trust/NecessityN.lean` reuses NecessityE's three for F12); an existence record carries the conditions in its conclusion (no hypotheses). Value role `free` (`q 0`, `β` are bound variables).

## Falkner–Skan table rows by similarity scaling, `Work/FalknerSkan/`, `Checked/FalknerSkan/` (run 2026-11-08T0828Z)
- `FSScale.scale` (for c > 0: (f, p, q) solving f' = p, p' = q, q' = −a f q − b(1 − p²) within Ici 0 ↦ (c f(·/c), p(·/c), q(·/c)/c) solving it with a/c², b/c²), `FSScale.scale_lim`, rational √2 bounds `sqrt2_lt`, `lt_sqrt2`, `sqrt2_le'`, `le_sqrt2'`.
- Headlines `FalknerSkan.fs_half_exists` (from `Checked.Homann.homann_exists`, c = √2), `fs_zero_wall_shear` (from `Checked.Blasius.blasius_wall_shear`, c = √2). NV witness of `fs_zero_wall_shear`: `blasius_exists` rescaled with c = √(1/2).
- Bounded class (run 2026-11-08T1628Z): `HalfBounded.fs_half_bounded_window`, `fs_half_bounded_equal`, `fs_half_exists_bounded` from `Bounded.homann_*` by `FSScale.scale` (c = 1/√2; existence c = √2); audit `Work/FalknerSkan/HBBlindClosed.lean`, referee `runs/2026-11-08T1628Z/referee_fshalf.md`; script `runs/2026-11-08T1628Z/scripts/promote_hb.py`.
- Scripts: `runs/2026-11-08T0828Z/scripts/promote_fs.py`. Audit: `Work/FalknerSkan/FSBlindClosed.lean`; reader `Checked/Trust/SecondReadingFalknerSkan.lean`; referee `runs/2026-11-08T0828Z/referee_fs.md`.

## Monotone solutions of stagnation-point flows (Crocco comparison), `Work/FalknerSkan/`, `Checked/FalknerSkan/`, `Checked/{Hiemenz,Homann}/*ExMono.lean` (run 2026-11-08T1028Z)
- `CroccoMap.crocco` (q > 0 on [0, E): inverse ψ of p, z = q ∘ ψ, F = f ∘ ψ with dF/dt = t/z, dz/dt = −kF − (1 − t²)/z inside (0, p E)); `CroccoCompare.compare` (k ≥ 0, range ≤ 1: z₂ − z₁ ≥ z₂(0) − z₁(0)); `CroccoWindow.smono_Icc`, `smono_Ici`, `p_lt_one`, `exists_q_lt`, `le_of_over`, `ge_of_under` (generic in k ≥ 0).
- Headlines `MonotoneWindow.hiemenz_monotone_window`, `homann_monotone_window` (f'' > 0 ⇒ wall shear in the window; against `HIVP.ivp_lo/hi`, `HmIVP.ivp_lo/hi` and the shooting theorems), `MonotoneExists.hiemenz_exists_monotone`, `homann_exists_monotone` (from `HExMono.exists_bvp_pos` / `HmExMono.exists_bvp_pos`: the shooting construction with the positivity `no_event` proves), `hiemenz_monotone_same_wall_shear`, `homann_monotone_same_wall_shear` (`MonotoneExists.not_lt_wall` both ways). NV witnesses from the monotone solution.
- Scripts: `runs/2026-11-08T1028Z/scripts/mk_mono.py`, `promote_mw.py`; rejected route `gen_ball.py`, `probe.py`. Audit: `Work/FalknerSkan/MWBlindClosed.lean`, `MEBlindClosed.lean`; referee `runs/2026-11-08T1028Z/referee_mw.md`.

## Bounded class of stagnation-point flows (−1 ≤ f' ≤ 1), `Work/FalknerSkan/Bounded*.lean`, `Checked/FalknerSkan/Bounded*.lean` (run 2026-11-08T1228Z)
- `BoundedTools.stays_nonpos` (fencing with barrier 0 when q' < 0 at zeros of q), `le_start`, `pos_of_abs_lt_one` (any real k: |p| < 1, p → 1 ⇒ q > 0), `fsV` / `fsV_lip` (the field (f, p, q) ↦ (p, q, −kfq − 1 + p²), locally Lipschitz), `uniq_right` / `uniq_left` (forward / backward uniqueness, Lipschitz on the compact union of two trajectories), `triple`, `triple_cont`, `eq_of_start`, `start_of_touch` (a touch of ±1 forces p(0) = ±1 via the straight-line solutions), `abs_lt_of_abs_le`, `pos_of_abs_le`, `bounded_of_pos`.
- Headlines `Bounded.hiemenz_bounded_window`, `homann_bounded_window`, `hiemenz_bounded_equal`, `homann_bounded_equal`, `hiemenz_exists_bounded`, `homann_exists_bounded`. NV witnesses from the existence theorems. Literal reading `Checked/Trust/SecondReadingBound.lean`.
- Scripts: `runs/2026-11-08T1228Z/scripts/mk_frozen.py`, `promote_bd.py`. Audit: `Work/FalknerSkan/BBlindClosed.lean` (`toSys`, `ofSys`: C³ iterated `derivWithin` ⇄ first-order system); referee `runs/2026-11-08T1228Z/referee_bounded.md`. Next: β = 1/2 row by scaling (`runs/2026-11-08T1228Z/lean/FSHalfBounded.lean`).

## Phrase fidelity of generated claims, `scripts/trust/Claims.lean`, `scripts/trust/check_claims.py` (run 2026-11-08T1828Z)
- Claims.lean: PINNED definitions listed with phrase and Lean body; Prop phrases substituted with slot bindings (`k₃ := 10000`); `.lake/phrases.jsonl` carries `spec_text` (docstrings and field names of the `Checked.Fidelity` constants the pin theorem uses, two levels).
- check_claims.py: P1 (no formula characters), U1, U2 (first glossary term own), P2 (spec quotation; baseline `scripts/trust/phrase_vocab_baseline.txt`, shrink-only via `--base`), controls in `_controls()`.
- Judge tools: `runs/2026-11-08T1828Z/t5/scripts/judge_phrases.py`, `variants_X.py`; red teams `runs/2026-11-08T1828Z/t5/redteamX`, `redteamY`.

## Falkner–Skan table rows β = 1/K, `Work/FSFifth/`, `Checked/FSFifth/`, `Work/FSTenth/`, `{Work,Checked}/FalknerSkan/{Fifth,Tenth}Bounded.lean` (run 2026-11-08T2028Z)
- Coefficient-K stack (ported from Homann, K = 2): `F5CellW`/`F5CellWC` (`defect3` with `qsmul K c.pg`, `os_kK`, psd corners at K·mlo, K·qlo, K·qhi), data `F5{U,O}Data{,C}` (128 cells per side, 16 segments), `F5ExFlow` (`lip` KT + 4K + 4, `norm_le` 2KT + 4K + 5), `F5ExLimit`, `F5ExAssemble.exists_bvp`, `F5ExMono.exists_bvp_pos`, `F5IVP.ivp_lo/ivp_hi`, `FSFifth.k5_under/k5_over/k5_exists`, `F5Bounded.k5_monotone_window/k5_exists_monotone/k5_bounded_window/k5_bounded_equal/k5_exists_bounded`; same with F10/k10 for K = 10 (96 cells, horizon 3).
- Falkner–Skan statements by scaling (`FSScale.scale`, c = 1/√K): `FifthBounded.to_k5`, `sqrt5_lt`, `lt_sqrt5`, headlines `fs_fifth_bounded_window`, `fs_fifth_bounded_equal`, `fs_fifth_exists_bounded`; `TenthBounded.fs_tenth_*` (Work).
- Generators: `runs/2026-11-08T2028Z/scripts/gen_k_w.py`, `gen_k_wc.py` (FS_K = K), `port_k.py` (K = 5), `port_row.py` (any integer K), `make_row.py` (freeze / prove a whole row), `fix_ivp.py`, `promote_fsf.py`. Audits: `Work/FalknerSkan/FBBlindClosed.lean`, `FTBlindClosed.lean`; readers `Checked/Trust/SecondReadingFSFifth.lean`, `runs/2026-11-08T2028Z/fst_reader/`.

## Falkner–Skan with no bound on f', `{Work,Checked}/FalknerSkan/{UnrestrictedCore,Unrestricted}.lean` → `Checked/FalknerSkan/{LimitCore,Limit}.lean` (run 2026-11-09T0028Z)
- Calculus on [0, ∞) from `HasDerivWithinAt (Ici 0)`: `cont_of`, `at_of`, `smono`/`santi`/`mono`/`anti` (interior derivative signs), `right_nonneg`/`right_nonpos`/`left_neg` (one-sided slopes), `le_of_right`/`ge_of_right`, `weight` (W > 0, W' = a f W via exp of an FTC antiderivative of f ∘ max · 0).
- System lemmas: `le_one` (p ≤ 1), `rder`, `phider`, `wrder`, `omder` (identities L1), `q_eventually_pos` (L4), `last_zero` (L5), `descent_core`, `descent` (L6), `ascent` (L7), `omega` (L8), `q_pos_of_touch`, `touch_one`/`touch` (L3, backward uniqueness), `q_pos`, `in_class`.
- Headlines: `{hiemenz,homann,fs_half,fs_fifth}_limit_{window,equal}` from the `*_bounded_*` theorems; helper `fs_monotone_of_limit` (β-form, scaling by `FSScale.scale` with c = √β). Audit `Work/FalknerSkan/UBlindClosed.lean`; referee `runs/2026-11-09T0028Z/referee_unrestricted.md`; script `runs/2026-11-09T0028Z/scripts/promote_unres.py`.

## Falkner–Skan β = 1/10 in Checked and the general-β headline, `Checked/FSTenth/`, `Checked/FalknerSkan/{TenthBounded,LimitTenth}.lean` (run 2026-11-09T0428Z)
- `Checked/FSTenth/` (14 modules) and `TenthBounded.lean` copied from Work by `runs/2026-11-09T0428Z/scripts/promote_fst.py` (pattern `promote_fsf.py`; number-free module docs). `LimitTenth.lean`: `fs_tenth_limit_{window,equal}` = `fs_tenth_bounded_*` with the class from `Limit.fs_monotone_of_limit` + `BoundedTools.bounded_of_pos`. `fs_monotone_of_limit` registered (reader `Checked.Trust.SecondReading.fsBetaRhs`). Audit `Work/FalknerSkan/FTLBlindClosed.lean`. Research for β < 0: `runs/2026-11-09T0428Z/research/fs_negative_beta.md`.

## Falkner–Skan with adverse pressure gradient (β < 0), `Work/FalknerSkan/Neg*.lean`, `Work/FSNeg/` (run 2026-11-09T0828Z)
- Uniqueness for every β < 0 in the class f'' > 0 + super-exponential approach: scaling `NegCore` → Crocco map adverse sign `NegCrocco` → no-crossing `NegNoCross` (replaces the cooperative `CroccoCompare`) → `NegUPrime` (max wall shear) → `NegDecay`.
- β = −1/10 existence and non-uniqueness: `NBase` (clamped field, Over/Slow) → `NCellWC` + chains `NSlowHalf`, `NSlow34`, `NOver11` (generator `runs/2026-11-09T0828Z/scripts/gen_neg_wc.py`) → `NFlow`, `NSlowInv`, `NLimit`, `NRiccati`, `NLemma1`, `NUnclamp` → `NAssemble` (core theorems over `ChainTo`) → `NegTenth`.
- Promoted (run 2026-11-09T1028Z): `Checked/FSNeg/`, `Checked/FalknerSkan/Neg*.lean`; headline `NegOutside.fs_neg_tenth_outside_decay` (two solutions outside the decay class, from `NegTenth.fs_neg_tenth_not_unique`); readings `SecondReadingFSNeg`, `SecondReadingFSWall`; necessity witnesses for the decay hypotheses.
- Next: ten-decimal window; reversed-flow branch (Lemma D).

## Hypothesis necessity (trust track T2b), `Checked/Trust/NonVacuity.lean`, `Checked/Trust/Necessity.lean` (run 2026-11-09T0628Z)
- Obligations `necessity% thm i`, `dropped% thm i` (numbering as CLAIMS.md); classification in `scripts/trust/StatementDeps.lean` → TRUST_MAP.md "Hypothesis necessity" (report-only).
- Witnesses generated by `runs/2026-11-09T0628Z/scripts/{gen_nc.py,gen_y.py,emit_nc.sh}`; generic lemmas `expProfile`, `linF_deriv`, `linQ_deriv`, `linProfile`. 155 needed + 17 redundant of 794.
- Run 2026-11-11T0028Z: `Checked/Trust/NecessityB.lean` (run 2228Z's scratch batch repaired and completed, plus four families: junk critical points of the cubic isotherm `crit_of_unbounded`/`crit_at_b`/`crit_at_root`; de Sitter against the ΛCDM/CPL coefficient laws and records; the lookback expansions with the scale factor `flatStart` = 1 + t²; `ne_a0_of_hubble` (24 redundancies) and `not_littleO_core` (Hubble rate needed in 7 series)). 253 needed + 51 redundant of 843; 22/150 headlines fully classified.
- Ratchet (blocking): `scripts/trust/check_necessity.py` N1–N3 + planted controls; baseline `scripts/trust/necessity_open_baseline.txt` (exactly the open hypotheses).
- Next: the remaining series/curvature families (`Ω₀`-conditions of the `_fails` headlines, `ContDiffAt` redundancy by bootstrap), boundary-value families (`f 0 = 0`, far-field limits) via the certified IVP solutions.
- Runs 2026-11-11T1428Z, 1628Z (item 3e): per-part obligations `necessity% thm i j` / `dropped% thm i j` (`partsWalk`: through ∧, ∃, ∃!, ∀, ∀ᶠ, ↔, an implication's conclusion; part replaced by `True`); `necShape` (`bundled` = ≥ 2 parts, `restated` up to unfolding, `subtype` through type definitions) gates the fully-classified tally (N4, shape baseline); witnesses `Checked/Trust/NecessityF.lean` (cosmography: `a ↦ -a` invariance and law ⇒ differentiability). Blind round AG: `runs/2026-11-11T1628Z/t5/`.
- Run 2026-11-12T0828Z (blind red team AH): `partsWalk` opens set membership (`p ∈ {q | A ∧ B}`, intervals) into parts; StatementDeps `carriesProof` flags binder types with a proposition field (`ℝˣ`, `PLift P`, `Fin n`) as `subtype`; the "each alone, not together" label counts redundant hypotheses and parts together.
- Run 2026-11-11T2028Z: `Checked/FalknerSkan/BoundedLimit.lean` (`stays_nonpos_from`, `mono_le`, `anti_le`, `tendsto_of_pos`, `false_of_nonpos` → `tendsto_of_bounded` (k > 0), `tendsto_of_bounded_beta` (β > 0, via `FSScale.scale`)); witnesses `Checked/Trust/NecessityH.lean` (generator `runs/2026-11-11T2028Z/lean/gen_necG.py`): parts of the velocity bound by the `_limit_` headlines, the far-field condition by `BoundedLimit`.

## Falkner–Skan β = −1/10, reversed flow and ten-decimal windows, `Work/FSNeg/{NWin*,NWindow,L*}`, `Work/FalknerSkan/{NegWindow,NegReversed}.lean` (run 2026-11-09T1228Z)
- Attached window: certified Slow/Over at the scaled window ends (`NWinLo`, `NWinHi`), `NWindow.core_window` (supremum argument for any certified window lo < hi ≤ 11/10), uniqueness and largest shear from `NegDecay`.
- Reversed branch: Over and the lower Slow event `LCell.SlowL` at the window ends (`LOver`, `LSlow`), a tube for the whole window on [0, 3/2] (`LTube`, `LCell.endT`, `sideP`, `cell_box`), Lemma I for the clamped field (`LInv`), no clamp after 3/2 (`LUnclamp`), `LAssemble.core_lower`.
- Promoted (run 2026-11-09T1628Z, through CI): `Checked/FSNeg/{NWinLo,NWinHi,NWindow,LCell,LInv,LUnclamp,LAssemble,LOver,LSlow,LTube}`, `Checked/FalknerSkan/{NegWindow,NegReversed}.lean`; four headlines; NV witnesses for the two window theorems; necessity witnesses (f'' > 0 needed in `NegDecay`, reversed-flow counterexample).
- Next: β = −0.15 (K = 20/3) or the exact classical class (Hartman Ch. XIV).
- **Part 3 (run 2026-11-09T1828Z):** P13 — every SIGN/CLAUSE reader line of a phrase is a theorem of `Checked/Trust/PhraseCerts.lean` about its definition (registry `scripts/trust/phrase_certs.txt`; conditions printed after the phrase; `PHRASE_LINES.md`) or in the shrink-only `phrase_cert_baseline.txt`. Next: certify group A (34 owed), a check that a certificate's statement matches its line (AE d02), unpinned predicates in certificate hypotheses printed with their bodies (AE d04c).

## Falkner–Skan separation value, `Work/FSSep/`, `Work/FalknerSkan/Separation*.lean` (run 2026-11-11T0232Z)
- Existence: `SBase` (field `vS K`, events `Over`, `SlowS`, `ChainK`) → `SCellWC` (`CellProp K`, rational coefficient) + chains `SOverLo`, `SSlowHi` (generator `runs/2026-11-11T0232Z/scripts/gen_sep_wc.py`, emitter `emit_sep_wc.py`) → `SFlow` (`flowK`, `flowK_cont` in K) → `SUnclamp` (q(0) = 0) → `SAssemble.core_sep` → `Separation.fs_separation_exists`.
- Uniqueness: `UCrocco` (β-form Crocco map, q > 0 only on (0, E)) → `UCompare` (`SolB`, `start` by z², `no_cross_s`, `stepS`) → `UPair.sep_core` → `SeparationUnique.fs_separation_unique`.
- Audits: `SepBlindClosed.lean`, `SepUniqueBlindClosed.lean`.
- Promoted (same run): `Checked/FSSep/*` (+ `SSlowSol` for necessity), `Checked/FalknerSkan/{Separation,SeparationEqual}.lean`; reading `Checked/Trust/SecondReadingFSSepW.lean`; necessity `Checked/Trust/NecessityC.lean`. Next: the 16 open hypotheses of `fs_separation_equal`; β-form endpoint events.

## Hypothesis necessity: shape of the statement (run 2026-11-11T0428Z)
- `scripts/trust/StatementDeps.lean` `necConjuncts` (conclusion conjuncts through `let` and program definitions) → `necShape` (`conclusion`, `subtype`, `bundled i`, `restated i`) → `shape:` entry of each TRUST_MAP.md necessity line, excluded from the fully-classified tally → `scripts/trust/check_necessity.py` N4 with `scripts/trust/necessity_shape_baseline.txt` (shrink-only). Blind measurement: `runs/2026-11-11T0428Z/t5/` (red team AF). Next: per-conjunct necessity for the bundled predicates.

## Hypothesis necessity, fourth batch (run 2026-11-11T0628Z)
- `Checked/Trust/NecessityD.lean` (namespace `Checked.Trust.NCD`): models `cub c = 1 + t + c t³`, `kink n = 1 + t + tⁿ⁺¹|t|` (`pabs_hasDerivAt`), static `a = 1`; comparison `compare_general` / `not_littleO_decomp` with `comoving_bounds`, `lumflat_bound`, `angflat_bound`, `dQflat_bound`; bootstrap `contDiffAt_of_law` → `contDiffAt_of_flatLCDM`, `contDiffAt_of_flatCPL`, `exists_flatLCDM_any`; `not_hasDerivAt_of` (removable-looking singularity); toy Falkner–Skan profile `toyP`, `toyQ`; `not_unique_of_pole` (uses `NCB.crit_at_root`). Scratch history in `runs/2026-11-11T0628Z/lean/`. Next: the `_fails` smoothness hypotheses (junk fifth derivative with a prescribed true coefficient), B1 interval hypotheses, bundled predicates (item 0b).

## Falkner–Skan printed values (run 2026-11-11T0828Z)
- `Checked/FalknerSkan/SeparationPrinted.lean` (branch `wip/sep-printed-promo`): `Separation.fs_separation_exists` + `SeparationEqual.fs_separation_equal` → the printed β_min is outside the window. Reading `Checked/Trust/SecondReadingFSSepPrinted.lean`; necessity `Checked/Trust/NecessityE.lean` (profiles `1 − e^{−kη²}`, `min(η, 1)` with the linear q-solution); blind closure `Work/FalknerSkan/SepPrintedBlindClosed.lean` (branch `wip/sep-printed`).
- `Work/FalknerSkan/Neg1988.lean` (frozen): β = −0.1988 window and existence; route: template `Checked/FSNeg/` to K = 2500/497 (STATE exact next step 2).

## Falkner–Skan attached rows, generic in K (run 2026-11-11T1028Z)
- `Checked/FSAtt/ABase` (`SlowA`, `ChainA K α E`) → `AFlow` (flow of `SBase.vS K` from (0, 0, α), continuous in α; `SFlow` lemmas) → `AUnclamp` → `AAssemble` (`over_open`, `slow_open`, `slow_not_over`, `neither_class`, `slow_class`) → `AWindow` (`core_window`, `window_of_chains`, with `NegDecay.fs_neg_decay_equal`).
- Row β = −1988/10000 (K = 2500/497): `N1988Lo`, `N1988Hi` (generated chains on `FSSep.SCellWC`), `N1988Core` (√K bounds), headlines `Checked/FalknerSkan/NegWallShear.lean`; Work: `Work/FalknerSkan/Neg1988.lean`, blind closure `Neg1988BlindClosed.lean`.
## Falkner–Skan reverse-flow branch, generic in K (runs 2026-11-11T1228Z, 1828Z)
- `Checked/FSRev/RBase` (`SlowR`, `PhiT`, `TubeR K`) → `RCell` → `RInv` → `RUnclamp` → `RIdent` (`ident`, `cell_box_lt`, `uS`, `PhiS`) → `RAssemble.core_rev`; row K = 2500/497: `R1988Over`, `R1988Slow`, `R1988Tube`, `R1988Printed` (ball around the printed value), `R1988PrintedEnd` (end state at t = 4); global continuation `RGlobal` (`vT`, `Q`, `W`, `tail`) → `RPrintedNV.printed_ivp_exists`; headlines `Checked/FalknerSkan/NegReversedWallShear.lean`; necessity `Checked/Trust/NecessityG.lean`.
## Suction witnesses for wall conditions (run 2026-11-11T2228Z)
- `Checked/Suction/<T>Flow` (`flowS a0 α`, `flowS_cont`) → `<T>Limit.no_eventS` (0 ≤ a0 ≤ 2) → `<T>UData`/`<T>OData` (cells from (a0, 0, lo/hi)) → `<T>Assemble.exists_bvpS`, for T = HS (Hiemenz), HmS (Homann), F5S, F10S (coefficients 5, 10); witnesses `Checked/Trust/NecessityI.lean` (Blasius, β = 0), `NecessityJ.lean` (Hiemenz), `NecessityK.lean` (Homann, β = 1/2, 1/5, 1/10).
## Necessity witnesses for the B1 family and the pinning theorems (run 2026-11-12T0227Z)
- `Checked/Trust/NecessityL.lean` (`Checked.Trust.NCL`): `diff_of_law`, `H0_pos_of_redshift` (generic redundancies of the law), `flat_arg_pos`, `curved_arg_pos`; `model_ratio` (exact ΛCDM at Ω = 1/5: `d₅ ≤ 4 d₃`) → `no_rise` → `box_fails`; radiation model `rad_*` (`a = √t`, `rad_dL`: `d_L = 2z`) → `rad_diff_le`; off-domain spec witnesses `hubbleOff`, `decelOff`, `yredOff`, `omega0Off`, `curvKOff` (each meets its specification).

## Bonnor–Ebert critical sphere, `Work/Math/BE*.lean`, `Work/Math/BonnorEbert*.lean` (run 2026-11-12T0427Z)
- Start `BEStart.startBE` (Gelfand start template, [0, 1/64], domain [0, 7]) → cells `BEQData` (381, `GCellQ.Cell`, `bchainTo` with `BECellQ.BInvProp` modes 1/2) → `BEChain.chain` (φ²/2 < e^w on [1/64, A], bracket-cell enclosure on [A, B], e^w < φ²/2 on [B, 7]) → `BEMain.bonnor_ebert_critical` (with `GProfile.profile_bounds` on (0, 1/64], `GFinal.derivs_at`) → `BonnorEbert.bonnor_ebert_critical` (frozen statement).
- Audit: `BonnorEbertBlind.lean` (verbatim blind file), `BonnorEbertBlindClosed.lean`.
- Checked (run 2026-11-12T0628Z, from run 0427Z's branch): `Checked/Math/{BECellQ,BEStart,BEQData,BEChain,BEMain,BonnorEbert}.lean`; NV `Checked.Trust.NV.bonnor_ebert_critical` (Gelfand existence at 7); necessity `Checked/Trust/NecessityM.lean` (`scaled_hyps`: u(s) = w(cs) + 2 log c; hypotheses 1–5 classified; also Gelfand 5, Thomas–Fermi 1, Gelfand PDE 2–3); literal reading `Checked/Trust/SecondReadingBE3.lean`.
- Next: promotion to `Checked/Math/` (STATE 0e); the maximum over all radii.
## Necessity of the chemistry acentric-factor hypotheses (run 2026-11-12T1228Z)
- `Checked/Trust/NecessityO.lean` (`Checked.Trust.NecessityO`): `not_ii_of_pole` → `maxwell_zero_of_pole` (junk Maxwell states at pressure 0); `crit_RT_pos` (from `CubicEOS.reduced`); `big_pressure`; per EOS `*_junk_maxwell`, witnesses `*_h<i>`, RK redundancies `rk_coexistence_{unique,exists}_r{1,2}` (`rk_no_crit`). PR/PR78 emitted from SRK by `runs/2026-11-12T1228Z/scripts/gen_pr.py`.
- `Checked/Trust/MaxwellRight.lean` (`Checked.Trust.MaxwellRight`): `integral_gt_of_strictConcave`, `integral_lt_of_strictConvex`; `p1`, `p2`, `hasDerivAt_p1`, `deriv2_eq` (second derivative on an open set through `EventuallyEq.deriv_eq`), `p2_neg`, `p2_pos`, `p_ne_zero` → `maxwell_right` → `srk_omega1_unique_r5`, `rk_coexistence_unique_r7` (with `SRKExists.theta_bounds`, `RKExists.theta_bounds`).
- `Checked/Trust/NecessityP.lean`: FR13 `fr13_zda{68,738}_h{3,5}`, `_r4` (`gt_neg_one_of_cube`); `eta_ratios_r2`.
