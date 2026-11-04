# Run 2026-11-04T1828Z (scheduled)

> **Unchecked prose.** Written by hand; no script checks what these sentences claim beyond citations. The Lean statements, `TRUST_MAP.md` and certified numbers win where they disagree.

Environment: add_repo not exposed; repo pre-cloned (detached HEAD, stale local `main` reset to origin/main). No LOCK (run 1628Z closed). **Local Lean available** (elan installer accepted; Mathlib cache). CI of run 1628Z: promotion 49989be **41883514176 green** (FR13 data claim PROVED); other ids in STATE "Environment".

**THE RESULT:** part 5 (breadth) moves, after five runs idle: the chemistry pipeline leaves the one rational case (van der Waals) for an equation of state with irrational critical constants and a temperature-dependent attraction. The Redlich–Kwong acentric factor is frozen, proved (uniqueness of the numbers and existence), blind-audited (blind restatement closed in Lean) and refereed in one run. Mathematics still has no certified result.

**WHAT CAN A SCIENTIST NOW TRUST WITHOUT CHECKING IT THEMSELVES?** For the original Redlich–Kwong fluid P = RT/(v − b) − A/(√T v(v + b)), any R, A, b > 0 and any critical point: at T = 0.7 T_c every Maxwell equal-area coexistence state (liquid volume above b) has p_s/P_c = 0.087 and acentric factor ω = 0.058 (3 decimals each; proved window p_s/P_c ∈ [0.08743, 0.087458]), and such a state exists. Before, this number existed only as floating-point output (Shamsundar & Lienhard 1983 print 0.058); it was not known to be the value of *every* coexistence state.

**Kind of result (PROMPT working note on part 2/5 questions):** answer already in print (referee: Shamsundar & Lienhard 1983, ω = 0.058 for an RK fluid); new is the certified form, the uniqueness, and the method (θ-uniform certificates for irrational constants).

**WEAKEST UNCHECKED STEP NOW:** the existence of the RK critical point used by the non-vacuity witness comes from a constant-attraction instance read as A = √T_c (sound, but the general RK existence/uniqueness of T_c for every R, A, b is proved only in Work, `Work/Chemistry/CubicEOSTemp.lean`, not promoted). Second: the module doc's prior-art statement is one referee reading of an OCR text.

**BOTTLENECK AND WHY:** part rotation: part 5 idle since 0828Z (rule: four idle runs gets the block). STATE offered a mathematics result or RK/PR acentric factors. A mathematics question whose answer is not in print could not be screened and proved inside one run; the RK acentric factor was the decisive chemistry step because every cubic beyond van der Waals has irrational critical constants (cube roots of 2) and a temperature-dependent a(T) — the vdW proof did not show that the method survives either. Yes = the certified-coexistence method extends to the whole cubic family (SRK, PR next, same template); no = each EOS needs bespoke proofs.

**WHAT WE DID:**
1. Floating point, two routes (`scripts/rk_float.py`: Maxwell areas in reduced variables; `scripts/rk_fugacity_check.py`: equal fugacity from the Z-cubic): p_s/P_c = 0.087442, ω = 0.05828. Side computation (not frozen): Soave's own κ(ω) correlations, fed back into SRK and PR at T_r = 0.7, reproduce their input ω to 3·10⁻⁴ (SRK, ω ≤ 0.5) and 4·10⁻³ (PR, ω ≤ 0.5), but PR misses by 0.058 at ω = 1.0 (session scratch; candidate for a later data/consistency claim).
2. Froze two statements (46d5200, `Work/Chemistry/RKAcentric.lean`) using only existing program definitions (`cubicP`, pinned `IsCriticalIsotherm` and `IsMaxwellCoexistence`, `acentric`, `RoundsTo`): no new definition to classify or pin.
3. In one message: blind restater (from the claim alone), referee (fidelity, independent numerics, prior art), prover (fork).
4. Proof (2278758, axioms standard): reduced variables x = v/b, θ = RTb/a(T); every θ in a rational interval of width 2·10⁻⁸ (from bounds on the critical root x_c and on √0.7) gives the reduced-pressure window [0.0012845, 0.0012849]: Rolle, critical points of g_θ localised by the sign of a quartic linear in θ, generated exact-rational brackets and certified logarithms (`scripts/gen_rk.py`); existence by the intermediate value theorem on the maxima of the primitive over liquid and gas windows (`Work/Chemistry/RKExists.lean`, `scripts/gen_rk_exists.py`).
5. Audit (c1d077d): blind restatement closed in Lean (`Work/Chemistry/RKAcentricAudit.lean`): the blind pressure is literally the program's `cubicP R (A/√T) b 1 0 T`; the blind numbers (incl. 0 < p_s/P_c), existence and combined claim follow from the frozen theorems. Referee STANDS-WITH-CORRECTIONS (`referee_rk.md`): statements faithful and true; exactly one Maxwell state; `0 < R` redundant (harmless); value in print (applied to the Checked module doc).
6. Promotion to Checked (`Checked/Chemistry/RK{Reduced,Exists,Acentric}.lean`, specific Mathlib imports): headlines registered, NV witnesses `Checked.Trust.NV.rk_coexistence_exists`, `rk_coexistence_unique`; see STATE "Environment" for what was verified locally (all CI-replica checks green) and in CI.

**WHAT COULD STILL BE WRONG:** the statement is about the RK model, not about real fluids; 3 decimals only; the T_r = 0.7 reference is Pitzer's definition. One referee reading of the prior art.

**NEXT:** STATE "Exact next step".
