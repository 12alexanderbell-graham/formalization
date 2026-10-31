# Fidelity audit (annex XL): Checked.Chemistry.CubicEOS (run 2026-10-31T0628Z)

Headlines: `isCritical_iff`, `critCubic_existsUnique`, `exists_unique_critical`, `vdW_constants`, `rk_constants`, `pr_constants`.
Definitions: `cubicP` (FORMULA: the generalized two-parameter cubic EOS, displayed), `critCubic` (FORMULA), `IsCriticalIsotherm` (PHYSICS, pinned by the blind `CriticalSpec`).

- **Frozen** before proof: commit 9241870 (`Work/Chemistry/CubicEOS.lean`, statements with `sorry`).
- **Changes at proof time (all strengthenings: hypotheses removed, none added, conclusions unchanged):** `isCritical_iff` drops `0 < R`, `0 < b`, `0 < T` (unused; the unused-hypothesis check would block them); the three constants theorems drop `0 < R`, `0 < T` (at a critical point `R T D² = a (v−b)² (2v+ub) > 0`); `exists_unique_critical` takes `0 < 1 + u + w` instead of `∀ v ≥ b, 0 < v² + ubv + wb²` (implied by it; equivalent given u > −2: referee item B).
- **Blind restatement** (`Work/Chemistry/CubicEOSBlind.lean`, subagent, textbook only, own pressure functions and own `IsCriticalPoint` with T > 0, v > b built in): all six blind statements proved from the Checked theorems in `Work/Chemistry/CubicEOSAudit.lean` (closed in Lean). The blind pressures `v²`, `v(v+b)`, `v(v+b)+b(v−b)` equal the program's (u, w) = (0,0), (1,0), (2,−1) by `ring` (a machine-checked second reading of the family).
- **Definition pin** (T1): blind spec `CriticalSpec` (subagent, did not see the definition; determining law without `deriv`: `p(v′) − p(v) = o((v′−v)²)` for C² isotherms, plus vdW anchors, near misses incl. a stationary non-inflection point, invariances). Copied verbatim to `Checked/Fidelity/CriticalSpec.lean`; `isCriticalIsotherm_meets` (all 15 fields) and `criticalSpec_pins` (from the determining law alone).
- **Not vacuous:** witnesses in `Checked/Trust/Witnesses.lean` (vdW explicit T = 8/27, v = 3; RK and PR from `exists_unique_critical`); CI-enforced.
- **Not trivial / bites:** the constants are specific decimals with margins down to 5.3e-7 (PR Ω_a, referee table); Soave's printed 0.42747 would fail `RoundsTo · 5`.
- **Junk values:** v > b and D(v) > 0 keep both poles away; `deriv` acts on the germ at v where the function is smooth (referee §3). Ω's are stated as the ratios themselves, no division by a possibly zero R·T: R·T > 0 follows from criticality.
- **Quantifiers:** constants hold at *every* critical point; `a` is the attraction parameter at the temperature considered, so every α(T) is covered for the constants. **Scope (referee item A):** existence and uniqueness of the critical *temperature* are proved for constant `a`; with a temperature-dependent a(T) they need the fixed-point equation R T D² = a(T)(v−b)²(2v+ub) (not proved here; for RK's a/√T it is explicit).
- **Referee** (`referee_eos.md`): STANDS-WITH-CORRECTIONS. A (scope above: recorded), B (adopted), C (Soave printed 0.42747: recorded, truncation not rounding), D (RK 1949 printed values unverified: not cited).
- **Error classification:** none found in the program's statements (no Translation/Underspecified errors).

Verdict: AUDITED.
