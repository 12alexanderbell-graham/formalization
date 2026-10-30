# Fidelity audit (annex XL): C5, Bamba et al. 2012 Eq. (10.54)

Headlines: `lumDist_y_third_order`, `printedD2y_fails`, `printedD2y_fails_past`, `bambaD2yClaim_false`, `bambaD2yClaimPast_false` (namespace `…Cosmography.BambaY`). Definitions: `yred`, `comoving`, `lumDistFlat`, `D1y`, `printedD2y`, `correctD2y`, `seriesY`, `remainderY`, `BambaD2yClaim`, `BambaD2yClaimPast`.

- **Frozen:** commit 6636035, before proof work. Proof commit 819f3be; statements byte-identical (checked by diff: only `sorry` lines removed).
- **Source:** `source_C5.md` (typeset text, v3 p. 108–111; referee re-read v1, v2, v3: (10.54) identical in all).
- **Blind restatement:** subagent from the source alone (`blind/C5_blind.lean`, compiled, refuted the claim itself on de Sitter). Closed in Lean (`Work/Cosmography/BambaDLyAudit.lean`, `C5Audit`): `residual_eq` (blind residual = ours, every `t`, once `a(t₀) ≠ 0`, both printed and corrected `D²`); `blind_implies_ours` (blind claim, C^∞ class ⇒ our analytic-class claim); `blind_false`; `blind_derived_holds` (our general theorem gives the blind's independently derived coefficient). Divergences recorded: blind uses C^∞ (we use analytic: our claim is the weaker one, so our refutation is the stronger one); blind also states a literal `O(y⁴)` reading, implied by ours. Same model, shared blind spots (annex 40.2).
- **Not vacuous:** de Sitter (`a = exp`, `t₀ = 0`) satisfies every hypothesis (`C5Audit` example; used in the refutations).
- **Not trivial:** general theorem needs Taylor + mean-value inequality + FTC for the comoving integral; no single tactic closes it.
- **Bites on examples:** de Sitter: general theorem gives `D¹ = 2`, `D² = 3` = exact `y/(1−y)²` series; printed gives `−3`.
- **Near-misses:** printed `D²` fails in every flat C³ model with `11 − 5q₀ + 3q₀² − j₀ ≠ 0` (the exact condition: printed − correct = −2·correct); corrected passes for all.
- **Junk values:** `∫ 1/a` is honest near `t₀` (C³ ⇒ `a` continuous and nonzero on a ball; the claims assume `a > 0` everywhere); `x/0` excluded near `t₀` by `a(t₀) ≠ 0`; `deriv` junk excluded by C³ at `t₀` and `H₀ ≠ 0`; no ℕ subtraction.
- **Types/quantifiers:** real; ∀ models; remainder `o(y³)` as `t → t₀` (weakest reading); two-sided and past-only (`𝓝[<] t₀`) both refuted.
- **Readings (Underspecified):** the y-series is not printed in the review; `y = z/(1+z)` and `d_L(y) = (cy/H₀)[D⁰ + D¹y + D²y² + …]` are pinned by the printed `D¹_{L,y}` (= 1 + D¹_L only for this reading) and by the review's own `d_A,y` coefficients (10.58)–(10.60), which are consistent with this reading and imply the `+` sign (referee).
- **Classification:** **Source** error (sign of (10.54)), introduced in the review; upstream Cattoën–Visser 2007 Eq. (52) is right.
- **Scope:** Lean covers the flat instance (`Ω₀ = 1`). The referee shows the sign error holds for every curvature (Milne, open-dust Mattig checks; sympy); not in Lean.
- **Referee** (`referee/`): STANDS-WITH-CORRECTIONS. Corrections taken: the error is not flat-only (scope note above); the review does not simply "reproduce" CV Eq. (52) (it adds y³, y⁴ and d_A,y; its curvature terms there are wrong: C6, C7 now confirmed by a second independent derivation); crop `typeset/C5_p110_Omega0_def_eq10.52-53.png` shows only the Ω₀ definition (mislabelled; (10.52)–(10.54) are in `crop_p111_eq10.54-57_DLy.png`). No erratum or prior report found; D_{L,y} is not used numerically in the review (presentational error).
- **Axioms:** `#print axioms` on all five headlines (Checked): `propext, Classical.choice, Quot.sound`.

# Fidelity audit (annex XL): C1, Cattoën–Visser 2007 Eq. (59)

Headlines: `dQ_y_third_order`, `printedQ2_fails_past`, `cvdQClaim_false`, `cvdQClaimPast_false` (namespace `…Cosmography.CVdQ`). New definitions: `dQFlat` (= d_L/(1+z)^{3/2}, `Real.rpow`), `printedQ2`, `correctQ2`, `seriesQ`, `remainderQ`, `CVdQClaim`, `CVdQClaimPast`; reuses the audited F4 definitions.

- **Frozen:** commit d18789a. Proof commit 63610cd; statements byte-identical (diff removes only `sorry`). Docstring citation fixed after the referee (d_Q is Eq. 5, not 3); no statement touched.
- **Source:** `source_C1.md`; typeset (59) read in run 0220Z and by the referee this run (only v1 exists; 0809.0537v1 Eq. (32) identical).
- **Blind restatement:** `blind/C1_blind.lean` (own definitions; refuted the claim itself on de Sitter). Closed in Lean (`Work/Cosmography/CVdQAudit.lean`, `C1Audit`): `remainder_eq` (blind remainder = ours for any coefficient, once a(t₀) ≠ 0), `blind_implies_ours` (same analytic class, past-only), `blind_false`, `blind_derived_holds` (our general theorem gives the blind's independently derived 1/24). Same model, shared blind spots.
- **Not vacuous / bites:** de Sitter satisfies all hypotheses; exact H₀d_Q = y(1−y)^{−1/2}: coefficient 3/8 = `correctQ2 (-1) 1 1`, printed 3/4.
- **Near-misses:** printed fails in every flat C³ model with −1 − 2q₀ + 12q₀² − 4j₀ ≠ 0 (printed − correct = correct); corrected holds for all.
- **Junk values:** `rpow` base 1 + z = a₀/a > 0 near t₀ (proved on the neighbourhood, `Real.inv_rpow` used only there); others as F4.
- **Types/quantifiers:** real; o(y³) weakest reading (blind's O(y⁴) reading implied); two-sided and past-only refuted.
- **Classification:** Source error (misprint 1/12 for 1/24). **Scope:** flat instance in Lean; referee: curvature-independent (constant term), EdS check.
- **Referee:** STANDS-WITH-CORRECTIONS: the 1/12 already appears in gr-qc/0703122 (v1–v3, Eq. 59/60) and is copied into 0710.1887 (59) and 0809.0537 (32); the papers' fits use the correct ln-series, so no numerical result is affected; d_Q is Eq. (5). All adopted.
- **Axioms:** `#print axioms` on the four Checked headlines: `propext, Classical.choice, Quot.sound`.
