# Fidelity audit: C3, lookback distance to fifth order (Capozziello, Cardone, Salzano 2008, Eq. (A2))

Promoted: `Checked/Cosmography/CCSLookback.lean`, namespace `Checked.Cosmography.CCS`.
Frozen in commits `362315b` (CCSD4Claim, lookback_fifth_order, printedD4_fails, ccsD4Claim_false)
and `76227bf` (CCSD4ClaimPast, printedD4_fails_past, ccsD4ClaimPast_false), before any proof of
them. Statements unchanged since (every frozen line present, in order, in the proved file — checked
by script); only helper definitions/lemmas inserted and `sorry`s replaced. Work and Checked differ
only in namespace and the module docstring's FROZEN/PROMOTED line (checked by `diff`).

Headline declarations: `printedD4`, `correctD4`, `series`, `remainder` (definitions; reuse audited
`hubble`, `decel`, `cosmoCoeff`, `redshift`); `CCSD4Claim`, `CCSD4ClaimPast` (frozen printed claim,
two readings); `lookback_fifth_order` (correct series for every C⁵ scale factor);
`printedD4_fails`, `printedD4_fails_past` (printed D⁴ false in every C⁵ model with q₀ ≠ 0);
`ccsD4Claim_false`, `ccsD4ClaimPast_false` (de Sitter).

**SOURCE.** arXiv:0802.1583v2 App. A, Eqs. (1), (A1), (A2), p. 15–16 (App. A absent in v1).
Typeset: rendered PDF (`typeset/C3_ccs2008_v2_p16_A2.png`), read by the main session and,
independently, by the referee at 200 and 400 dpi. Quote: `source_C3.md`.

**Plain words.** Light emitted a short time ago reaches us with small redshift z; the travel time,
expanded in powers of z, has coefficients fixed by H₀, q₀, j₀, s₀, l₀. The paper prints the z⁵
coefficient with 7/2 q₀⁴ where inverting its own (A1) gives 7/8 q₀⁴. All other coefficients right.

## 40.2 Blind restatement
Subagent given only `source_C3.md` (+ the PDF); no access to Work/Checked/runs/git. File:
`blind/C3_blind.lean`, copied verbatim (namespace renamed `C3Blind`) into
`Work/Cosmography/CCSAudit.lean`.
- Same: H = ȧ/a, q = −ä/(aH²), j, s, l = a⁽ⁿ⁾/(aHⁿ), z = a(t₀)/a(t) − 1, D = c(t₀ − t*), the
  parametric reading in t* (no explicit inverse), D⁰…D⁴ transcribed identically.
- Divergences (all **Underspecified** by the source): restater's primary reading is C⁶ + O(z⁶)
  two-sided; it also wrote past-only O(z⁶) and C⁵ + o(z⁵). Ours: o(z⁵), C⁵ (positive theorem) /
  analytic (refuted claim), two-sided and past-only. Its readings all imply ours on de Sitter.
- Closed in Lean (`C3Audit`): `blindClaim_false`, `blindClaim_past_false`,
  `blindClaim_littleO_false` (every analytic reading the restater wrote is false);
  `blind_defs_exp`, `blind_rem_exp` (its definitions and remainder equal ours on de Sitter).
  Its purely formal reading R3 (polynomial coefficients) left with the restater's `sorry`
  (equivalent to R1 by the restater's own argument; not needed).
- Restater's independent sympy (`blind/C3_blind_sympy.py`): printed − derived = +21/8 q₀⁴ in D⁴,
  zero elsewhere; checked against the exact Einstein–de Sitter series (D⁴ = 231/128, printed 63/32).

## 40.3 Sanity tests
- Not vacuous: de Sitter (`Real.exp`, analytic, positive, H₀ = 1, q₀ = −1) satisfies every
  hypothesis of both claims and of `lookback_fifth_order` (used in `ccsD4Claim_false`).
- Bites / near-misses: `printedD4_fails` is the near-miss test for `lookback_fifth_order`: changing
  one coefficient of D⁴ makes the statement false in every model with q₀ ≠ 0. On de Sitter the
  correct coefficients are those of ln(1+z) (1, −1/2, 1/3, −1/4, 1/5); referee and restater
  confirmed EdS and flat ΛCDM (Ω = 0.3, mpmath 40 digits) numerically.
- Not trivial: Taylor's theorem (Mathlib `taylor_isLittleO`) plus an asymptotic series inversion
  (`inversion`): truncated reciprocal and powers with sympy-generated remainder polynomials
  (`scripts/gen2.py`), each identity checked by `ring`.
- Junk values: `decel`, `cosmoCoeff`, `hubble` divide by a(t₀), ȧ(t₀): theorems assume a(t₀) ≠ 0,
  H₀ ≠ 0 (so ȧ(t₀) ≠ 0); `ContDiffAt ℝ 5` makes all `iteratedDeriv`s genuine. z(t) uses a(t)
  near t₀, nonzero by continuity. o(z⁵) is not vacuous: z ≠ 0 on a punctured neighbourhood
  (`HasDerivAt.eventually_ne`, z'(t₀) = −H₀), used in the refutations.
- Types and quantifiers: ∀ a t₀; limit t → t₀ (𝓝 t₀ and 𝓝[<] t₀); c cancels (H₀D/c = H₀(t₀−t*)).

## Error classification
**Source** (misprint) in (A2) D⁴: 7/2 q₀⁴ should be 7/8 q₀⁴. Not Translation: the restater's
independent formalization and two independent derivations (series reversion, Lagrange inversion)
agree. Secondary (sympy + typeset, not in Lean): (A5) R⁵_D has l₀/6 (24 l₀/144) where l₀/720 is
correct (flat case).

## Verdict
AUDITED. With green CI on `Checked` + standard axioms: PROVED.
