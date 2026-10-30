# Fidelity audit: C2, flat ΛCDM cosmographic coefficients (Aviles et al. 2012, Eq. (15))

Promoted: `Checked/Cosmography/LCDMCoefficients.lean`, namespace `Checked.Cosmography.Aviles`.
Frozen in commit `9b658b7` (`Work/Cosmography/AvilesLCDM.lean`); the frozen claims were then
strengthened once before promotion (hypothesis `ContDiffAt ℝ 6 a t₀` added to the *claims*, which
makes their refutation stronger). Work and Checked differ only in imports, namespace and the
module docstring (checked by `diff`).

Headline declarations: `cosmoCoeff`, `IsFlatLCDM` (definitions); `AvilesL0Claim`,
`AvilesM0Claim` (frozen printed claims); `avilesL0Claim_false`, `avilesM0Claim_false`
(refutations); `flatLCDM_coeffs` (correct q₀, j₀, s₀, l₀, m₀ for every Ω).

**SOURCE.** A. Aviles, C. Gruber, O. Luongo, H. Quevedo, PRD 86, 123516 (2012), arXiv:1204.2007v2
(only version listed). Typeset text verified by rendering p. 10 of the PDF and reading it
(`typeset/C2_aviles_v2_p10_eq15.png`), by the PDF text layer (pdftotext), and by two
summariser reads (v1 and v2). All four routes agree with the screen's transcription. Exact
quotes: `source_C2.md`.

**Plain words.** In the standard flat ΛCDM model the scale factor's derivatives today are fixed
by the matter fraction Ω_m. The paper prints l₀ = 1 + 3Ω_m − (27/2)Ω_m² and
m₀ = 1 − (27/2)Ω_m² − 81Ω_m² − (81/2)Ω_m³. The model gives l₀ = 1 + 3Ω_m + (27/2)Ω_m² and
m₀ = 1 − (27/2)Ω_m − 81Ω_m² − (81/4)Ω_m³. The printed q₀, j₀, s₀ are right.
**The paper's own Table V matches the correct formulas, not the printed ones** (with
Ω_m = 0.268 implied by its s₀ = −0.2061: correct l₀ = 2.774, m₀ = −8.827, exactly the table;
printed formulas would give 0.834, −6.568). So Eq. (15) is a misprint; the paper's numbers
are unaffected.

## 40.2 Blind restatement
Subagent given only `source_C2.md` (no Work/Checked/git). Its file: `Aviles_blind.lean`.
- Same definitions: H = ȧ/a, 1 + z = a(t₀)/a(t), coefficient = a⁽ⁿ⁾/(aHⁿ) via `iteratedDeriv`,
  minus sign on q only. Same model sentence, imposed on a neighbourhood of t₀.
- Same true values (its own sympy): l₀ = 1 + 3Ω + 27Ω²/2, m₀ = 1 − 27Ω/2 − 81Ω² − 81Ω³/4.
- Divergences: it assumes global `ContDiff ℝ 6 a`, `a t₀ = 1`, a free parameter H₀ > 0 and
  0 ≤ Ω ≤ 1; ours assumes C⁶ only at t₀, no normalisation, H₀ := H(t₀) > 0, any Ω.
  Classified **Underspecified** (source does not say where smoothness holds; its a₀ = 1 is
  "without loss of generality"). Ours is weaker in every hypothesis.
- Closed in Lean (`Work/Cosmography/AvilesAudit.lean`, namespace `BlindC2`, statements
  verbatim, checked by script): `BlindC2.lcdm_l0`, `BlindC2.lcdm_m0` are derived from
  `flatLCDM_coeffs`; `BlindC2.printedL0_false`, `printedM0_false` refute the printed claims in
  the restater's own reading, using a globally C⁶ glued Einstein–de Sitter scale factor
  `smoothTransition(4t − 1)·t^{2/3}`.

## 40.3 Sanity tests (`Work/Cosmography/AvilesAudit.lean`, `AvilesLCDM.lean`)
- Not vacuous: `eds_isFlatLCDM` (Ω = 1, a = t^{2/3}), `deSitter_isFlatLCDM` (Ω = 0, a = eᵗ),
  and the globally smooth `BlindC2.g_flat`.
- Bites on examples: theorem at Ω = 0 gives l₀ = m₀ = 1 (de Sitter, every coefficient 1); at
  Ω = 1 agrees with the independent direct computation `l0_eds` = 35/2, `m0_eds` = −455/4
  (5th/6th derivatives of t^{2/3} via descending Pochhammer).
- Near-miss: any value of l₀ other than 35/2 at Ω = 1 is refuted (example in audit file).
- Not trivial: needs the squared Friedmann identity, four successive differentiations of an
  eventually-zero polynomial in a, ȧ, …, a⁽⁶⁾, and a linear solve at t₀.
- Junk values: H₀ > 0 is a hypothesis of the model; a > 0 near t₀; the √ argument is shown
  positive near t₀ (it is 1 at t₀) before squaring; `iteratedDeriv` is genuine under
  `ContDiffAt ℝ 6 a t₀` (derivatives up to order 5 are differentiable near t₀). No ℕ
  subtraction, no log, no sSup.
- Types/quantifiers: real scale factor, two-sided neighbourhood; claims quantified over all
  Ω, a, t₀ satisfying the model, as Eq. (15) is stated for the model in general.
- Independent derivations: sympy (main session, `d/dt = aH d/da`), sympy (blind restater),
  sympy generator for the Lean proof (`scripts/gen.py`, solving successive derivatives of the
  polynomial identity) — three methods, same values.

**Classification:** Source error (misprint) in Eq. (15) for l₀ and m₀; one Underspecified
(smoothness domain) between readings, closed by proving both. No Translation errors found.

**Verdict: AUDITED.** Status of the C2 finding: Lean evidence and fidelity audit done;
remaining before it can be reported (FINDINGS protocol): referee subagent, prior-art check
(does anyone cite or reuse the wrong formula?), nanoda repair.

---

# Addendum: `Checked.Cosmography.AvilesWitness` (referee follow-up, same run)

Referee weakness: the refutation was machine-checked only at Ω = 1. Added (Work → Checked,
statements byte-identical apart from namespace/imports/docstring):
- `lam_isFlatLCDM`: a(t) = sinh(t)^{2/3} is flat ΛCDM at t₀ > 0 with Ω = 1/cosh²(t₀) (the
  standard ΛCDM solution with H₀-units scaled out); `exists_flatLCDM`: every Ω ∈ (0,1) has a
  C⁶ (indeed C^∞) model.
- `printedL0_false_at`: for every Ω ∈ (0,1), the Ω-instance of the frozen claim
  `AvilesL0Claim` is false. `printedM0_false_at`: same for m₀ at every Ω ∈ (0,1) with
  3Ω² + 2Ω − 2 ≠ 0 (the referee's exception Ω = (√7 − 1)/3, where printed and true m₀
  coincide).
- Fidelity: no new definitions; the statements are the frozen claims specialised to a fixed Ω
  (same `IsFlatLCDM`, `cosmoCoeff`, same printed polynomials), so the blind restatement above
  covers them. Not vacuous by construction (`exists_flatLCDM`). The m₀ exception is stated as
  an explicit hypothesis, not hidden. Junk values: none new (sinh t > 0 near t₀ > 0, so rpow
  and division are genuine).

**Verdict: AUDITED.**
