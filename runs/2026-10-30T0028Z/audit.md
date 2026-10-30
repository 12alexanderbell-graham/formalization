# Fidelity audit: `lookback_second_order` (target 1, milestone 1)

Frozen: commit `6ef1003`, `Work/Cosmography/Lookback.lean` (sha256 at freeze
`cda2aa7a7a986d716edf932ae03c1001f8e19951ee98751e31a8207e9c918a74`). Statement and the three
definitions are byte-identical between the freeze, `Work` and `Checked` (checked by diff).

**SOURCE.** Physlib `Physlib/Cosmology/FLRW/Distances.lean` TODO at commit
`2725b6f621901d4cd330869e9b77105045c1582e`: "prove its model-independent expansion
`t₀ - t = H₀⁻¹ [z - ½(2 + q₀) z² + …]`". M. Visser, Gen. Rel. Grav. 37 (2005) 1541,
arXiv:gr-qc/0411131, Eq. (11) with D = cΔt (Eq. 7). (Bibliographic details to be verified by
Alexander before any upstream use, per 47.1.)

**Plain words.** Light from a source left it at time t and arrives now (t₀). Its redshift z
is how much the universe has stretched since: 1 + z = a(t₀)/a(t). For nearby sources the
travel time is z/H₀, corrected at the next order by −(1 + q₀/2) z²/H₀, where q₀ says whether
the expansion is slowing down. The theorem says the error of this two-term formula is smaller
than any multiple of z² as the source gets close. It uses only how a(t) behaves near today;
no Einstein equations.

## 40.2 Blind restatement
Subagent given only the two source texts (no access to Work/, Checked/, git history).
Its statement (`runs/2026-10-30T0028Z/Lookback_blind.lean`):
- same definitions of H, z; its q = −(a''/a)·H⁻², proved equal to ours in Lean
  (`Work.CosmographyAudit.decel_eq_blind`, needs a(t₀) ≠ 0, a'(t₀) ≠ 0);
- same parametrisation (z as a function of emission time t, limit t → t₀, two-sided);
- same H₀ ≠ 0 hypothesis, a(t₀) > 0 (ours: ≠ 0, weaker);
- **divergence:** remainder O(z³) under `ContDiffAt ℝ 3 a t₀`, versus ours o(z²) under
  "a differentiable near t₀, a' differentiable at t₀". Neither implies the other.
- Resolution: **Underspecified** (40.4). The source's "+ …" does not fix the remainder. Ours
  is the minimal-hypothesis reading and matches Physlib's own `FLRW` structure (twice
  differentiable, no C²). The blind O(z³) reading is a separate, stronger-conclusion statement:
  recorded as milestone 1b, to be proved too, so both readings are covered.
- Same model, shared blind spots: this reduces, not removes, error (40.2).

## 40.3 Sanity tests (all in Lean, `Work/Cosmography/LookbackAudit.lean`, against the
`Checked` declarations)
- Not vacuous: hypotheses instantiated for de Sitter `a = exp` at 0 and `a = t²` at 1.
- Definitions bite: `hubble exp 0 = 1`, `decel exp 0 = -1`, `hubble t² 1 = 2`,
  `decel t² 1 = -1/2` (textbook: de Sitter q = −1; power law a ∝ tⁿ has H = n/t,
  q = (1 − n)/n).
- Bites on an example: `lookback_deSitter` is the second-order Taylor coefficient of
  log(1 + z) (exact de Sitter lookback is ln(1+z)/H₀).
- Near-miss 1 (`nearMiss_static`): drop a'(t₀) ≠ 0 → false for static a = 1.
- Near-miss 2 (`nearMiss_wrong_coefficient`): any coefficient other than 1 + q₀/2 is false
  (de Sitter, every k ≠ 1/2). So the statement pins the coefficient; it is not trivially
  satisfiable by a loose remainder.
- Not trivial: needs Peano Taylor at a point, a local inversion estimate (t − t₀ = O(z)) and
  remainder algebra; no single tactic closes it.
- Junk values: `a t = 0` cannot occur near t₀ (continuity + a(t₀) ≠ 0), and the filter only
  sees a neighbourhood; H₀ ≠ 0 and a'(t₀)² ≠ 0 are hypotheses; both derivatives used are
  genuine derivatives by hypothesis. No ℕ subtraction, no sqrt/log, no sSup.
- Types/quantifiers: real scale factor, real time, two-sided neighbourhood filter (stronger
  than past-only t < t₀).
- Independent numeric cross-check (exploratory, sympy): the lookback coefficient and all of
  Visser's d_L coefficients to z⁴ re-derived symbolically; all agree
  (`runs/2026-10-30T0028Z/cosmo.py`).

**Classification of fidelity issues found:** one Underspecified (remainder form). No
Translation errors. No Source errors.

**Verdict: AUDITED.**
