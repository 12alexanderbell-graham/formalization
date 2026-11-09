# Brief: blind clause reader for the pinned definitions (run 2026-11-09T0228Z)

**Purpose (fixed before any red team of this run ran).** The program generates the claim of every headline
(`CLAIMS.md`) from its Lean statement. The only hand-written words in it are the *phrases* of 23 pinned
definitions. Their names (P6), the role of every argument (P3) and 13 sign conventions (P4) already come from blind
readers. Everything else a phrase says — units, which named quantity is which order or which coefficient, which
species react to which, on which domain or neighbourhood a law holds — is still written by the author, and blind
red team Z showed it can be falsified unnoticed (it deleted "minus" in "the deceleration parameter is minus the order 2
coefficient"). Planned rule **P7 (coverage)**: every word and number of a phrase must lie inside a text written by a
blind reader (the NAME; a ROLE immediately before its argument; a SIGN or CLAUSE line, word for word) or be one of a
fixed list of connectives (the a an of at for in on with and or by from to obeys holds satisfies solves; punctuation).
You write the CLAUSE lines. Your answers will be compared mechanically with text written by someone else.

You are a blind reader. Read the specification and pinning theorem of each definition below and write the short
plain-English clauses that a scientist needs, besides the definition's name and the roles of its arguments, to read
its Lean body correctly.

## What you may read
- `Checked/Fidelity/*.lean`, `Checked/Sim/DuffingPin.lean`, `Checked/Sim/MMPin.lean`, `Checked/Sim/RobPin.lean`
  (the specifications and pinning theorems; find each pin theorem below with grep).
- The Lean source of each definition (its signature and body) under `Checked/` (find it with grep), and the Lean
  sources it uses.

## What you must NOT read
`scripts/` (everything in it), every `*.md` file in the repository other than this brief (README, STATE, CLAIMS,
TRUST_MAP, TRUSTED_DEFINITIONS, FINDINGS, LEDGER, CHANGELOG, …), `validation/`, `runs/` (except this folder), `Work/`,
`_archive/`, and the git history. Do not use the web. Lean docstrings (`/-- … -/`) of the program definitions
themselves are author text: do not take clauses from them; the specification's own fields, laws and docstrings are
blind text you may use.

## The definitions (Lean name · binders in order · pinning theorem)
1. `Checked.Cosmography.hubble` · a t · `hubbleSpec_pins`
2. `Checked.Cosmography.decel` · a t · `decelSpec_pins`
3. `Checked.Cosmography.BambaK.lumDist` · K a t₀ t · `lumDistSpec2_pins`
4. `Checked.Cosmography.BambaA.angDist` · K a t₀ t · `angDistSpec_pins`
5. `Checked.Cosmography.Aviles.IsFlatLCDM` · Ω a t₀ · `flatLCDMSpec2_pins`
6. `Checked.Cosmography.redshift` · a t₀ t · `redshiftCore_pins`
7. `Checked.Cosmography.Aviles.cosmoCoeff` · n a t · `cosmoCoeffCore_pins`
8. `Checked.Cosmography.BambaY.yred` · a t₀ t · `yRedSpec_pins`
9. `Checked.Cosmography.BambaK.omega0` · K a t₀ · `omega0Spec_pins`
10. `Checked.Cosmography.BambaZ.curvK` · K a t₀ · `curvKSpec_pins`
11. `Checked.Cosmography.BambaY.lumDistFlat` · a t₀ t · `lumDistFlat_pins`
12. `Checked.Cosmography.BambaY.comoving` · a t₀ t · `comoving_pins`
13. `Checked.Cosmography.CPL.IsFlatCPL` · Ω w₀ wₐ a t₀ · `flatCPL_pins`
14. `Checked.Cosmography.FRCosmo.curv` · a t · `ricciSpec_pins`
15. `Checked.Cosmography.FRCosmo.rhoM` · Ω a t₀ t · `rhoM_eq_dust`
16. `Checked.Cosmography.FRCosmo.FriedmannEq` · Ω a F t₀ t · `friedmannEq_iff_blind`
17. `Checked.Cosmography.FRCosmo.MasterEq` · Ω a F t₀ t · `masterEq_iff_blind`
18. `Checked.Cosmography.Transverse.transverse` · K χ · `transverseSpec_pins`
19. `Checked.Chemistry.CubicEOS.IsCriticalIsotherm` · p v · `criticalSpec_pins`
20. `Checked.Chemistry.Coexistence.IsMaxwellCoexistence` · p vl vg ps · `maxwellSpec_pins`
21. `Checked.Sim.Duffing.IsDuffingSolution` · k β x₀ v₀ T x · `duffingSpec_pins`
22. `Checked.Sim.MichaelisMenten.IsMMSolution` · k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p · `mmSpec_pins`
23. `Checked.Sim.Robertson.IsRobSolution` · k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃ · `robSpec_pins`

## What a clause should say
For each definition, 0 to 6 clauses, each a fact the specification or pinning theorem fixes, for example (forms
only, not answers): the unit convention ("units in which X is one"); a relation to another named quantity ("the
named parameter P is minus the order k coefficient"); which named letters stand for which orders; for a reaction
network, which species react to which, and with which rate constant; for an equation, which equation it is and how
it is normalised; on which domain or neighbourhood a law is required to hold; for a sign, what positive and negative
mean. Every clause must be true according to the specification (or, where the specification is silent, the Lean
body). Prefer clauses that would *change the reading* if a word were deleted or swapped (a sign, an order, a
species, a direction of reaction); skip clauses that only repeat the name or the arguments' roles.

## Output (write exactly one file: `runs/2026-11-09T0228Z/clauses/CLAUSES.txt`)
One line per clause, definitions in the order above:

    CLAUSE | <full Lean name> | <clause>

- `<clause>`: plain English, 3 to 14 words, lowercase except proper names, named letters, Greek letters and chemical
  species letters; **no formula characters at all** (none of = + / · * √ ′ ″ ^ ² ³ < > ≤ ≥ − × and no hyphen-minus
  except between two letters; write "minus", "times", "over", "squared"); digits only as numbers (orders, counts),
  never as part of a formula; no article at the start; no semicolon or comma inside a clause (split it instead).
- Do not repeat a clause for several definitions unless the specification of each fixes it.

At the end, a line `END` and a one-paragraph note (after `END`) on anything you could not decide.
