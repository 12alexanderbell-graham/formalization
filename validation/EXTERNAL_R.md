# External test, target R: Alpöge's claimed proof of RH and GRH (announced 2026-11-20)

Run 2026-11-27T0628Z (PROMPT, "TOP PRIORITY NOW … target R"). Blind: no review, certification,
dashboard, tracker, forum or news about this proof was read before this file's verdicts were committed.
Sources used: the note, the editions' Lean sources, Mathlib. (Locating the sources took two web searches
restricted to github.com/arxiv.org; their result titles were seen, no result page other than the
sources was opened; the mirror `tamnd/riemann-lean`'s SOURCE.md was read only for the alpo.ge URLs and
hashes, which were then checked against our own download.)

## Verdict

**Statement: DONE** for all four editions. **Proof: NOT DONE** — the 20 November archive cannot be replayed
here (blocker R1, below); the Sernau editions' replays are dispatched on GitHub (`external.yml`, lines
`R-sernau-compact`, `R-sernau-grh`), verdict on the proof when they finish. **No mismatch found** between
what the note claims and what the Lean states.

## Sources (pinned)

| edition | where | pin | size |
|---|---|---|---|
| note `remark.pdf` (4 pp., 20 Nov) | alpo.ge/remark.pdf | sha256 3fc97784…eb8d | text: `runs/2026-11-27T0628Z/R/sources/` |
| original archive (20 Nov) | alpo.ge/lean.tar.gz.part01–14 | tarball sha256 9631b4f0…7fc (equal to the mirror's published hash); Lean 4.33.1, Mathlib 0df444a | 175,212 files; closure of `Main`: 175,187 modules, 17,374,215 lines |
| Sernau `grh` (25 Nov) | github.com/lsernau/grh-lean, dir `grh` | 72fead1; Lean 4.35.0, Mathlib 56a0058 (= this repository's pin) | 803 modules, 477 k lines |
| Sernau `grh-compact` (25 Nov) | same repo, dir `grh-compact` | 72fead1 | 794 modules, 113 k lines |
| community cleanup | github.com/leanprover-community/riemann-hypothesis | 7c4ccbd (27 Nov; built on Sernau `grh`) | statements only compared |

"Condensed rewriting of 25 November" and "two shorter editions by Luke Sernau": the 25 November items found
are the two Sernau directories of one commit (72fead1, "Lean proof of GRH"); the community repository is
Kim Morrison's move of `grh` to a repository root the same day. If a different 25 November rewriting
exists, it was not found without reading commentary; recorded as open (R5).

## 1. Statement

All four editions state the five headlines with **byte-identical** `src/Statements.lean`
(sha256 79ef7ca7…47bf; the community copy differs only by the `module`/`public` header):
`RiemannHypothesis` (Mathlib's constant), `RiemannZetaZerosOnLine` (definitionally the same),
`DirichletLNonvanishingRightOfHalf` (all characters, all moduli, `re s > 1/2`, pole excluded),
`DirichletLZerosOnLine` (all characters, open strip), `PrimitiveDirichletLZerosOnLine`.

**Three blind readers** (A Opus, B Sonnet, C Haiku; brief da74d92 committed first; readings 8458a7e,
committed alone; C's own compile fix committed alone) wrote 10 readings from the note and the standard
definitions. **Every reading is proved equivalent to a frozen headline**
(`runs/2026-11-27T0628Z/R/closure/Closure.lean`, standard axioms only, coverage 10/10 by
`scripts/external/coverage.py`), except reader C's primitive reading with its own primitivity
definition, which is proved *implied* by the frozen statement (the direction that matters; the
converse needs C's definition of primitivity shown equal to Mathlib's — not needed, since C's
all-character reading closes both ways):

| reading | closure |
|---|---|
| A RH (not trivial, not 1) | `A_RH` ↔, by `not_exists` |
| A, B, C RH as "zeros in the open strip" | ↔ via `strip_iff_RH`, using `zeta_zero_in_strip` (functional equation `riemannZeta_one_sub`, Γ and ζ nonvanishing on `re ≥ 1`) |
| A GRH, B GRH', C GRH' (all characters, strip) | ↔ `DirichletLZerosOnLine` (`Iff.rfl` / argument order) |
| B GRH (primitive, strip) | ↔ `PrimitiveDirichletLZerosOnLine` (`Iff.rfl`) and ↔ all-characters (`prim_iff_all`: imprimitive L = primitive L × Euler factors, nonzero for `re > 0`) |
| A GRH' (primitive, all non-trivial zeros, trivial zeros by parity, s ≠ 1) | ↔ `DirichletLZerosOnLine` (`A_GRH'_iff`, via `dirichlet_zero_in_strip`: functional equation of `χ⁻¹`, gamma-factor zeros = trivial zeros) |
| C GRH (primitive by C's own definition) | frozen ⇒ reading (`frozen_C_GRH`) |
| half-plane headline | implied by the strip headline (`nonvanishing_of_strip`) |

**Definitions pinned** (`Pins.lean`): Mathlib's `riemannZeta` and `DirichletCharacter.LFunction χ` are,
on ℂ∖{1}, the unique holomorphic continuations of `∑ n^{-s}` and `∑ χ(n) n^{-s}` from `re s > 1`
(identity theorem). So no definition makes a headline easier than RH/GRH; the only junk value (at
s = 1) is excluded by every headline's hypotheses. Mathlib at the original's pin (0df444a) has the same
text for every `def` in the eight files defining ζ, Hurwitz ζ, L-functions, Dirichlet characters and
L-series (only a proof field of `hurwitzOddFEPair` differs).

**Hypotheses** (`Necessity.lean`): RH "not a trivial zero" NEEDED (ζ(−2) = 0); RH `s ≠ 1` REDUNDANT
(Mathlib's ζ(1) = (γ − log 4π)/2 ≠ 0); half-plane `1/2 < re s` NEEDED; strip `0 < re s` NEEDED (both
forms); primitive `re s < 1` REDUNDANT; `IsPrimitive` REDUNDANT (`prim_iff_all`). OPEN (R3): the
half-plane form's `χ ≠ 1 ∨ s ≠ 1` and the all-character strip form's `re s < 1` are redundant iff
Mathlib's junk value `LFunction (1 : DirichletCharacter ℂ N) 1` is nonzero for every N
(`ZL_lt_one_iff_junk`); either way the headline means GRH. Non-vacuity: the hypotheses hold exactly at
nontrivial zeros, whose existence (Hardy 1914) is not in Mathlib (R4); the hypotheses are not
contradictory by construction (each is shown needed or redundant on concrete points).

## 2. Coverage (claims of the note with no Lean statement)

All three readers, independently, flagged the same gaps:
- "the so-called **Generalized** Riemann Hypothesis": the Lean covers **Dirichlet L-functions only**.
  "GRH" also names the hypothesis for Dedekind, Hecke or automorphic L-functions; the note does not say
  which. If broader, it has no Lean statement. (The note calls the Dedekind case "Extended RH" and only
  expects it: "I expect, with more time".)
- "the qN = M k + R sign-only proof of **Weil and Deligne**" (p. 2): no headline states it.
- timeline item 17, "a significant weakening of **Vandiver**", footnote 6 (K-groups of Z, a belief):
  no headline.
- "formalized the arguments **without assumptions**": checked for the Sernau editions by the replay
  (pending) and by the scan below; for the original only by the scan (R1).
- Editions: no difference in the statements (byte-identical); the proofs are different texts
  (original 17.4 M lines; `grh` 477 k; `grh-compact` 113 k).

## 3. Proof (escapes and replay)

`scripts/external/scan_escapes.py` over each closure (`runs/2026-11-27T0628Z/R/scan/`): **no `sorry`,
`admit`, `axiom`, `native_decide`, `ofReduceBool`, `implemented_by`/`extern`, `#exit`** in any edition.
Hits: elaborator options only (`backward.isDefEq.respectTransparency`, `maxRecDepth`; not kernel
switches); original also has 1,814 custom-syntax lines (mostly `local notation`), two `partial def`
metaprograms (`CutCptCopy.lean` copies declarations with `addDecl`, which goes through the kernel;
`OwnStruct.lean`) and five `run_cmd` lines that only add library-suggestion deny-list entries.
No `addDeclWithoutChecking`, `skipKernelTC`, `#eval`, `initialize`, `unsafe`.

Replay (match against the frozen `Challenge`, axioms, nanoda, leanchecker in 4 shards, and our
readings/closures/pins/necessity built against each edition's own `Statements` module,
`FrozenIsStatements.lean`): dispatched for `R-sernau-compact` and `R-sernau-grh` (see run README for the
run id). **Proof verdict pending.**

## Blockers (also in `EXTERNAL_BLOCKERS.md`)

- R1 original archive replay: closure 175,187 modules / 17.4 M lines, Lean 4.33.1: beyond a GitHub job
  (T1's closure, 610 modules / 382 k lines, rebuilt in 34 min on one runner; scaled by lines ≈ 26 h, by modules ≈ 160 h, against a 6 h job limit) and the 10 GB Actions
  cache that carries builds across jobs. Infrastructure; the Sernau editions prove the identical statements.
- R3 junk value `LFunction 1 1` for N > 1 (two hypotheses' necessity open; meaning unaffected).
- R4 non-vacuity needs a nontrivial zero of ζ; Mathlib has none.
- R5 "condensed rewriting of 25 November" not identified beyond the Sernau/community editions.
