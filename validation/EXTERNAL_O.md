# External test, target O: the rest of OpenAI's 6 October release (github.com/openai/math)

PROMPT, queue after target R. Release pin 3344da59991ed94f9ba711217b29c1d760badfa6 (Lean 4.34.1, Mathlib
d13f23b). 425 comparator challenges (`lean/ComparatorChallenges/*.json`). Order: smallest challenge file
first; target S families skipped. Blind: no review, forum thread, blog or analysis of a family is read
before its verdict is committed. Readers: three models (Opus, Sonnet, Haiku) per family (item 2).

## Running table

| # | family (challenge) | verdict | finding |
|---|---|---|---|
| O1 | The Quasi-Riemann Hypothesis (`QuasiRiemannHypothesis`, `DirichletSevenEighths`, `HeckeSevenEighths`) | **NOT DONE** (statement: ζ and Dirichlet parts closed; Hecke part open; replay dispatched) | the two manuscripts state different theorems (7/8 on 30 Sep, 11/12 on 5 Oct); the Lean states 7/8 |

## O1. The Quasi-Riemann Hypothesis — NOT DONE

Run 2026-11-27T0628Z. Files: `runs/2026-11-27T0628Z/O/qrh/`.

**Claims** (TeX, verbatim excerpts in `sources/`): 30 Sep (paper.tex, sha256 42a5ee0f…): "Every
finite-order Hecke L-function over F = Q(√−3) has no zero in Re s > 7/8. The same holds for every
Dirichlet L-function, including ζ(s). A pole at s = 1 for a principal character is allowed."
5 Oct (paper2.tex, sha256 d9a8f15a…): the same with **11/12**, Dirichlet L-functions defined for
**primitive** characters, plus "this rules out the existence of Landau–Siegel zeros".

**Frozen Lean statements** (three challenges, one family): ζ ≠ 0 for Re s > 7/8; every
`DirichletCharacter ℂ q` (all moduli, imprimitive included), `LFunction χ s ≠ 0` for Re s > 7/8 unless
χ = 1 ∧ s = 1; the release's own `HeckeFamily.LFunction χ ≠ 0` for Re s > 7/8 unless residue = 1 ∧ s = 1.

**Blind readings** (brief 0cd0d4b first; readings b3038bb alone): 3 readers × (ζ, Dirichlet all
characters, Dirichlet primitive, Hecke over Q(√−3) via every holomorphic f on ℂ∖{1} equal to the ideal
series on Re s > 1). All three independently found the edition difference (7/8 vs 11/12; all vs
primitive characters; pole sentence only on 30 Sep).

**Closed** (`closure/ClosureZeta.lean`, `closure/ClosureDirichlet.lean`, standard axioms, checked
locally against this repository's Mathlib; in the release's pin by the replay): every reader's ζ
reading at 7/8 ⟺ frozen (s = 1 covered by Mathlib's ζ(1) ≠ 0); every reader's all-character Dirichlet
reading at 7/8 ⟺ frozen; every reader's 11/12 readings (ζ, primitive Dirichlet) ⇐ frozen.

**Not closed (the blocking link):** the Hecke conjunct of every reading. The frozen statement uses the
release's own `Character` (a `MulChar (𝓞 ⧸ 𝔪) ℂ` trivial on units, with a period) and `LFunction`
(a theta-lattice Mellin construction `π^s Γ(s)⁻¹ Λ(s) / 6`). The release's library contains the bridges
a closure needs (`LFunction_eq_series`/`LFunction_eq_ideal_tsum` for Re s > 1, `continuedLattice_hasSum`,
`continuedLattice_differentiableAt` for s ∉ {0, 1}, `normForm x y = x² − xy + y²` with
`normForm_eq_absNorm_span`); missing is the correspondence between the readers' ray-class characters and
the release's `Character` (class number one of ℤ[ω], units of order 6). `coverage.py`: 0/6 reading
theorems closed (each is a conjunction with the Hecke part).

**Proof:** closure of the solution modules: 2,925 modules, 486,558 lines; imports two outside packages
(PrimeNumberTheoremAnd, rellich-kondrachov) — `replay.sh` now requires such packages at the release
manifest's pinned revisions (general fix, this run). Escape scan (`scan/closure.txt`): no `sorry`,
`axiom`, `native_decide`, `implemented_by` in the 2,926 files of the release's own closure (2,884
custom-syntax lines, local notation); the outside packages' 3 imported modules are not scanned (the
replay's axiom check covers them). Replay lines `O-qrh-zeta`, `O-qrh-dirichlet`, `O-qrh-hecke`
dispatched (run id in the run README).

**Consistency with target R:** Alpöge's frozen `DirichletLNonvanishingRightOfHalf` would imply the
release's Dirichlet and ζ statements at 7/8 (one-line Lean implication; not needed for either verdict).
