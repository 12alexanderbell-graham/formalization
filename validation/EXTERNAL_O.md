# External test, target O: the rest of OpenAI's 6 October release (github.com/openai/math)

PROMPT, queue after target R. Release pin 3344da59991ed94f9ba711217b29c1d760badfa6 (Lean 4.34.1, Mathlib
d13f23b). 425 comparator challenges (`lean/ComparatorChallenges/*.json`). Order: smallest challenge file
first; target S families skipped. Blind: no review, forum thread, blog or analysis of a family is read
before its verdict is committed. Readers: three models (Opus, Sonnet, Haiku) per family (item 2).

## Running table

| # | family (challenge) | verdict | finding |
|---|---|---|---|
| O1 | The Quasi-Riemann Hypothesis (`QuasiRiemannHypothesis`, `DirichletSevenEighths`, `HeckeSevenEighths`) | **NOT DONE** (statement: ζ and Dirichlet parts closed; Hecke part open; replay dispatched) | the two manuscripts state different theorems (7/8 on 30 Sep, 11/12 on 5 Oct); the Lean states 7/8 |
| O2 | Catalan's constant is irrational (`Catalan`) | **NOT DONE** (statement DONE: 7/7 readings closed; replay dispatched) | none at statement level; the L(2, χ₋₄) form proved equal to the frozen series in Lean |
| O3 | Kaplansky direct finiteness, characteristic two (`KaplanskyFinitelyPresented`) | **NOT DONE** (Theorem 1.1 closed 3/3; replay dispatched) | the manuscript's Gottschalk (surjunctivity) consequence, stated as proved, has no Lean statement in this family |
| O4 | The Euclidean plane is not five-colorable (`EuclideanFiveColor` + `PlaneColoring`) | **NOT DONE** (statement DONE: 9/9 closed with the family's two frozen statements; replays dispatched) | none: χ ≤ 7 (Isbell, cited by the manuscript) is the family's second challenge `properColoring_seven`; the first record of this row (χ ≤ 7 uncovered) was corrected the same run |
| O5 | The additive indecomposability of the primes (`OstmannPrimes`) | **NOT DONE** (statement DONE: 7/7 closed; replay dispatched) | none at statement level |
| O6 | A power saving for square-difference-free sets (`SquareDifference`) | **NOT DONE** (statement DONE: 6/6 closed; replay dispatched) | none at statement level; the frozen `C` is unconstrained and `c` is not bounded by 1, as in the source (readers B, C note c > 1 would make it false, so the theorem forces c ≤ 1) |
| O7 | A complete local domain without a small Cohen–Macaulay module (`SurfaceConeCandidateSupport`) | **NOT DONE** (0/9 readings closable) | **the family's only Lean statement does not state the claim**: it asserts that *some* complete Noetherian normal local domain of dimension 3 with residue field ℂ exists — any such ring (e.g. ℂ⟦x, y, z⟧) satisfies it — and says nothing about small Cohen–Macaulay modules; the manuscript's Theorem 1.1 and its disproof of the conjecture have no Lean statement |
| O8 | The Falconer distance conjecture in all dimensions (`FalconerAllDimensions`) | **NOT DONE** (statement DONE: 3/3 closed; replay dispatched) | none at statement level |
| O9 | The irrationality exponent of π is 2 (`PiExponent`) | **NOT DONE** (6/10 closed: μ(π) = 2 and the inequality, every reader; replay dispatched) | the abstract's consequence "the Flint–Hills series converges" has no Lean statement |
| O10 | An explicit noncoordinate polynomial with affine three-space zero fibre (`AbhyankarSathaye`) | **NOT DONE** (Corollary 1.2 closed 3/3; replay dispatched) | the headline Theorem 1.1 is about an explicit F; no Lean statement names F (the Lean states only the existential corollary). Tested here: the source's identity x² + y³ = h·s, F(P) = −1 and ∇F(P) = 0 at P = (2, 0, −1/2, 1/2) hold (Lean, `noncoord/check/Gradient.lean`) |
| O11 | A logarithmic independence bound for clique-free graphs (`CliqueFreeLog`) | **NOT DONE** (statement DONE: 3/3, frozen ⇒ reading; replay dispatched) | none at statement level |
| O12 | (second challenge of O4: `PlaneColoring.properColoring_seven`) | see O4 | — |
| O13 | An infinite finitely presented simple amenable group (`SimpleAmenable`) | **NOT DONE** (statement DONE: 3/3, frozen ⇒ reading; replay dispatched) | none at statement level |

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

## O2. Catalan's constant is irrational — NOT DONE (statement DONE, proof pending)

Run 2026-11-27T0628Z. Files: `runs/2026-11-27T0628Z/O/catalan/` (brief 850f128, readings 8e422fa).
Claim (introduction.tex, sha256 dfef42bb…): G = β(2) = Σ (−1)^j/(2j+1)², "Catalan's constant is
irrational". Frozen: `Irrational (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)`.
Readers A, B, C: 7 claim theorems (G irrational; β(2) irrational; L(2, χ₋₄) = G; L(2, χ₋₄) not rational;
L(2, χ₋₄) a real irrational). **All 7 closed** (`closure/Closure.lean`), including a proof here that
Mathlib's `LSeries` of `ZMod.χ₄` at 2 equals the frozen series (`catalan_LSeries`), so the statement is
about the constant the source names, by any of its three definitions. Each reader proved its series
summable (so `tsum` is not a junk 0). Replay line `O-catalan` dispatched.

## O3. Kaplansky direct finiteness in characteristic two — NOT DONE

Run 2026-11-27T0628Z. Files: `runs/2026-11-27T0628Z/O/kaplansky2/` (brief 850f128, readings 8e422fa).
Claim (01-introduction.tex, sha256 4abc0e82…): Theorem 1.1 (finite field of characteristic two,
finitely presented group with an element of odd prime order, a·b = 1 ≠ b·a in K[G]); and (lines 47–51)
"It gives a negative resolution of Gottschalk's conjecture for the group in Theorem 1.1", the transfer
"proved in full" in a later section. **Theorem 1.1: closed 3/3** (frozen ⟺ each reading; Fintype vs
Finite, "odd prime" vs "prime ≠ 2"). **Not closed: the Gottschalk consequence** — no comparator
challenge of this family states it (the odd-characteristic family's `OddKaplansky.MainClaim` does, with
`cellular b` injective and not surjective). A claim stated as proved with no Lean statement: reported, not
a mismatch of the Lean. Also not formalizable as stated: "specified by a terminating prescription"
(effectivity; reader A). Replay line `O-kaplansky2` dispatched.

## O4–O6 (run 2026-11-27T0628Z; brief 4fd330c, readings ee3c89e; files `runs/2026-11-27T0628Z/O/{plane5,ostmann,sqdiff}/`)

**O4, plane five-coloring.** Claim (introduction.tex, sha256 41222c5b…): "The Euclidean plane has no proper
five-coloring, even when arbitrary color classes are allowed. Consequently, 6 ≤ χ(ℝ²) ≤ 7." Frozen: no
`ℂ → Fin 5` with `‖p − q‖ = 1 → c p ≠ c q`. Closed (`closure/Closure.lean`, transport by the linear isometry
`Complex.orthonormalBasisOneI.repr` to `EuclideanSpace ℝ (Fin 2)`): each reader's no-five-coloring ⟺ frozen
(A with colours `Icc 1 5`, B with `dist`, C with `Fin 5`), and C's "no k < 6 works" ⇐ frozen. Uncovered
(5 of 9): every reading containing χ ≤ 7 — Isbell's seven-coloring, cited by the manuscript, not proved there
and not in any frozen statement. The solution closure is small: 70 files, 30,336 lines, no escape hits.

**O5, Ostmann.** Frozen: `A.Nontrivial → B.Nontrivial → ((A + B) ∆ primes).Infinite` on `Set ℕ`. 7/7 readings
closed (encard ≥ 2 ⟺ Nontrivial; explicit sumset = pointwise `+`; the "Equivalently" and intro forms follow).
The manuscript's Theorem 2.x ("two infinite summands") was outside the excerpt; its Lean counterpart, if any,
is not a headline. Closure: 4,358 files, 364,516 lines, imports PrimeNumberTheoremAnd and StrongPNT
(required at the manifest's revisions); 161 custom-syntax hits, no other.

**O6, square-difference-free sets.** Frozen: `∃ c C, 0 < c ∧ ∀ N ≥ 1, ∀ A ⊆ [1, N] (Finset ℤ),
square-difference-free → |A| ≤ C N^(1−c)`. 6/6 closed (A both ways on `Finset ℤ`; B, C on `Finset ℕ` via the
cast, frozen ⇒ reading; the "Equivalently" forms as contrapositives with the same constants). Closure: 81 files,
24,221 lines, no escape hits.

Escape scans of O2–O6 closures: `runs/2026-11-27T0628Z/O/scan/` (O2: 988 files, 574,902 lines, imports
PrimeNumberTheoremAnd; O3: 126 files; none with sorry/axiom/native_decide).

## O7–O9 (run 2026-11-27T0628Z; brief f0cdc21, readings 194ff62; files `runs/2026-11-27T0628Z/O/{smallcm,falconer,piexp}/`)

**O7, small Cohen–Macaulay modules — a coverage finding.** Claim (paper.tex, sha256 76d8de92…): Theorem 1.1, "There
exists a three-dimensional complete Noetherian normal local domain R containing ℂ, with residue field ℂ, such that
no nonzero finitely generated R-module has depth three", which "disproves the domain form of the small
Cohen–Macaulay module conjecture". The family's only comparator challenge, `OAI.SmallCM.candidate_ring_properties`,
states the existence of a ring with the listed ring-theoretic properties and nothing about modules. Its solution
(11 files, 7,844 lines) uses the paper's completed cone ring as the witness, but the *statement* is met by any
regular complete local ℂ-algebra of dimension 3 (ℂ⟦x,y,z⟧; classical, not proved here in Lean — Mathlib lacks
Krull dimension and completeness of multivariate power series). All 9 reading theorems of the three readers
(the theorem, the disproof of the conjecture, and the conjecture as a `Prop`) are UNCOVERED. What the release's
Lean certifies for this family is a support lemma, not the result.

**O8, Falconer.** Frozen: `∀ d ≥ 2, ∀ E compact ⊆ EuclideanSpace ℝ (Fin d), (d : ℝ≥0∞)/2 < dimH E →
0 < volume {r | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}`. 3/3 closed both ways. Closure: 2,384 files, 185,097 lines,
no escape hits.

**O9, π.** Frozen: the "more precisely" inequality (with `2 ≤ Q`) ∧ `sSup {ν > 0 | infinitely many r : ℚ with
den ≥ 2 and 0 < |π − r| < den^(−ν)} = 2` (real `sSup`). Closed for every reader: the inequality (readers A, C add
`0 < q`, implied) and μ(π) = 2 in each reader's form (A: `EReal` sSup and `IsLUB`; B: `EReal`; C: `ℝ≥0∞` iSup) —
a real `sSup` equal to 2 forces the set nonempty and bounded, and rationals of denominator ≥ 2 correspond to
coprime pairs (p, q), q ≥ 2 (`pairs_eq_image`, `SP_eq_SF`). Uncovered: the abstract's Flint–Hills corollary
(no Lean statement). Closure: 869 files, 94,948 lines, no escape hits.

## O10 (run 2026-11-27T0628Z; brief f3fee82, readings b1b49e5; files `runs/2026-11-27T0628Z/O/noncoord/`)

Claim (paper.tex, sha256 60993c0b…): Theorem 1.1 — for the explicit F of (eq:xyz)–(eq:F) in ℂ[h,u,v,w],
R/(F) ≅ ℂ^[3] and ∇F(2, 0, −1/2, 1/2) = 0, so F is not a coordinate; Corollary 1.2 — for every n ≥ 4 some
f ∈ ℂ[z₁,…,zₙ] has ℂ[z]/(f) ≅ ℂ^[n−1] and is not a coordinate. Frozen: Corollary 1.2 only. Closed: every
reader's corollary (A, C both ways; B, whose "coordinate" uses the first variable only, frozen ⇒ reading), and
reader C's identity x² + y³ = h·s. Uncovered: the readings of Theorem 1.1 (9 of 13). **Small-case test of the
manuscript (this run, Lean, standard axioms):** typed from the TeX, F has x² + y³ = h·s identically, F(P) = −1,
and each partial derivative of F vanishes at P (`deriv_h/u/v/w` via the exact cofactor identities
F(P + t eᵢ) = −1 + t²·Gᵢ(t), checked by `ring`) — the stated critical point is right. Solution closure:
15 files, 1,445 lines, no escape hits.

## O4 corrected; O11–O13 (run 2026-11-27T0628Z; brief 877840e, readings 0b756ff)

**O4, corrected.** The family has a second comparator challenge, `PlaneColoring.properColoring_seven` (a
seven-colouring of `EuclideanSpace ℝ (Fin 2)`, the cited Isbell bound; solution 9 files, 519 lines). With both
frozen statements every reading closes (`plane5/closure/ClosureBounds.lean`: A's χ as least colourable n, its
unpacked form and its Mathlib `chromaticNumber` form of the unit-distance graph, B's `IsLeast` form, C's
seven-colourability). `replay.sh` gained `@Module` EXTRA entries (an outside module copied and built with the
closure) so one closure can combine a family's two frozen statements on one replay line (`O-plane7`).

**O11, K_r-free graphs.** Frozen: `∀ r ≥ 4, ∃ c > 0, ∀ V G, G.CliqueFree r → 2 ≤ averageDegree G →
c n log d / d ≤ G.indepNum` (`averageDegree = 2|E|/n`). Closed frozen ⇒ each reading (A: own indepNum as a
`Finset.sup`, own edge count over `Sym2`, own K_r-freeness; B: an independent set of that size, `Nat.card` of
the edge set, an explicit `0 < n`; C: own α and K_r-freeness): edge counts and average degrees equal,
`CliqueFree` from each reader's form, Mathlib's `indepNum` realised by an independent set. Solution closure:
31 files, 5,539 lines, no escape hits — small for the claim (the log log d factor of Shearer's bound removed
for every r ≥ 4); the replay decides whether it checks.

**O13, simple amenable group.** Frozen: `∃ G, Infinite G ∧ Group.IsFinitelyPresented G ∧ IsSimpleGroup G ∧
FolnerAmenable G` (the source's Følner condition). Closed frozen ⇒ each reading (finite presentation via
`exists_mulEquiv_presentedGroup`; simplicity with and without nontriviality; the Følner sets with the readers'
symmetric differences). Solution closure: 550 files, 84,848 lines, 6 custom-syntax hits.
