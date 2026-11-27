# External test, target O: the rest of OpenAI's 6 October release (github.com/openai/math)

PROMPT, queue after target R. Release pin 3344da59991ed94f9ba711217b29c1d760badfa6 (Lean 4.34.1, Mathlib
d13f23b). 425 comparator challenges (`lean/ComparatorChallenges/*.json`). Order: smallest challenge file
first; target S families skipped. Blind: no review, forum thread, blog or analysis of a family is read
before its verdict is committed. Readers: three models (Opus, Sonnet, Haiku) per family (item 2).

## Running table

| # | family (challenge) | verdict | finding |
|---|---|---|---|
| O1 | The Quasi-Riemann Hypothesis (`QuasiRiemannHypothesis`, `DirichletSevenEighths`, `HeckeSevenEighths`) | **NOT DONE** (statement: ζ and Dirichlet parts closed; Hecke part open; proofs of `DirichletSevenEighths` and `HeckeSevenEighths` PASSED with the dependency patches (nanoda 125,027 / 124,996 declarations), leanchecker running; `QuasiRiemannHypothesis` replay pending) | **1248Z: disclosed** (CONTENTS 003: "A companion gives a different proof of the zero-free half-plane Re s > 11/12"; the Lean states the stronger 7/8) — not a finding. the two manuscripts state different theorems (7/8 on 30 Sep, 11/12 on 5 Oct); the Lean states 7/8 |
| O2 | Catalan's constant is irrational (`Catalan`) | **NOT DONE** (statement DONE: 7/7; replay with OpenAI's dependency patch PASSED: match, axioms, nanoda 88,413 declarations, coverage COMPLETE (run 45973479628); leanchecker pending) | none at statement level; the L(2, χ₋₄) form proved equal to the frozen series in Lean |
| O3 | Kaplansky direct finiteness, characteristic two (`KaplanskyFinitelyPresented`; second challenge `KaplanskyDirectFiniteness`, the f.g. form, replay line O-kaplansky2-fg) | **NOT DONE** (Theorem 1.1 closed 3/3; replay PASSED: match, axioms, nanoda 82,359 declarations, leanchecker 3 of 4 shards OK, 4th running) | **1248Z: reclassified.** Gottschalk's conjecture *is* refuted in the family's Lean: `OddKaplansky` (same scope document `docs/197.md`) states an injective, non-surjective cellular automaton; only the char-2 paper's own corollary for its G is unstated (scope document silent: undisclosed, minor). **New finding (index, undisclosed):** CONTENTS item 197 and the title of `docs/197.md` present "a finitely presented torsion-free nonsofic group whose group algebra over 𝔽₂ is not directly finite … even without torsion" under the Lean link; none of the family's four Lean statements says torsion-free or 𝔽₂ — `KaplanskyFinitelyPresented.lean:10` asserts an element of odd prime order, the field is any finite field of characteristic 2, and the torsion-free paper (4 Oct) is not among the document's papers. the manuscript's Gottschalk (surjunctivity) consequence, stated as proved, has no Lean statement in this family |
| O4 | The Euclidean plane is not five-colorable (`EuclideanFiveColor` + `PlaneColoring`) | **NOT DONE** (statement DONE: 9/9 closed with the family's two frozen statements; replays PASSED for both: `no_proper_five_coloring` nanoda 82,222 declarations, `properColoring_seven` nanoda 18,649, coverage COMPLETE on O-plane7; leanchecker shards running) | none: χ ≤ 7 (Isbell, cited by the manuscript) is the family's second challenge `properColoring_seven`; the first record of this row (χ ≤ 7 uncovered) was corrected the same run |
| O5 | The additive indecomposability of the primes (`OstmannPrimes`) | **NOT DONE** (statement DONE: 7/7; replay with the dependency patches PASSED: match, axioms, nanoda 148,846 declarations, coverage COMPLETE; leanchecker queued; second challenge `OstmannComplete` dispatched) | none at statement level |
| O6 | A power saving for square-difference-free sets (`SquareDifference`) | **NOT DONE** (statement DONE: 6/6 closed; match and axioms PASSED, closures' axioms standard; nanoda crashed on a stack overflow (ours: its threads' 32 MiB default), re-dispatched with 1 GiB) | none at statement level; the frozen `C` is unconstrained and `c` is not bounded by 1, as in the source (readers B, C note c > 1 would make it false, so the theorem forces c ≤ 1) |
| O7 | A complete local domain without a small Cohen–Macaulay module (`SurfaceConeCandidateSupport`) | **NOT DONE** (0/9 readings closable; the frozen statement's proof PASSED: match, axioms, nanoda 63,751 declarations; readings do not elaborate under OpenAI's Mathlib pin (no `IsLocalRing.depth`)) | **1248Z: disclosed** (`docs/195.md`: "verifies only the ring-theoretic candidate … does not assert the absence of small Cohen–Macaulay modules") — a disclosed scope limit, not a mismatch; the fact below stands, the word finding does not. **the family's only Lean statement does not state the claim**: it asserts that *some* complete Noetherian normal local domain of dimension 3 with residue field ℂ exists — any such ring (e.g. ℂ⟦x, y, z⟧) satisfies it — and says nothing about small Cohen–Macaulay modules; the manuscript's Theorem 1.1 and its disproof of the conjecture have no Lean statement |
| O8 | The Falconer distance conjecture in all dimensions (`FalconerAllDimensions`; second challenge `PlanarFalconer`, the d = 2 case, replay line O-falconer-planar) | **NOT DONE** (statement DONE: 3/3; replay PASSED: match, axioms, nanoda 87,904 declarations, coverage COMPLETE; leanchecker running; second challenge `PlanarFalconer` PASSED incl. leanchecker, nanoda 70,239) | none at statement level |
| O9 | The irrationality exponent of π is 2 (`PiExponent`) | **NOT DONE** (6/10 closed: μ(π) = 2 and the inequality, every reader; replay PASSED: match, axioms, nanoda 118,090 declarations; leanchecker pending) | **1248Z: disclosed** (`docs/017.md`: "The paper's convergence consequence for the Flint–Hills series is outside this selected statement") — not a finding. the abstract's consequence "the Flint–Hills series converges" has no Lean statement |
| O10 | An explicit noncoordinate polynomial with affine three-space zero fibre (`AbhyankarSathaye`) | **NOT DONE** (Corollary 1.2 closed 3/3; replay PASSED, run 45967351577) | the headline Theorem 1.1 is about an explicit F; ~~no Lean statement names F (the Lean states only the existential corollary)~~ **withdrawn 1248Z: wrong** — `CommutingDerivations` (same scope document `docs/049.md`) defines the manuscript's F term by term and states, at n = 4, that it is not a coordinate; every reader's "F is not a coordinate" closed against it (`runs/2026-11-27T1248Z/O/noncoord/Closure.lean`, standard axioms, replay line O-noncoord-cd). Still unstated for the named F: R/(F) ≅ ℂ^[3] (scope document silent: undisclosed, minor; the existential Corollary 1.2 is stated). Tested here: the source's identity x² + y³ = h·s, F(P) = −1 and ∇F(P) = 0 at P = (2, 0, −1/2, 1/2) hold (Lean, `noncoord/check/Gradient.lean`) |
| O11 | A logarithmic independence bound for clique-free graphs (`CliqueFreeLog`) | **DONE pending leanchecker** (statement DONE: 3/3, frozen ⇒ reading; replay PASSED: match, axioms, nanoda 46,877 declarations, coverage COMPLETE; leanchecker shards pending) | none at statement level; a 5.5k-line proof of a bound removing Shearer's log log d factor for every r ≥ 4 checks |
| O12 | (second challenge of O4: `PlaneColoring.properColoring_seven`) | see O4 | — |
| O13 | An infinite finitely presented simple amenable group (`SimpleAmenable`) | **NOT DONE** (statement DONE: 3/3; replay PASSED with the closure fixed for OpenAI's pin: nanoda 96,392 declarations, coverage COMPLETE; leanchecker queued) | none at statement level |
| O14 | An exponential bound for sunflowers (`Sunflower`) | **NOT DONE** (3/7: every reader's qualitative Theorem 1.1 closed; replay dispatched) | **1248Z: disclosed** (`docs/379.md` § Sunflowers: "the paper's threshold B_r^k … remains unformalized") — not a finding. the manuscript's explicit B_r = 2^{C H⁴ L^{5/2}} with an absolute C has no Lean statement: the Lean states only that some base C(r) exists (the Erdős–Rado sunflower conjecture itself) |
| O15 | Real Littlewood polynomials are asymptotically minimal (`AsymptoticallyMinimalLittlewood`) | **DONE** (statement DONE: 6/6 — the "Equivalently" form and, with the lower bound proved here, the "lim m_N = 1" form, every reader; replay PASSED: match, axioms, nanoda 62,941 declarations, leanchecker 4/4 shards, coverage COMPLETE, run 45974543330) | the Lean states only the upper bound; the headline limit also needs m_N ≥ 1, which the source cites as known — proved here in Lean (discrete orthogonality at the N-th roots of unity), so the frozen statement does imply the headline |
| O16 | The dyadic case of the Erdős similarity conjecture (`DyadicAvoidance`) | **NOT DONE** (statement DONE: 5/5; replay PASSED: match, axioms, nanoda 39,826 declarations, coverage COMPLETE; leanchecker pending) | **1248Z: new finding (index, undisclosed):** CONTENTS item 084 ("For every fixed q ∈ (0,1) … resolves the geometric-progression case … for every ratio") and the title of `docs/084.md` ("The geometric case …") sit on the Lean link; the only Lean statement (`DyadicAvoidance`) is hard-wired to 2⁻ⁿ and the geometric paper (5 Oct) is not among the document's papers; its scope text says "proves the dyadic case" but nowhere that general q is not formalized. none at statement level |
| O17 | Almost-everywhere Fourier convergence in L log L (`FourierLLogL`) | **DONE** (statement DONE: 3/3; replay PASSED: match, axioms, nanoda 60,516 declarations, leanchecker 4/4, coverage COMPLETE; run 45978039795) | none at statement level: every reader's normalised measure is Mathlib's `haarAddCircle`, every reader's e^{ikx} is `fourier k`, so coefficients and partial sums are the frozen ones; the frozen hypothesis (integrability of ‖f‖ log(2+‖f‖)) follows from the readers' (lower integral < ∞) |
| O18 | A power saving for planar unit distances (`PlanarUnitDistances`) | **DONE** (statement DONE: 6/6, both forms; replay PASSED: match, axioms, nanoda 75,221 declarations, leanchecker 4/4, coverage COMPLETE; run 45978039795) | none at statement level: the readers' counts (2-element subsets for A and C, `Sym2` for B) proved equal to the frozen `Sym2` count |
| O19 | A universal group of type F∞ (`UniversalFInfinity`) | **NOT DONE** (3/7: Theorem 1.1 closed for every reader; proof replay PASSED incl. leanchecker 4/4, nanoda 58,001 declarations) | **1248Z: disclosed** (`docs/250.md`: "The paper's converse about recursively presented subgroups is not included") — not a finding. Corollary 1.2 (f.g. G embeds in H iff recursively presented) has no Lean statement; it rests on Higman's embedding theorem, not in Lean |
| O20 | The symmetric Mahler conjecture and its equality cases (`MahlerConjecture`) | **NOT DONE** (4/6: the inequality for every reader; reader A's equality case against `SymmetricMahlerEquality` (B, C: Euclidean transport not written); replays dispatched) | ~~the equality case has no Lean statement~~ **withdrawn 11:07Z: wrong** — the family has a second challenge, `SymmetricMahlerEquality` (54 lines, `OAI.Analysis.Mahler.Classification`), stating it; closure against it pending |
| O21 | A classification of finite Euclidean Ramsey configurations (`EuclideanRamseySpherical`, `…Circle`, `…Transitive`) | **NOT DONE** (5 of 12 claim readings closed: every reader's necessity (iii), reader B's circle (ii), reader B's Classification against `EuclideanRamsey.classification`; replays dispatched) | **1248Z:** the family has **seven** challenges (`docs/172.md`), not six: `GrahamSpherical` (the twelve-point non-Ramsey set, Proposition cons:twelve) was missed by `family_challenges.py`'s count; Corollary cons:kites' "not subtransitive" is cited (Leader–Russell–Walters), not proved by the paper. ~~the headline Classification theorem has no Lean statement~~ **withdrawn 11:07Z: wrong** — the family has six challenges; `EuclideanRamsey.classification` (52 lines) states the Classification, and `EuclideanRamseyNine`, `EuclideanRamseyQuadratic` state further consequences; closures against them pending. (Original text: the release states three consequences (a Ramsey set is cospherical — the classical 1973 theorem the paper cites —, at most five points on a circle are Ramsey, subtransitive sets are Ramsey); readers A and C's circle form (in ℝ^m) and every reader's subtransitive form not closed this run |
| O22 | The circulant Hadamard conjecture (`CirculantHadamard` + `EvenBarker`) | **NOT DONE** (3/6: Theorem 1.1 closed for every reader; replays dispatched) | **1248Z: disclosed** (`docs/179.md`: "The paper's classification of odd Barker lengths is outside this selected additional statement") — not a finding. Corollary 1.2 (Barker lengths exactly {2,3,4,5,7,11,13}) is stated in Lean only for even lengths (`even_length_eq_two_or_four`); the odd case (cited) and existence are not |
| O23 | A quadratic bound for Jacobsthal's function (`JacobsthalImproved` + `Jacobsthal`) | **NOT DONE** (statement DONE: 6/6 — Theorem 1.1 and Jacobsthal's quadratic question, every reader; replays dispatched) | none at statement level; the frozen iterated-log bound also gives the quadratic form (C' = C/(log log 3)²), closed in Lean |
| O24 | Single-fold Diophantine representations (`SingleFold`) | **NOT DONE** (3/6: Theorem 1.1 closed for every reader; replay dispatched) | **1248Z: disclosed** (`docs/242.md`: "The consequence that solvability remains undecidable under an at-most-one-solution promise is not separately formalized") — not a finding. the Corollary (undecidability under an at-most-one-solution promise) has no Lean statement |
| O25 | A single lattice covering bound of order n log n (`SingleLatticeCovering`) | **NOT DONE** (statement DONE: 3/3; replay dispatched) | none at statement level |
| O26 | The Euclidean Steinitz–Bergström theorem (`SteinitzBergstrom`) | **NOT DONE** (8/11: Theorems 1.1 and 1.2 with one constant, every reader; replay dispatched) | **1248Z: not a gap** — `docs/097.md` describes the Lean exactly ("one absolute constant C … the same bound"); the readers' every-constant form is a reading of an ambiguous sentence, not a claim presented as formalized. the source's "the constant in Theorem 1.1 also suffices here", read by all three readers also as *every* 1.1-constant works for 1.2, is not in the Lean (it gives one common C) |
| O27 | A doubling Hilbert subset with no finite-dimensional bi-Lipschitz embedding (`DoublingHilbert` + `CompactBanach`) | **NOT DONE** (4/6: readers A and C, both theorems; replays dispatched) | the source does not say open or closed balls; the Lean fixes open balls; reader B's closed-ball reading (constant 76800) does not follow — an ambiguity resolved by the Lean, not a mismatch with the text |
| O28 | Uniform exclusion of Landau–Siegel zeros (`SiegelZeros`) | **NOT DONE** (statement DONE: 4/4, every reader; replay dispatched) | none at statement level: the frozen statement is the readers' up to argument order (`LFunction` pinned in target R) |
| O29 | The sharp logarithmic exponent of r(5,t) (`RamseyFive`) | **NOT DONE** (statement DONE: 6/6 — bounds and limit, every reader; replay dispatched) | none at statement level |
| O30 | The subcritical Hénon–Lane–Emden conjecture (`HenonEmden`) | **NOT DONE** (statement DONE: 6/6 — Theorem 1.1, and Corollary 1.2 derived in Lean from the frozen theorem at A = B = 0, every reader; replay dispatched) | none at statement level |
| O31 | Relative independence of the separable quotient problem (`SeparableQuotientNegative`) | **NOT DONE** (1 of 6 claims: reader A's (ii); replay dispatched) | **1248Z: disclosed** (`docs/323.md`: "The positive consistency direction and the paper's full relative-independence conclusions are outside the selected statement") — not a finding. Theorem 1.1 (i) (real-valued measurable 𝔠 ⇒ SQ) has no Lean statement; only (ii) (CH ⇒ ¬SQ) is stated; the independence conclusions are about provability in ZFC (not statable, all readers agree) |
| O32 | Finite algebraic envelopes and the Boone–Higman conjecture (`BooneHigman`) | **NOT DONE** (3/4: every reader's Theorem 1.1 with "some generating family", G in `Type`; replay dispatched) | none at statement level; reader A's extra "every generating family" form is not closed (true, needs a computability argument) |
| O33 | An explicit failure of complex affine space cancellation (`ComplexCancellation`) | **NOT DONE** (7/10: Theorem 1.1, every reader; replay dispatched) | **1248Z: disclosed** (`docs/047.md`: "The separate stable-coordinate and general line-bundle lifting consequences are not included") — not a finding. Corollary 1.2 (H is a stable coordinate but not a coordinate: the Stable Coordinate Conjecture fails) has no Lean statement |
| O34 | Bi-Lipschitz absorption of c₀ without a linear copy of c₀ (`C0Absorption`) | **NOT DONE** (1/3: reader C; replay dispatched) | none at statement level; readers A and B define c₀ inside ℓ^∞ (isometric to the frozen `C₀(ℕ, ℝ)`; transport not written) |
| O35 | Kaplansky's direct finiteness conjecture in odd characteristic (`OddKaplansky`) | **NOT DONE** (statement DONE: 4/4, every reader; replay dispatched) | none at statement level; the prime p = minFac((C(1200,600)!)² + 1) is never evaluated — each reader's p is proved equal to the frozen one symbolically |
| O36 | A nine-dimensional counterexample to Borsuk's covering assertion (`BorsukNine`) | **NOT DONE** (readings committed; closures not written this run; proof replay dispatched) | **1248Z: not a gap** — the frozen statement asserts `projectorSet ⊆ traceOneSymmetric` (a 9-dimensional affine subspace) and `docs/156.md` says exactly that; the identification with ℝ⁹ is a link of ours not yet closed, not a gap of the Lean. the frozen statement is about X in `EuclideanSpace ℝ (Fin 4 × Fin 4)`; "Borsuk fails in dimension nine" (a set in ℝ⁹) has no Lean statement — it needs the trace-one hyperplane identified with ℝ⁹ |
| O37 | A counterexample to the infinite matroid packing/covering conjecture (`InfiniteMatroid` + `InfiniteMatroidCorollaries`) | **NOT DONE** (Theorem 1.1 closed for every reader — A's two forms, B, C's three — against `main`; Corollary 1.4 readings, against the second challenge, not written this run; replays dispatched) | none found: Corollary 1.4 (intersection fails, partitional) is the second challenge |
| O38 | Fixed points of nonexpansive maps in reflexive Banach spaces (`ReflexiveFixedPoints`; scope document 328) | **NOT DONE** (Theorem 1.1 closed 3/3: readers A, B directly, reader C, which omits completeness, through a proof here that a space whose canonical map into the bidual is onto is complete; non-vacuity: ℝ is reflexive, proved; replay dispatched) | none at statement level; Corollary 1.2 (commuting families, through Bruck's cited theorem) has no Lean statement and the scope document does not mention it (undisclosed, minor) |
| O39 | Pure-point spectrum for the two-dimensional Anderson model (`PlanarAndersonSpectrum`; scope document 261) | **NOT DONE** (conclusion (i), the spectrum, closed 3/3 across three models of the randomness, each transported to the frozen product law; B and C's "every operator with the formula" reduced to the frozen one by uniqueness; replay dispatched) | the headline — pure-point type, eigenbasis, dense eigenvalues — has no Lean statement; **disclosed** (`docs/261.md`: "It does not assert the pure-point spectral type claimed in the accompanying paper"); the Lean statement (spectrum = [−4−h, 4+h]) is the classical part (767-line proof) |
| O40 | Quasipolynomial bounds for arithmetic progressions (`ErdosReciprocal`; scope document 159) | **NOT DONE** (Corollary 1.2 — Erdős's reciprocal-sum conjecture — closed 3/3, reader A's sum in ENNReal; the solution's closure is 4,774 files, 1.12 M lines; replay dispatched) | Theorem 1.1 (the density bound) and its threshold form have no Lean statement: **disclosed** (`docs/159.md`) |
| O41 | A counterexample to Hadwiger's conjecture (`HadwigerCounterexample`; scope document 157, with O42's paper) | **NOT DONE** ("Hadwiger's conjecture is false" closed 3/3 from `not_hadwiger_conjecture`, the frozen Hadwiger number shown a genuine maximum (t ≤ |V| for a K_t minor); Theorem 1.1 (α ≤ 2, cm < m/100) closures not written (connected matchings: Sym2 edges vs two-element finsets); replay dispatched) | none at statement level for the disproof; the corollary's χ_f bounds (and the fractional weakening's disproof) have no Lean statement: **disclosed** (`docs/157.md`) |
| O42 | A linear list-coloring bound in terms of the Hadwiger number (`ListHadwiger`; scope document 157) | **NOT DONE** (Theorem 1.1 closed 3/3; the frozen `listChromaticNumber` (`sInf`) shown non-vacuous by Hall's theorem; Corollary 1.2 (χ ≤ C h) has no Lean statement, a one-line consequence; replay dispatched) | none at statement level |
| O43 | Rokhlin's multiple-mixing problem for one transformation (`Rokhlin`; scope document 145) | **NOT DONE** (reader A's explicit Theorem 1.1 closed (gap filters, ℕ+ vs positive ℕ, the two mixing filters on ℤ proved related); readers B (ε–N, toReal) and C (`Equiv.Perm` with measurable inverse) and every reader's "order k for every k ≥ 2, arbitrary t₁" form not written; replay dispatched) | none found |
| O44 | Seymour's second-neighborhood conjecture (`SeymourSecondNeighborhood`; scope document 173) | **NOT DONE** (Theorem 1.1 closed 3/3 **in both directions**: each reader's statement implies the frozen one and is implied by it; orientation shown needed (two vertices with both arcs: no good vertex); replay O-seymour dispatched) | none at statement level. The paper's directed-triangle consequence (minimum in- and outdegree ≥ n/3) has no Lean statement and the scope document does not mention it: undisclosed, minor (a stated corollary). It was not read blind: the brief's excerpt stopped one line before it (brief defect, ours) |
| O45 | A counterexample to Kaplansky's zero-divisor conjecture (`TorsionFreeZeroDivisors`; scope document 196) | **NOT DONE** (first sentence of Theorem 1.1 closed 3/3, "Kaplansky's conjecture is false" 3/3; the "Moreover" clause (finite two-dimensional K(G,1)) closed for reader B; A (higher homotopy groups vanish) and C (simplicial complex) not closable in Mathlib; replay O-zerodiv dispatched) | none at statement level; the frozen classifying space (finite CW complex, cells in dimensions ≤ 2 with a 2-cell, contractible covering space, π₁ ≅ G) is a K(G,1) as the paper means it |
| O46 | Uniformly bounded components of Gaussian-prime graphs (`GaussianMoat`; scope document 028) | **NOT DONE** (Theorem 1.1, its "Consequently" and the negative answer to the moat question each closed 3/3; the frozen `dist` in ℂ proved equal to each reader's distance; replay O-moat dispatched) | none at statement level |
| — | Integral points on character varieties (`CharacterVarietiesAllSeamsSupport`) | **NOT STARTED** | observation (orchestrator only, not a blind reading): the family's only challenge is a lemma about the release's own `Diagram` structures (it imports OAI modules), not a statement of Theorem 1.1 in Mathlib terms; queued for the protocol |

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

## O14–O16 (run 2026-11-27T0628Z; brief 3fe4368 with exact paths and "no wildcards" — no reader saw another family's
file this time; readings c0c63963; closures b810f86b)

**O14, sunflowers.** Frozen: `∀ r ≥ 3, ∃ C : ℕ, 1 ≤ C ∧ ∀ k α (F : Finset (Finset α)), (all k-sets) → C^k < |F| →
F has an r-sunflower` — uniform families, which is the Erdős–Rado sunflower conjecture. The manuscript states it for
sets of size *at most* k, with B_r = 2^{C H⁴ L^{5/2}}. Closed (`sunflower/closure/Closure.lean`, standard axioms):
reader C's bounded-size form from the uniform one by splitting F into its k + 1 layers (B = 2C); readers A and B's
forms over a possibly infinite `Set` of sets (finiteness part of the conclusion) from C's, since a set family whose
finite subfamilies are bounded is finite; reader A's `M_r(k) ≤ B_r^k` (a supremum in ℕ∞) the same way.
Uncovered: the three quantitative readings and reader C's quantitative `M_r(k)` bound — the explicit B_r is the
manuscript's own content beyond the conjecture and has no Lean statement. Solution closure: 7,272 files, 885,263
lines (external packages Lemmata, FixedPointTheorems); scan: 34 `admit` hits, all an identifier named `admit`
(scan_escapes.py now reports `admit` apart from `sorry`), 21 `partial def` metaprograms, no `debug.` options.

**O15, Littlewood polynomials.** Frozen: `∀ η > 0, ∃ N₀ ≥ 1, ∀ N ≥ N₀, ∃ ε (±1 reals), ∀ |z| = 1,
|∑ ε_k z^k| ≤ (1 + η)√N` — the manuscript's "Equivalently" form. Closed for every reader (frozen ⇒ reading).
The headline "lim m_N = 1" needs also m_N ≥ 1, which the source gives as known (orthogonality, ‖P‖₂² = N) and
which no frozen statement carries; first recorded as uncovered (3/6), then closed the same run
(`littlewood/closure/ClosureLimit.lean`, standard axioms): ∑_{j<N} |P(ω^j)|² = N² at the N-th roots of unity, so
some e(j/N) has |P| ≥ √N, hence each reader's m_N ≥ 1 (reader A's `inf'` over `ℤˣ` signs and `⨆` over ℝ;
reader B's `⨅` over a subtype; reader C's `sInf`/`sSup` over images); with the upper bound from the frozen
statement, a squeeze gives the limit. 6/6. Solution closure: 24 files, 9,315 lines, no escape hits.

**O16, dyadic Erdős similarity.** Frozen: for 0 < η < 1 a compact E ⊆ [0, 1] of measure > 1 − η with
x + s·2^{−n} ∉ E for some n ≥ 1, for every x and s ≠ 0. Closed frozen ⇒ each reading, both forms (5/5). Solution
closure: 75 files, 8,455 lines, no escape hits.

## Replays read at 09:18Z (runs 45961122008, 45963613011, 45966220553, 45969890573)

- PASSED (match, axioms, nanoda): O-kaplansky2, O-plane5, O-plane7 (coverage COMPLETE), O-piexp, O-cliquefree
  (coverage COMPLETE), O-noncoord. Leanchecker shards: kaplansky2 3/4 OK, plane5 3/4 OK, others pending.
- O-catalan, O-ostmann: the solution's build failed (PrimeNumberTheoremAnd's `Catalan.Consequences` and the
  modules above it). Both jobs ran before replay.sh applied OpenAI's `patches/<pkg>-lean4341.patch` (2cb101a);
  re-dispatched. Their leanchecker shards failed on the same build (bad imports), not on a check.
- O-sqdiff: match and axioms PASSED; nanoda aborted (`thread 'thread_0' has overflowed its stack`). Ours, not
  the proof's: replay.sh now gives nanoda's worker threads 1 GiB; re-dispatched. Leanchecker shards 2 and 4 OK.
- O-smallcm: match and axioms PASSED; the blind readings do not elaborate under OpenAI's Mathlib pin
  (`IsLocalRing.depth` is newer). The verdict does not depend on them (no closure exists); re-dispatched without.
  General lesson: a reading written against our Mathlib may not compile at an outside pin — the replay line then
  checks the readings under our pin only, and says so.

## O17–O19 (run 2026-11-27T0628Z; brief 9c41e72, readings 990145b; files `runs/2026-11-27T0628Z/O/{llogl,unitdist,finfty}/`)

**O17, Fourier series in L log L.** Claim (01-introduction.tex, 61ad5332…): for every complex f ∈ L log L(𝕋),
𝕋 = ℝ/2πℤ with dμ = dx/2π, S_N f → f off a measurable null set, along the full sequence. Frozen: the same on
`AddCircle (2π)` with `haarAddCircle`, Mathlib's `fourierCoeff` and `fourier`, hypotheses `AEStronglyMeasurable`
and integrability of ‖f‖ log(2 + ‖f‖). Closed frozen ⇒ each reading (`llogl/closure/Closure.lean`): A's
(ofReal 2π)⁻¹ • volume and B's ofReal(1/2π) • volume equal `haarAddCircle` (`volume_eq_smul_haarAddCircle`);
A's character, the descent of t ↦ e^{ikt}, equals `fourier k`; the readers' lower-integral hypothesis gives the
frozen `Integrable`. Solution closure: 156 files, 29,665 lines, no escape hits — small for the claim (the L log L
endpoint of Carleson–Hunt, open since Kolmogorov's L¹ counterexample); the replay decides.

**O18, unit distances.** Claim (00-introduction.tex, 25a795fb…): absolute 0 < C, 1 ≤ β < 4/3 with u(n) ≤ C n^β
for all n; equivalently u(n) = O(n^{4/3−δ}). Frozen: the bound, u as the `sSup` of `Sym2` unit pairs. Closed
for every reader, both forms (6/6): a bijection between 2-element unit subsets and `Sym2` unit pairs (A, C), set
equality (B); big-O with δ = 4/3 − β. Solution closure: 40 files, 28,113 lines, no escape hits.

**O19, universal F∞ group.** Claim (introduction.tex, 069ab99e…): Theorem 1.1, an F∞ group into which every
finitely presented group embeds; Corollary 1.2, f.g. G embeds iff recursively presented. Frozen: Theorem 1.1
with `HasTypeFInfinity` (Hausdorff, connected, CW structure on univ with finitely many cells per dimension,
π₁ ≃* H, a surjective covering from a contractible space). Closed: every reader's Theorem 1.1 (readers B and C
ask less of the cover, A also continuity; A and C's own finite presentations give Mathlib's
`Group.IsFinitelyPresented`). Uncovered: Corollary 1.2 (4 readings). Solution closure: 50 files, 19,991 lines, 5
custom-syntax hits.

## O20–O22 (run 2026-11-27T0628Z; brief 893ed69, readings 1e43daa; files `runs/2026-11-27T0628Z/O/{mahler,ramsey,hadamard}/`)

**O20, symmetric Mahler.** Claim (introduction.tex, 64a324e8…): for n ≥ 1 and every origin-symmetric convex
body K ⊂ ℝⁿ, |K||K°| ≥ 4ⁿ/n!, with equality iff K is a linear Hanner body. Frozen: the inequality, on
`Fin n → ℝ` with a coordinate polar, as `toReal` products. Closed for every reader (frozen ⇒ reading): A in
`Fin n → ℝ` directly; B and C in `EuclideanSpace` via the volume-preserving `EuclideanSpace.equiv`, under which
their inner-product polar is the coordinate polar; the frozen real bound gives the readers' ℝ≥0∞ bound
(`ofReal a.toReal ≤ a`). Uncovered: the equality case (3 readings). Solution closure: 229 files, 21,379 lines,
5 custom-syntax hits.

**O21, Euclidean Ramsey.** Claim (01-introduction.tex, 55d8307a…): the Classification theorem (A is Ramsey iff a
matrix P over F ⊗_ℚ F satisfies the tensor evaluation identities and m_F(P_αβ) = δ_αβ), and in prose: subtransitive
sets are Ramsey; ≤ 5 points on a circle are Ramsey; finite Ramsey sets are spherical (cited, EGMRSS). Frozen:
three challenges, each on enumerations `Fin s → ℝ^d`; they cannot be imported together (each redeclares
`Congruent` and `Ramsey`), so the closures are split by challenge. Closed: (iii) for every reader, (ii) for
reader B (`enum`/`ofSet`/`toSet` carry a set's Ramsey property to an injective enumeration's and back).
Uncovered: the Classification (3 readings), (i) (3), (ii) for A and C (stated for circles in ℝ^m; a closure needs
a congruence of the circle into the plane — not attempted this run). Coverage prints 4/13: reader B's
`HasTensorMatrix` is a `def … : Prop` counted as a reading; the claims are 4/12. Solution closures: 39 files,
7,653 lines, no escape hits (all three).

**O22, circulant Hadamard.** Claim (introduction.tex, 54c2d276…): for n > 0 a real circulant Hadamard matrix of
order n exists iff n ∈ {1, 4} (Ryser's conjecture); corollary: for n > 1 a Barker sequence of length n exists iff
n ∈ {2, 3, 4, 5, 7, 11, 13}. Frozen: Theorem 1.1 (`Fin n` subtraction) and the even Barker case (separate
challenge; the two cannot be imported together). Closed: every reader's Theorem 1.1 (both directions of the
existence statements: A asks the signs of h, given by the first row; B and C index by `ZMod n`, carried by
`ZMod.finEquiv`). Uncovered: Corollary 1.2 (3). Solution closures (both): 73 files, 9,773 lines, no escape hits.

## Replays read at 10:25Z

- PASSED (match, standard axioms, nanoda): O-catalan (with the dependency patch; 7/7 COMPLETE), O-falconer (3/3
  COMPLETE), O-falconer-planar, O-kaplansky2-fg, O-smallcm (proof only), O-dyadic (5/5 COMPLETE), O-littlewood
  (6/6 COMPLETE; leanchecker 4/4 → **O15 DONE**), O-llogl (3/3), O-unitdist (6/6), O-finfty (3/7). Leanchecker
  4/4: O-noncoord, O-littlewood; 3/4 with the 4th lost to "the hosted runner lost communication": O-kaplansky2,
  O-plane5 (re-dispatched); O-sqdiff shards 1 and 3 lost the same way.
- **O-amenable: our closure failed at OpenAI's Mathlib pin** (`IsSimpleGroup.eq_bot_or_eq_top_of_normal` takes
  the normality explicitly there, as an instance in ours): A_thm and C_thm printed `sorryAx` and the job failed —
  the gate held. Fixed to elaborate at both pins (`first | … hN | …`); re-dispatched. General lesson: closures are
  written against our Mathlib and judged at the outside pin; only the replay at the pin counts.
- O-qrh-*: every earlier failure predates the dependency patches (RellichKondrachov type mismatches, a lake
  cache fetch); the patched runs are still going.

## O23–O25 (run 2026-11-27T0628Z; brief c5c91a5, readings 1d9fc2b; files `runs/2026-11-27T0628Z/O/{jacobsthal,singlefold,latticecov}/`)

**O23, Jacobsthal.** Claim (introduction.tex, 94390ede…): h(k) ≤ C k²/(log log 3k)² for every k ≥ 1, h(k) = sup of
Jacobsthal's j(n) over ω(n) ≤ k; it answers Jacobsthal's question h(k) ≪ k². Frozen: some m with the covering
property for every n with ω(n) ≤ k and m ≤ C k²/(log log 3k)². Closed for every reader (their j(n) ≤ m as m is
admissible; sup ≤ m), both forms; the quadratic one from the same frozen statement since log log 3k ≥ log log 3 > 0
(e < 3). The family's second challenge (`erdos_970_quadratic`) cannot be imported with the first; replayed alone.
Solution closure: 819 files, 152,494 lines (PrimeNumberTheoremAnd, StrongPNT, AbsorptionCutoff), 55
custom-syntax hits.

**O24, single-fold representations.** Claim (main.tex, 1872e660…): every r.e. S ⊆ ℕⁿ (n ≥ 1) has m ≥ 1 and
P ∈ ℤ[A, W] with exactly one witness w ∈ ℕ^m on S and none off S (Matiyasevich's single-fold conjecture); corollary:
undecidability of solvability under an at-most-one-solution promise. Frozen: Theorem 1.1 (`REPred`, existence iff
membership, witness uniqueness at every input). Closed for every reader (A and C count with `encard`, B with
`∃!`). Uncovered: the Corollary (3). Solution closure: 28 files, 7,598 lines, 4 custom-syntax hits — small for the
claim; the replay decides.

**O25, lattice covering.** Claim (overview.tex, 99f45ea7…): an absolute C with, for n ≥ 2 and every convex body K,
a full-rank lattice Λ with K + Λ = ℝⁿ and vol K / det Λ ≤ C n log n. Frozen: the same with Mathlib's `IsZLattice`
and `ZLattice.covolume`. Closed for every reader: A (Λ = Aℤⁿ, det A ≠ 0) and C (ℤ-span of a linearly independent
family) from a ℤ-basis of L indexed by `Fin n` (rank n) and `covolume_eq_det`; B in `EuclideanSpace` by pulling L
back along the volume-preserving `EuclideanSpace.equiv` (`covolume_comap`). Solution closure: 41 files, 25,913
lines, no escape hits.

## O26–O28 (run 2026-11-27T0628Z; brief 6a2ff84, readings e0665a9; files `runs/2026-11-27T0628Z/O/{steinitz,doubling,siegel}/`)

**O26, Steinitz–Bergström.** Claims (introduction.tex, 84a36d95…): signed prefixes ≤ C√d (1.1); zero-sum orderings
≤ C√d (1.2); "the constant in Theorem 1.1 also suffices here". Frozen: one C with both. Closed: 1.1, 1.2 and the
common-constant form for every reader (8). Uncovered: the "every constant" reading (3; A, B and C each wrote it).
Solution closure: 29 files, 15,082 lines, no escape hits.

**O27, doubling Hilbert subset.** Claims (main.tex, 3eac74d0…): a subset of real ℓ₂ with doubling constant ≤ 76800
and no bi-Lipschitz embedding into any ℝ^k at any distortion (the Lang–Plaut question, negative); a compact
obstruction with universal doubling constant in every infinite-dimensional real Banach space (stated in prose,
Section 8). Frozen: both, as two challenges (open balls; scale a > 0, distortion D ≥ 1). Closed for readers A and C
(an embedding at distortion D < 1 is one at distortion 1). Not closed: reader B (closed balls) — the source's
"balls" is ambiguous; the Lean takes open balls. Solution closures: 28 files, 4,664 lines, no escape hits.

**O28, Landau–Siegel zeros.** Claim (paper.tex, b011ba9c…): an absolute c > 0 with (1 − β) log q ≥ c for every real
zero β ∈ (0,1) of every primitive nonprincipal real Dirichlet L-function of conductor q ≥ 3. Frozen: the same with
Mathlib's `DirichletCharacter.LFunction` (the continuation — pinned in target R by the identity theorem), real
values as zero imaginary parts. Closed for every reader, and reader A's conductor form (4/4). Solution closure:
306 files, 69,818 lines (PrimeNumberTheoremAnd), 56 custom-syntax hits. The claim is one of the central open
problems of analytic number theory; the replay decides whether the proof checks.

## Correction, 11:07Z: two "no Lean statement" findings withdrawn (our error)

The O20 and O21 findings sent to Alexander at 10:30Z ("Mahler: equality case has no Lean statement";
"Euclidean Ramsey: the Classification theorem has no Lean statement") were **wrong**. Each family has further
comparator challenges that I had not listed: I mapped families to challenges by taking the challenges near the
current size threshold, not by the solution module's directory. Listing every challenge by solution directory
(`OAI.<Area>.<Family>.*`) shows:

| family | challenges | missed |
|---|---|---|
| O20 Mahler | `MahlerConjecture`, `SymmetricMahlerEquality` | the equality case (Hanner bodies) |
| O21 Euclidean Ramsey | `EuclideanRamsey` (Classification), `…Spherical`, `…Circle`, `…Transitive`, `…Nine`, `…Quadratic` | the headline and two consequences |
| O5 Ostmann | `OstmannPrimes`, `OstmannComplete` (inverse Goldbach; no two infinite summands) | further claims (O5's readings closed 7/7 against `OstmannPrimes`) |
| O15 Littlewood | `AsymptoticallyMinimalLittlewood`, `LittlewoodFiniteFlatness` | a second statement (O15's readings closed 6/6 against the first) |

Every other "no Lean statement" finding (O3 Gottschalk, O7 small CM, O9 Flint–Hills, O10 explicit F, O14 explicit
B_r, O19 Corollary 1.2, O22 Barker lengths, O24 Corollary, O26 every-constant form) was re-checked against the full
list by solution directory and a keyword search of all 425 challenge files (Gottschalk, surjunctive, Flint, Hills,
Barker, Hanner, recursively, REPred, Higman, Steinitz, …): no further challenge states those claims.
General fix: `scripts/external/family_challenges.py` lists a family's challenges by solution directory; a coverage
verdict cites its output.

After the correction (11:14Z): reader A's equality case closed against `symmetric_mahler_equality`
(`mahler/closure/ClosureEquality.lean`: A's Hanner polytopes equal the frozen ones by induction both ways; the
`ℝ≥0∞` equation is the frozen real one since 0 < vol K < ∞); reader B's Classification closed against
`EuclideanRamsey.classification` (`ramsey/closure/ClosureClassification.lean`: B's criterion indexed by `Fin (d+1)`
is the frozen one indexed by `Option (Fin d)` under `finSuccEquiv`; the frozen extra hypothesis 1 ≤ d follows from
two distinct points). Not yet: B and C's equality case, A and C's Classification (their coefficient fields are
other terms for the same field; the tensor-ring transport is not written). Replay lines added for every missed
challenge (O-mahler-eq, O-ramsey-class, O-ramsey-nine, O-ramsey-quad, O-ostmann-complete, O-littlewood-flat).

## O29–O31 (run 2026-11-27T0628Z; brief 0aae0c4, readings fbb30b3; files `runs/2026-11-27T0628Z/O/{ramsey5,henon,sepquot}/`; `family_challenges.py`: one challenge each)

**O29, r(5,t).** Claim (introduction.tex, d7ffbe8e…): ∃ C > 0, ∀ ε > 0, eventually t⁴/(log t)^{3+ε} ≤ r(5,t) ≤ C t⁴/(log t)³;
hence (4 log t − log r(5,t))/log log t → 3. Frozen: both, with `ramsey` = sInf over `SimpleGraph (Fin n)`. Closed for
every reader: each reader's r(s,t) equals the frozen `ramsey` (A, C: cliques/independent sets of given cardinality;
B: `¬CliqueFree` of G and Gᶜ via `isNClique_compl`). Solution closure: 482 files, 73,678 lines, no escape hits.

**O30, Hénon–Lane–Emden.** Claim (01-introduction.tex, 6f100de2…): no positive u, v ∈ C²(ℝⁿ∖{0}) ∩ C(ℝⁿ) solving
−Δu = |x|^A v^p, −Δv = |x|^B u^q off 0 when (n+A)/(p+1) + (n+B)/(q+1) > n − 2 (n ≥ 2, p, q > 0); corollary: the
unweighted Lane–Emden conjecture. Frozen: Theorem 1.1 (`Laplacian.laplacian`, `ContDiffOn ℝ 2` off 0, continuity).
Closed for every reader, both: the corollary follows in Lean from the frozen theorem (A = B = 0, the hypothesis
times n, |x|⁰ = 1). Solution closure: 96 files, 12,709 lines, no escape hits.

**O31, separable quotient problem.** Claim (introduction.tex, 743da2df…): ZFC proves (i) 𝔠 real-valued measurable ⇒
SQ_𝔽 and (ii) CH ⇒ ¬SQ_𝔽; hence independence relative to a measurable cardinal. Frozen: (ii) only. Closed: reader
A's (ii). Not closed: (i) for every reader (no Lean statement); (ii) for B (stated for every `RCLike 𝕜`) and C
(a type equal to ℝ or ℂ with an arbitrary `RCLike` instance) — true readings, but transporting the frozen ℝ/ℂ
statement along an `RCLike` isomorphism is not written; coverage also lists reader A's `CH` definition. Solution
closure: 51 files, 14,178 lines, 2 custom-syntax hits.

## O32–O34 (run 2026-11-27T0628Z; brief 08b11e5, readings 9c11aab; files `runs/2026-11-27T0628Z/O/{boonehigman,cancellation,c0absorb}/`; one challenge each)

**O32, Boone–Higman.** Claim (introduction.tex, 48b68815…): a finitely generated group has decidable word problem
iff it embeds in a finitely presented simple group. Frozen: the same (`ComputablePred` on words for some finite
generating family; `Group.IsFinitelyPresented`, `IsSimpleGroup`; universe-polymorphic). Closed at universe 0: B, C
(C's decider is a total `Computable` Bool function — `ComputablePred.computable_iff`), A's "some family" form (A's
finite presentations and simplicity converted both ways). Not closed: A's "every generating family" variant and A's
statement for G in higher universes (A puts H in `Type`). The simplicity conversions are written to elaborate at
both Mathlib pins (`IsSimpleGroup.eq_bot_or_eq_top_of_normal` changed signature). Solution closure: 47 files,
37,197 lines, 6 custom-syntax hits.

**O33, affine cancellation.** Claim (01-introduction.tex, 73508976…): A = ℂ[p,s,u,F,J]/(H) is a 4-dimensional domain
with A[w] ≅ ℂ[5 variables] and A ≇ ℂ[4 variables] (Zariski cancellation fails over ℂ in dimension 4); corollary:
H is a coordinate of P[w] but not of P. Frozen: Theorem 1.1 (plus finite type). Every reader wrote the same
variables in the same order: their A is the frozen A by `rfl`. Closed: Theorem 1.1 (A's four parts and conjunction,
B, C). Uncovered: Corollary 1.2 (3). Solution closure: 55 files, 5,573 lines, no escape hits.

**O34, c₀ absorption.** Claim (01-introduction.tex, 13bfea3a…): a separable real Banach Z with no closed subspace
isomorphic to c₀ and an onto bi-Lipschitz Z ⊕_∞ c₀ → Z (Kalton's Problem 2, negative). Frozen: with "no
bounded-below linear map c₀ → Z", plus further properties. Closed: reader C (a closed copy of c₀ would give such a
map). Not closed: A and B (c₀ as a subspace of ℓ^∞; the isometry with `C₀(ℕ, ℝ)` is not written). Solution closure:
34 files, 7,918 lines, no escape hits.

## Replays read at 12:00Z

PASSED (match, standard axioms, nanoda): O-amenable (3/3 COMPLETE, with the fixed closure), O-ostmann (7/7
COMPLETE), O-qrh-dirichlet, O-qrh-hecke, O-mahler (3/6), O-hadamard (3/6), O-barker, O-ramsey-sph, O-ramsey-circle,
O-ramsey-trans; leanchecker shards queued behind the runner limit. O-sqdiff's re-run lost its runner ("received a
shutdown signal", exit 143) after match and axioms — infrastructure; re-dispatched. Queued: R-sernau-grh/compact
(dedicated re-run for the leanchecker shards), O23–O34 lines and the missed challenges.

## O35–O37 (run 2026-11-27T0628Z; brief 4494e17, readings 3f45e7b; files `runs/2026-11-27T0628Z/O/{oddkaplansky,borsuk,matroid}/`)

**O35, Kaplansky in odd characteristic.** Claim (01-introduction.tex, 726e3c3b…): with m = C(1200, 600) and p the
least h > 1 dividing (m!)² + 1, p is an odd prime and there are a field of order p⁴, a finitely generated group
with torsion and a, b ∈ K[G] with ab = 1 ≠ ba. Frozen: the same (p = `Nat.minFac`, both numbers `@[irreducible]`;
plus characteristic p and an injective non-surjective cellular map). Closed for every reader (4/4): `Nat.find`
(A), `sInf` (B, C) and A's least-integer form all equal `minFac` for any n ≥ 2; the frozen m is reached by `unseal`
and `rfl` on the identical term — generating `sourceM`'s equation lemma, or stating C(1200,600) inside `rw`,
exceeds the recursion limit (a trap for closures: nothing about the huge numbers may be reduced). Solution closure:
138 files, 18,517 lines, 12 custom-syntax and 2 `partial` hits.

**O36, Borsuk in dimension nine.** Claim (introduction.tex, 379065fa…): X = {uuᵀ : ‖u‖ = 1}, in the 9-dimensional
trace-one hyperplane of Sym₄(ℝ) with the Frobenius metric, is compact of diameter √2 and not coverable by ten
subsets of smaller diameter. Frozen: the same in `EuclideanSpace ℝ (Fin 4 × Fin 4)`. Readers work with `Matrix`
and the Frobenius norm (A: Mathlib's scoped instance; B, C: written by hand); closures need the isometry between the
two and are not written this run. The readers' second theorem (a set in ℝ⁹) is not stated in the Lean. Solution
closure: 269 files, 78,964 lines, 148 custom-syntax hits.

**O37, infinite matroids.** Claim (01-introduction.tex, 8abfb85a…): a countably infinite E with two self-dual
matroids, no independent covering, no packing/covering partition; Corollary 1.4: both partitional, intersection
fails. Frozen: `main` and `partitional_intersection_counterexample` (second challenge). Readers use Mathlib's
`Matroid`; B writes contraction onto C as `M ／ (E \ C)`, A and C as (M✶ ↾ C)✶ like the frozen one; closures not
written this run. Solution closures: 33 files, 4,477 lines, no escape hits.

O37 update (`matroid/closure/Closure.lean`): every reader's Theorem 1.1 closed against `main` — a reader's
partition gives the frozen `HasPackingCovering` (closure of S in M ↾ P equal to P with S ⊆ P is `Spanning`; reader
B's contraction M ／ (E \ C) is the frozen (M✶ ↾ C)✶ when C ⊆ E, by `dual_delete_dual` and `delete_eq_restrict`);
reader A's "the conjecture is false" follows. 6/12; the six Corollary 1.4 readings await a closure against
`InfiniteMatroidCorollaries`.

## Correction 2, run 2026-11-27T1248Z: every gap re-checked against OpenAI's scope documents (PROMPT 11, "Target O correction")

**Method (general, `scripts/external/family_map.py`).** At the pin, `lean/formalization.yaml` does not link challenges to
papers: its `sources` list 186 papers and its `status.main_results` 225 challenges by config, with no paper id on any
result (Catalan's paper, for one, is not a source at all). The paper ↔ challenge link is in OpenAI's scope documents
`lean/docs/NNN.md` (248; linked from `CONTENTS.md` as "[Lean]"): each names its papers and lists its challenges under
"Comparator links" — 424 of the 425 challenges are linked (`MatrixFields` is not). `family_map.py` reads these documents:
a family is the challenge list of its scope document, whatever the names or directories, and the document's sentences
that limit coverage are printed as the DISCLOSED lines. `--contents` compares each CONTENTS item carrying a Lean link
with its document and flags an item whose headline belongs to a paper the document does not cover (26 leads over the
whole release, unread; two read here: 084 and 197). A gap is a finding only if **undisclosed**: the scope document,
`CONTENTS.md` or the paper presents it as formalized, or nothing says it is not. A result the paper cites rather than
proves is not a coverage gap of the formalization.

| # | earlier gap | challenges by scope document | class now |
|---|---|---|---|
| O1 | editions differ (7/8 vs 11/12) | 003: + `SiegelZeros` (= O28, another paper) | disclosed (CONTENTS 003); not a finding |
| O3 | Gottschalk consequence unstated | 197: + `GroupRingDeterminant` (another paper), `OddKaplansky` (= O35) | refutation of Gottschalk is in the family's Lean (`OddKaplansky`); char-2 G's own corollary unstated: undisclosed, minor |
| O3/O35 | — | 197 | **new, undisclosed (index):** "torsion-free … over 𝔽₂ … even without torsion" under the Lean link; no Lean statement says torsion-free or 𝔽₂; `KaplanskyFinitelyPresented.lean:10` asserts torsion |
| O7 | headline not stated | 195 | disclosed (`docs/195.md`, verbatim above); not a finding |
| O9 | Flint–Hills unstated | 017 | disclosed; not a finding |
| O10 | no Lean names F | 049: + `CommutingDerivations`, `StableCoordinateFour` (another paper) | **withdrawn: wrong** — `CommutingDerivations` names F; "F is not a coordinate" closed 3/3. R/(F) ≅ ℂ^[3] for the named F unstated: undisclosed, minor |
| O14 | explicit B_r unstated | 379 (seven papers) | disclosed ("remains unformalized"); not a finding |
| O16 | none | 084 | **new, undisclosed (index):** CONTENTS 084 and the document's title present the geometric case for every q ∈ (0,1); the Lean is the dyadic case only |
| O19 | Corollary 1.2 unstated | 250: + `BooneHigman` (= O32), `SimpleOvergroups` (another paper) | disclosed; not a finding |
| O21 | (withdrawn 11:07Z) | 172: **seven** challenges, + `GrahamSpherical` (missed) | kites' non-subtransitivity cited, not proved: not a gap |
| O22 | odd Barker lengths unstated | 179 | disclosed; not a finding |
| O24 | undecidability corollary unstated | 242 | disclosed; not a finding |
| O26 | every-constant form | 097 | not a gap (document states the one-constant form) |
| O31 | (i) unstated | 323 | disclosed; not a finding |
| O33 | stable-coordinate corollary unstated | 047 | disclosed; not a finding |
| O36 | ℝ⁹ unstated | 156 | not a gap (`projectorSet ⊆ traceOneSymmetric` is stated; ℝ⁹ transport is our link) |
| O15, O18, O20, O25, O29, O34 | — | further challenges belong to other papers of the same document (`PinnedDistances`, `GeneralMahler`, `SymmetricPolar`, `CoveringDensity`, `SharpLogRamsey`, `LipschitzEquivalence`), except O15's `LittlewoodFiniteFlatness` (already recorded) | unchanged |

**Corrected list.** Of the twelve "parts missing" or "headline missing" entries reported (O3, O7, O9, O10, O14, O19,
O22, O24, O26, O31, O33, O36), **none is an undisclosed mismatch in a Lean statement**: eight are disclosed scope limits
(O7, O9, O14, O19, O22, O24, O31, O33), two are not gaps (O26, O36), one was wrong (O10), and O3's is mostly covered
(Gottschalk is refuted in the family's Lean by `OddKaplansky`). What remains undisclosed: two **index** overstatements (CONTENTS 197:
torsion-free over 𝔽₂; CONTENTS 084: every ratio q) — the Lean link sits on a headline the Lean does not state, while the
scope text describes the Lean accurately — and two minor unstated corollaries (O3's G non-surjunctive; O10's
R/(F) ≅ ℂ^[3] for the named F). Referee (Sonnet, raw files only, adversarial): confirmed all five facts with file and line.

## Index check, run 2026-11-27T1248Z: CONTENTS headlines under a Lean link that no Lean statement states

`family_map.py --contents` flagged 26 of the 246 Lean-linked CONTENTS items (heuristic: the scope document's title is
closer to a paper the document does not formalize than to any it does). Each was read against its CONTENTS headline,
its scope text and the theorem statements of every challenge it links (197, 084, 150, 095, 207 here; the other 21 by a
Sonnet auditor given exact paths, spot-checked here on 058, 182, 184, 307, 365). **Not a defect of any Lean statement:**
every scope text describes its Lean accurately. The defect is in the index: the "[Lean]" link sits on a headline whose
main claim no linked Lean statement states, and the scope text never says that claim is outside.

| item | headline claim under the Lean link | what the Lean states | verdict |
|---|---|---|---|
| 197 | finitely presented **torsion-free** group, algebra over **𝔽₂** not directly finite | finite field of char 2; `KaplanskyFinitelyPresented.lean:10` asserts an element of odd prime order | overstatement (doc title too) |
| 084 | geometric case, **every q ∈ (0,1)** | q = 1/2 only (`DyadicAvoidance`) | overstatement (doc title too) |
| 150 | billiard flow **weakly mixing** | ergodic (`IrrationalTriangleBilliard.lean:108-117`: invariant sets have measure 0 or 1) | overstatement (doc title too) |
| 095 | hyperbolicity cones **not spectrahedral shadows** (no semidefinite lift; Projected Lax disproved) | cone ≠ PSD region of a linear pencil (`HyperbolicCones.lean:67`): not spectrahedral; no lift statement | overstatement (doc title too) |
| 207 | **ℓ¹**-Bass conjecture for every group | complex Bass trace over ℂ[G] (`BassTrace.lean`); no ℓ¹(G) | overstatement (doc title too) |
| 058 | Kollár–Pardon classification of semialgebraic universal covers | a bounded semialgebraic domain with cocompact proper action is a bounded symmetric domain (`SymmetricDomains.lean:47`) | overstatement |
| 082 | annular r-variation bounds, the symmetric L³×L³×L³ estimate | maximal hard-truncation estimate (`TriangularHilbert.lean:50`) | overstatement |
| 182 | every intersective polynomial h, and prime arguments | squares only, h(m) = m² (`SquareDifference.lean:10`) | overstatement |
| 184 | Alon–Krivelevich–Sudakov coloring O_F(Δ/log Δ) | only the K_r-free independence bound (`CliqueFreeLog.lean:11`) | overstatement |
| 186 | hypergraph threshold widths, nonmonotone influence | graphs only (`SharpThreshold.lean:51`) | overstatement |
| 218 | Ising universality, SLE₃ interface limits | a finite-graph likelihood-ratio bound (`BufferedIsing.lean:98`) | overstatement |
| 256 | Howie's conjecture (nonsingular systems over any group) | Kervaire-type injectivity for one unimodular relator (`Kervaire.lean:31`) | overstatement |
| 262 | **finite-matrix** potentials and **all equality cases** | scalar W, sharp constant, attainment (`LiebThirring.lean:82`) | overstatement |
| 307 | **maximal** coarse assembly not rationally injective | the reduced (ordinary) assembly (`CoarseAssembly.lean:6629`); reduced failure does not imply maximal failure (μ_red = λ ∘ μ_max) | overstatement |
| 337 | Cartan–Hadamard isoperimetry in manifolds, equality case | CAT(0) filling inequality, optimal constant (`SharpCAT0Filling.lean:135`) | overstatement |
| 356 | Gigli's characterization of Alexandrov curvature | a weak-Hessian transfer lemma in RCD(K,N) (`WeakHessian.lean:220`) | overstatement |
| 365 | joint metric and connection recovery from one boundary patch | only the scalar-conductivity nonuniqueness companion (`Conductivity.lean:77`) | overstatement |
| 149, 009, 066, 210, 247, 260, 347, 363 | — | scope text says the remainder is outside (149 only implicitly) | disclosed |
| 109 | — | the Lean bound n(log n)^{1/2+o(1)} is stronger than the headline's | matches |

**17 of the 246 Lean-linked CONTENTS items** (two in our families: 184 = O11's document, 182 = O6's) put the Lean link on a
headline the Lean does not state, five of them with the unformalized claim in the scope document's own title. The
heuristic finds only items whose document title points at another paper; the other 220 items are unchecked for this
pattern (next step: every item, auditor batches).

### Index check, second pass: the other 44 items that bundle papers the Lean document does not cover

Three Sonnet auditors (exact paths, no web, briefs identical to the first pass), one reader per item; checked here
against the challenge files: 143, 076, 271, 251, 015.

- **Index overstatements (26):**
  - **143:** "Resolves the uniform boundedness assertion in Hilbert's sixteenth problem" for every real planar polynomial
    field. The Lean is the quintic Liénard family only: at most 2 limit cycles, and 2 attained
    (`QuinticLienard.lean:39-42`).
  - **076 (O15's document):** "ultraflat … merit factors tend to infinity, disproving Turyn's conjecture". The Lean has
    the max bound and L^p flatness only.
  - **271:** "Bloch's T^{3/2} law with its exact coefficient". The Lean has spontaneous magnetization only
    (`Heisenberg.lean:206`).
  - **251:** "equivalent to strong Ulam stability". The Lean has Dixmier's problem only.
  - **015:** quartic and sextic packets. The Lean has prime degree only.
  - **033:** Campana, Popa.
  - **039:** Seshadri constants in dimension ≥ 3 and in characteristic p. The Lean has surfaces.
  - **090:** Riesz, Coulomb and sphere energies.
  - **104:** deterministic quasipolynomial algorithms. The Lean has one randomized algorithm.
  - **114:** integer polymatroids. The Lean has equal-rank matroids.
  - **116:** positive characteristic.
  - **119:** the Hellinger conjecture (auditor moderately confident).
  - **122:** the decoder upper bounds. The Lean has lower bounds only.
  - **175:** graph decompositions.
  - **211:** LQG for q ≤ 4, Liouville Brownian motion, spectra. The Lean has q > 4 only.
  - **212:** no bigeodesics.
  - **215:** the O(3) continuum limit.
  - **220:** finite-range-dependent environments.
  - **222:** jamming and bi-orthogonal disorder.
  - **227:** autocorrelation limits (minor).
  - **263:** Z + CM binding and first-ionization bounds.
  - **289:** the counterexamples. The Lean has the positive stability result.
  - **291:** equivariant Jiang–Su stability.
  - **348:** the nonnegative-curvature classification and the L² gap. The Lean has positive curvature.
  - **361:** the ℝ³ metric for every large k.
  - **378:** the E^NP circuit lower bound (minor: the ETH disproof itself matches).
- **Disclosed (13):** 032, 117, 157, 206, 229, 235, 237, 240, 261, 267, 290, 353, 359.
- **Matches (4):** 003, 107, 342, 376.
- **Unsure (1):** 238 (the Ω(log N) lower bound).

**Total over both passes: 43 of the 246 Lean-linked CONTENTS items carry the Lean link on a headline claim that no linked
Lean statement states, and their scope text does not say so.** That count includes 2 minor items and 1 moderately
confident one. The other 176 items have one paper each and the same document; they are not yet audited for a headline
stronger than the Lean.

**What this means.** In about one in six items, the claim a reader of the index sees next to "[Lean]" is not the claim
the Lean checks. The scope documents are accurate, but they list what is formalized and rarely what is not. The
general gate: for each item, require an explicit line for every headline claim, either "stated in Lean (challenge,
theorem)" or "not formalized".

Second readers (Opus, two auditors, same brief, independent of the first): **all 28 single-reader overstatements of the
second pass and of the first pass's auditor-only items confirmed** (082, 186, 218, 256, 262, 337, 356, 033, 039, 090,
104, 114, 116, 119, 122, 175, 211, 212, 215, 220, 222, 227, 263, 289, 291, 348, 361, 378); 238 resolved as MATCHES
(Θ(log N) is stated: `ThorpRemaining.lean:543`). Every one of the 43 now rests on two readers, or on one reader plus a check
of the challenge files here. Readers note two implications counted as stated: Kervaire from the unimodular-relator
injectivity (256) and the symmetric trilinear estimate from the maximal bound by Hölder (082).

### Index check, third pass: the remaining 176 single-paper items (eight Sonnet first readers, two Opus second readers on every non-match)

- **Index overstatements (8):** both readers agree on each.
  - **047:** the Dolgachev–Weisfeiler fibrations. The Lean states only ring-level cancellation.
  - **079:** maximal Bochner–Riesz, paraboloid and cone restriction, Schrödinger smoothing, Nikodym.
  - **091:** the B-conjecture.
  - **180:** the Pfaffian three-edge-path form. The Lean states planar Barnette.
  - **183:** the k-dependent k-set bound. The Lean states one uniform n^{4/3−ε} bound under extra genericity.
  - **230:** finiteness of the gauge measure, i.e. Schramm's exact gauge. The Lean states positivity only.
  - **299:** the Dadarlat–Toms answer, borderline: the Lean states only the criterion.
  - **350:** growth faster than λ^{1/2+ε₀} in dimension five. The Lean states only an unbounded ratio.
- **Minor (11):** a sharpness remark, a standard corollary, or a consequence through a cited theorem: 072, 089, 097 (O26's document: Θ(√d) needs a lower bound the Lean lacks), 162, 172 (O21: the LRW disproof rests on LRW's own cited non-subtransitivity), 246, 273, 274, 297, 303, 326.
- **Disclosed (33):** 017, 027, 052, 087, 088, 096, 103, 126, 131, 152, 159, 161, 179, 191, 194, 195, 199, 242, 244, 252, 266, 269, 272, 276, 280, 281, 287, 301, 312, 323, 367, 371, 373.
- **Matches:** every other item.
- **Scope documents that contradict their own links (they understate the Lean; not overstatements):**
  - 087 says "the nonsymmetric Mahler conjecture … not included" but links `GeneralMahler`.
  - 167 says "the separate unit-distance power-saving theorem is not included" but links `PlanarUnitDistances`.
  - 243 says "witnessed-symmetric-choice … not included" but links `WitnessedChoice`.
  - 052 is inconsistent on integrability.

**Final count, all 246 Lean-linked CONTENTS items read by two readers:**

- **51 overstate the Lean.** Their headline under "[Lean]" makes a main claim that no linked Lean statement states or
  obviously implies, and the scope text does not say so.
- 11 have a minor version of the same gap.
- 54 disclose their gaps.
- The other 130 match.

The single most consequential is item 143: "Resolves the uniform boundedness assertion in Hilbert's sixteenth
problem", where the Lean covers quintic Liénard systems only.

Limits of this verdict:

- It judges the index, not the proofs.
- Each "overstatement" says only that the Lean does not state the headline. It does not say the headline is false.
- Every judgment is a reading by model readers. Two readers agree on each verdict, but none of these verdicts is
  closed in Lean.


## O38–O40 (run 2026-11-27T1317Z; brief d66b2e9, readings committed alone; files `runs/2026-11-27T1317Z/O/{fixedpoint,anderson,erdosap}/`)
`family_map.py` first (one challenge each; scope documents 328, 261, 159). Readers A (Opus), B (Sonnet), C (Haiku);
reader C ran one `ls` of the brief's directory (family names only). Closures compiled locally against the frozen
statements (standard axioms): O38 3/3 Theorem 1.1, O39 3/3 conclusion (i), O40 3/3 Corollary 1.2. Escape scans
(`scan/`): O38 86 files, no hits; O39 1 file, no hits; O40 4,774 files with 11,722 `local notation` lines and no other
hits. Readers' remaining claims (O38 Corollary 1.2; O39 (ii)–(iv); O40 Theorem 1.1, threshold) have no Lean
statement: disclosed for O39 and O40, not mentioned for O38's corollary.


## O41–O43 (run 2026-11-27T1317Z; brief c15d791, readings committed alone; files `runs/2026-11-27T1317Z/O/{hadwiger,listhadwiger,rokhlin}/`)
Closures compiled locally against the frozen statements, standard axioms: O41 3/3 "Hadwiger's conjecture is false";
O42 3/3 Theorem 1.1; O43 1/3 explicit Theorem 1.1. Scans: O41 288 files, O42 53 files, no hits; O43 13 files,
32 `local notation`/syntax lines, no other hits. Both frozen junk-value risks were checked rather than assumed: the
Hadwiger number is an `sSup` (bounded: proved) and the list chromatic number an `sInf` (nonempty: proved by Hall).

## O44–O46 (run 2026-11-27T1428Z; brief 0ed6b5c, readings committed alone at 2dc1534; files `runs/2026-11-27T1428Z/O/{seymour,zerodiv,moat}/`)
Families chosen by `family_map.py`, smallest challenge first among the unread ones; 066 (bounded klt complements, 37
lines) was skipped for now: its only challenge is a supporting lemma stated with the release's own definitions
(`closedChartFieldRetraction`, `normalizedWeights`), and the scope document says the headline is outside the Lean.
Closures compiled locally against the frozen statements (our Mathlib), standard axioms: O44 3/3 both directions;
O45 3/3 Theorem 1.1 and 3/3 "conjecture false", 1/3 "Moreover"; O46 3/3 on each of its three claims. Scans: O44 43
files, O46 41 files, no hits; O45 123 files, 204 `local notation` lines and no other hits.
Brief defect (ours): the O44 excerpt ended one line before the directed-triangle sentence; readers A and B wrote
that theorem from memory and said so, C left it out. Those two are not readings and were not closed. Reader C
wrote torsion-freeness as Mathlib's `IsMulTorsionFree` (equal powers of commuting elements are equal); it is
proved equivalent to the frozen "no nontrivial element of finite order" for groups (`tf_iff_mulTorsionFree`).
