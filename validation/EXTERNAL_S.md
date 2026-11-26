# External test, target S: Lean-formalized Erdős claims of OpenAI's math release

Standing instruction 11. Run 2026-11-26T1529Z. Source: github.com/openai/math at
3344da59991ed94f9ba711217b29c1d760badfa6 (2026-11-24 head; release of 2026-10-06 plus later additions),
AI-written manuscripts, not peer reviewed. Families taken smallest Lean closure first, among those whose
headline claim resolves an Erdős problem and whose comparator challenge needs only Mathlib.
Verdicts committed before any review, forum thread or blog post on these families was read.

Every link below was produced in this run; files under `runs/2026-11-26T1529Z/S/`.

## Method (the same for each family; general tools in `scripts/external/`)

1. Source read literally: the erdosproblems.com statement (fetched by a subagent instructed to return the
   statement only) and the manuscript's headline theorem (from the TeX in the release).
2. Blind reading: brief committed first (`*/brief.md`, commit 0be6d39), then a fresh Sonnet reader wrote a
   Lean statement from the brief alone (`*/reading.lean`, commit b9f6f85), then the closure was written
   (`*/closure.lean`, commit e98ce7c). Three commits, in that order.
3. Closure: the frozen comparator statement (`lean/ComparatorChallenges/*.lean`, taken with `type_of%`,
   never retyped) proved equivalent to, or to imply, the reading. Checked in the release's own pin
   (Lean 4.34.1, Mathlib d13f23b), axioms propext, Classical.choice, Quot.sound.
4. Definition pins (`S/pins.lean`): each frozen definition evaluated on a hand-known case.
5. Solution: import closure of the solution module extracted into a minimal project
   (`scripts/external/replay.sh`), built with the Mathlib cache; Match file = the challenge verbatim in
   namespace `Chal` with its `sorry` replaced by the solution theorem (compiles only if the solution proves
   the challenge statement with the challenge's definitions); `#print axioms`; nanoda (independent Rust type
   checker) on the export of the matched theorem and every dependency, Mathlib included; leanchecker
   per module; advisory scan for `sorry`/`axiom`/`native_decide`/`implemented_by`/custom syntax.

## S1. Erdős Problem 304, short Egyptian fractions (family 025) — **DONE**

- Claim (erdosproblems.com 304): N(b) = max_{1≤a<b} N(a,b) ≪ log log b, N(a,b) the least number of
  distinct unit fractions 1/n_i, 1 < n_1 < … < n_k, summing to a/b. Manuscript Theorem 1.1: c₁ log log b ≤
  N(b) ≤ c₂ log log b for b ≥ b₀.
- Frozen statement `OAI.ShortEgyptian.main`: existence of expansions for 1 ≤ a < b, and the two-sided bound.
- Closure: frozen ⟺ (blind reading of Theorem 1.1 ∧ existence of expansions); frozen ⟹ the reader's form of
  Erdős 304 (`closure`, `closure_erdos`). The existence conjunct is what keeps `sInf` from a junk 0.
- Pin: `minLength 2 3 = 2` (2/3 = 1/2 + 1/6; not a unit fraction).
- Observation: the frozen `IsExpansion` elaborates `(ns.map (fun n => (1:ℚ)/(n:ℚ))).sum` by lifting the
  list through the list monad (`do let a ← ns; pure ↑a`); harmless (lemma `key`), but it is not the term
  a reader sees.
- Solution: 58 modules (8,140 lines), Mathlib only. Build green; Match green, axioms
  standard; nanoda: 45,753 declarations, no type errors (33 s); scan: no hits.
- Links resting on judgment: the blind reader's Lean rendering of the English (one reader, Sonnet).

## S2. Erdős Problem 184, Erdős–Gallai cycle decomposition (family 181) — **DONE**

- Claim (erdosproblems.com 184): any graph on n vertices decomposes into O(n) edge-disjoint cycles and
  edges. Manuscript Theorem 1.1: an absolute C > 0 with a partition of E(G) into at most Cn parts, each a
  cycle's edge set or a single edge.
- Frozen statement `OAI.ErdosGallai.erdos_gallai`: ∃ C > 0, ∀ n, ∀ G on Fin n, a decomposition with k ≤ C n.
- Closure: frozen ⟺ blind reading (which quantifies over every finite vertex type; transport along
  `Iso.comap`).
- Pins: K₃ has a 1-part decomposition and no 0-part decomposition.
- Solution: 34 modules (21,451 lines), Mathlib only. Build green; Match green, axioms standard; nanoda:
  41,966 declarations, no type errors; scan: no hits.
- Links resting on judgment: the blind reading.

## S3. Erdős's superexponential van der Waerden question (family 160) — **DONE**

- Claim: Erdős (1980, p. 90 (2), as cited): W(k)^{1/k} → ∞. Manuscript Theorem 1.1: W_r(k) >
  k^{c k ⌊log₂ r⌋}, c = 10⁻⁵, for k ≥ K₀, r ≥ 2. (The erdosproblems.com number of this question was not
  found by the statement fetch; the source used is the manuscript's citation of Erdős.)
- Frozen statement `OAI.QuantitativeVanDerWaerden.uniform_lower_bound`, with W = sInf of good N over
  colourings of {0,…,N−1}.
- Closure: frozen ⟺ blind reading (colourings of {1,…,N}, W as `IsLeast`, existence asserted);
  frozen ⟹ the reader's corollary (∀ r ≥ 2, W_r(k)^{1/k} → ∞) and Erdős's form (r = 2). The reading demands
  that W_r(k) exist for every k ≥ 1, which the frozen statement does not give for small k: proved here
  from Mathlib's Hales–Jewett theorem (`vdw_finite`), so no junk `sInf` anywhere.
- Pin: W₂(2) = 3 (fixes the interval {0,…,N−1}, the strict bound and d > 0).
- Solution: 115 modules (14,837 lines), Mathlib only. Build green; Match green, axioms standard; nanoda:
  36,021 declarations, no type errors; scan: no hits.
- Links resting on judgment: the blind reading; the identification of Erdős's question (no
  erdosproblems.com statement fetched).

## Not done in target S (blockers, `EXTERNAL_BLOCKERS.md`)

- S4 cycle–clique Ramsey numbers (Erdős–Faudree–Rousseau–Schelp, family 189): frozen statement read; its
  solution closure is 443 modules / 2.8 M lines, too large to build here in the time of this run; replay
  queued on GitHub (`validation/external_replays.txt`, workflow `external.yml`).
- leanchecker (the toolchain kernel's replay, second independent check after nanoda): running module by
  module locally (one process over a closure was killed by the sandbox memory limit at 4.5 GB, and a CI
  runner was shut down in the same step); result recorded in the run README when finished.

## Time

Statement fetch to three closures: 15:35Z–16:05Z (30 min). Builds and replays: 15:55Z–16:45Z on two cores.
