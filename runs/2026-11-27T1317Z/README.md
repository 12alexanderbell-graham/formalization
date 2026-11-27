# Run 2026-11-27T1317Z (external test long run: target O from O38)

**THE RESULT:** part 2 and part 3 (the trust system on AI-produced mathematics it did not make): six more families
of OpenAI's release were read blind by three models, and the readings were closed in Lean against the frozen
statements. Among them are three famous problems: Erdős's reciprocal-sum conjecture (O40), Hadwiger's conjecture
disproved (O41) and Rokhlin's multiple mixing (O43). The release's Lean statements say what the manuscripts claim, at
every link closed here. Where the Lean covers less (pure-point spectrum, the AP density bound, χ_f), OpenAI's scope
documents say so.

**What can a scientist now trust without checking it themselves, that they could not before?** That the Lean
statement "Hadwiger's conjecture is false" in OpenAI's release (`not_hadwiger_conjecture`) means what three
independent blind readings of the paper mean. The frozen Hadwiger number is a genuine maximum (proved here: a K_t
minor has t ≤ |V|), not an unbounded `sSup` that would default to 0. The same holds for the linear list Hadwiger
bound (the frozen list chromatic number's `sInf` is over a nonempty set, by Hall), for Erdős's reciprocal-sum
statement, for the reflexive fixed-point theorem, and for the Anderson spectrum. All of these are closures checked
locally with standard axioms; their replays at OpenAI's pin are queued.

**Weakest unchecked step:** no family of this run is DONE. Every replay, both target R leanchecker sets, and the O10
and O38–O43 closures at OpenAI's Mathlib pin are queued behind GitHub's job limit (backlog since 10:22Z; one
O-sunflower replay job has run 4.5 h). The closures were compiled only against this repository's Mathlib.

## Start
- 13:17Z. A manual firing brought context from Alexander's chat session (~12:50Z): continue the long external run.
  The Target O correction it asks for first was already done by run 1248Z (Correction 2 and Index check).
  `EXTERNAL_LOCK` taken at 00a47fc. `LOCK`: run 1228Z (part 1); its files were left alone.

## Target R
- Run 45985482988 (Sernau leanchecker shards) is still queued (status read 13:20Z and 13:55Z). There is no verdict
  change; the original archive is still blocker R1.

## Target O, O38–O43 (`validation/EXTERNAL_O.md`)
- Every family started with `family_map.py`. Briefs (d66b2e9, c15d791) were committed before the readers ran, and
  the readings were committed alone. Readers: A (Opus), B (Sonnet), C (Haiku). Two process deviations were reported
  by reader C (one `ls` of family names; a scratch log under /tmp); no other source was opened.
- O38, reflexive fixed points: 3/3. Reader C omits completeness; this run proves that a space whose canonical map
  into the bidual is onto is complete. The commuting-families corollary has no Lean statement.
- O39, planar Anderson: spectrum 3/3, across three models of the randomness transported to the frozen product law.
  Pure-point type is disclosed as outside.
- O40, Erdős reciprocal sums: 3/3. The density bound is disclosed as outside. The solution closure is 4,774 files.
- O41, Hadwiger counterexample: "conjecture false" 3/3. χ_f is disclosed as outside. Theorem 1.1 (cm) closures were
  not written.
- O42, linear list Hadwiger: Theorem 1.1 3/3.
- O43, Rokhlin: reader A's explicit form closed. B, C and the every-order forms are not written.
- Replay lines were added and dispatched (O-fixedpoint, O-anderson, O-erdosap; O-hadwiger, O-listhadwiger,
  O-rokhlin).

## Next
- CI: when the queue moves, read every external replay run from 45981618513 on. In particular:
  - Target R leanchecker (45985482988): then give the final proof verdict for the Sernau editions, and compare with
    the published checks.
  - O-noncoord-cd and O38–O43: a closure failing at OpenAI's Mathlib pin is a name change (see the O13 precedent).
- Open closures: O41 Theorem 1.1 (Sym2 edges ↔ two-element finsets; frozen `connectedMatchingNumber` boundedness);
  O43 B and C; O42 and O41 corollaries derived from the frozen theorems; and the earlier list in run 1248Z's Next.
- Then target O from O44, smallest challenge first by `family_map.py`. Candidates: 126 perfect-matching PSD rank,
  198 finitistic dimension, 066 klt chart (a supporting lemma, disclosed), 325 Crouzeix. Then target M.
- Message Alexander with the O-table at O47 (ten families after O37).
