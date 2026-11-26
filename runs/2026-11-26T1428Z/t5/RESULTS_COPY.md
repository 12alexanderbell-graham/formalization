# A copied reading against the closure rule and the blind route — run 2026-11-26T1428Z (part 3)

Question (section Next of `runs/2026-11-26T0828Z/README.md`): closures of fidelity objections were suspended because
red team BB passed `Claims.paramClosureFaults` with a reading that restates the headline beside a disjunct true at a
re-spelt literal. The planned repair was a check on the reading's provenance: accept a closure only on a reading whose
module `scripts/trust/check_blind_route.py` accepts. Can an author-written reading still close an objection?

Pre-registered decision (this file's first version, before the Lean run): if a reading written by the author passes
both the closure rule and the route, closures are abandoned, not suspended, and the planned provenance check is not
built (it would be a check of who wrote a commit).

## 1. The reading needs no re-spelling: a copy of the headline

`paramClosureFaults` rejects a reading side that contains the headline's statement as a *proper* part, and must accept
a reading side *equal* to it: an honest blind reading that agrees with a faithful headline can be the same term (the
Gelfand bound read blind is `∀ λ u, … → λ ≤ 3.321992119`, the headline's own shape). So the author can offer the
headline's statement itself as the reading, and the closure is `fun _ => Iff.rfl`.

Harness `t5/copy_body.lean` (run with `runs/2026-11-26T0828Z/scripts/run_pclosure.sh scripts/trust/Claims.lean
runs/2026-11-26T1428Z/t5/copy_body.lean`; output `t5/copy.out`):

| case | headline | reading | expected | result |
|---|---|---|---|---|
| C1 | `gelfand_pde_bound` (faithful) | copy of its statement | accepted (indistinguishable from an agreeing blind reading) | see `copy.out` |
| C2 | `CBench.weak_bound`, planted unfaithful (3.5 for the source's 3.321992119; true, proved from the program's theorem) | copy of ITS statement | accepted: the objection "the source says 3.321992119" is closed | see `copy.out` |
| C3 | `CBench.weak_bound` | the C1 copy (λ ≤ 3.321992119) through C1's closure theorem | rejected (control) | see `copy.out` |

The honest blind reading of the source (λ ≤ 3.321992119) cannot close C2's objection: `∀ c, (… → λ ≤ 3.321992119)
↔ (… → λ ≤ c)` is false at c = 3.4, so no closure theorem exists. The rule therefore separates C2's forged closure from
the honest attempt by one thing only: who wrote the reading.

## 2. The route accepts the copy

Local scratch branch `scratch-route-1428` (never pushed), base 422b684 (this run's LOCK commit), three commits as the
protocol asks: brief `runs/2026-11-26T1428Z/routedemo/reader_brief.md` (describes the source in words, no numbers),
then the reading `SecondReadingGelfandCopy.lean` alone (the C2 copy, `λ ≤ 3.5`, written by the author), then its
code-identical copy `Checked/Trust/SecondReadingGelfandCopy.lean`:

- `check_blind_route.py --base 422b684`: `1 second versions added or changed since 422b684ffe4d; ok`
- `check_brief_leak.py --base 422b684`: `1 briefs of reader files new since 422b684ffe4d; ok`
- `check_provenance.py --base 422b684`: `78 second-version modules, 6 baselined; ok`

This is the residue `check_blind_route.py`'s own docstring records ("An author who writes a brief without the answer,
commits it, writes a forged reading in a separate commit touching only runs/, and copies it in a third commit passes
every rule here"); it is now measured with the closure rule in the same case.

## 3. What follows

- **Closures abandoned (pre-registered).** Every check met on this route is a check on text or commit order, and the
  author writes every commit. A reading that agrees with the headline is the same object whether a blind reader or the
  author wrote it. `Claims.lean` keeps rejecting every closure field, now with the reason; `objections.txt` and both
  pages' header say so; an entry leaves only when its headline is re-frozen or withdrawn.
- **The pages now say what "blind" means on them.** The fidelity records print "blind second readings"; the header now
  says that CI checks a reading's route (brief first, no numbers in it, reading alone, then the copy), not that its
  reader was blind, and that an author-written copy passes the same checks.
- **Settled with it:** section Next of `runs/2026-11-25T1428Z/README.md` asked whether an entry may leave the registry
  through a recorded event other than a re-freeze (a blind referee's verdict committed alone under `runs/`). Same
  answer: such an event is a commit the author can write; no.
- **Where blindness can be evidenced:** only by a party outside the program's commits — the outside reviewers of
  THE RESULT part 4 (`validation/`). Inside the repository, the trust a reader can place in a fidelity record rests on
  what a machine re-derives (non-vacuity witnesses, necessity theorems, parametric equivalences between two given
  statements), not on who wrote a statement.

## 4. Measure

- Forged closures accepted by the rule the page runs: copy of the headline 2/2 (C1, C2), control rejected (C3).
- Author-written readings accepted by the blind-route checks (`check_blind_route`, `check_brief_leak`,
  `check_provenance`): 1/1.
- Forged closures the page can show as closed: 0 (closures abandoned; the closure field is a blocking error).
