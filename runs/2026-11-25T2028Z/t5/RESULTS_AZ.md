# Test AZ — may a fidelity objection leave the claims page by a recorded event? — run 2026-11-25T2028Z

Brief and decision rule: `reader_brief_AZ.md`, committed alone (76727bd) before any reader ran. Material:
`reader_material/{O,V,E}.md`, made by `runs/2026-11-25T2028Z/scripts/material_az.py` from AY's d04 material (the open
entry on `lookback_second_order_bigO`, whose note withdraws its query). Six fresh blind Sonnet readers, launched in one
message, each told to read one file and use no other tool; the files were copied to `/tmp/rmAZ/<k>/page.md`
(k = 1 … 6; one directory per reader instead of the brief's single `/tmp/rmAZ/page.md`, since six read in parallel;
the name says nothing). Readers 1, 4: O; 2, 5: V; 3, 6: E. Answers condensed; the deciding words quoted.

| version | reader | (3) cites? | deciding words |
|---|---|---|---|
| O (open, AY d04) | 1 | no | "Not yet … I wouldn't cite it until the open objection 1 (referee note) is read and resolved" |
| O | 4 | no | "a recorded fidelity objection is open with its content hidden and its settlement unknowable from this page" |
| V (closed by a verdict path) | 2 | yes | "its only recorded objection is closed … I would read the referee verdict before relying on the exact form" |
| V | 5 | yes | "The closed objection and the unread literals are the residual reasons for care" |
| E (closed by a checked equivalence) | 3 | yes | "its one recorded objection is closed … I would not treat the closed objection as confirming fidelity to a specific source" |
| E | 6 | yes | "its sole recorded fidelity objection closed … I rely on the generated record that the closure exists" |

All six readers also raised the same unrelated caveats (no positivity or expansion hypothesis; one redundant
hypothesis not named on the page; five literals never read twice); they are the same in every version.

**Decision (by the pre-registered rule):**

1. O control 2/2 decline: AY's result reproduced; the test discriminates.
2. V: 2/2 cite. A path-only closure lifts a recorded doubt for readers exactly as well as a checked one, and its
   closing file is author prose the program writes: a forger with a real objection writes the same file. **V stays
   out** (rule 1); this is the measured reason.
3. E: 2/2 cite. **E is adopted** (rule 2): `objections.txt` fifth field `closed by <theorem>`; `Claims.lean`
   `closureFaults` with eight planted controls run before any page is written; header text of both pages;
   `check_claims.py` O1 counts an entry by its first four fields (controls `closed`, `reworded`).

**What E still lets a forger do** (the rule's residue, stated on the page's header only as far as the rule goes):

- *A non-blind reading.* The reading must be a definition of a `Checked.Trust.SecondReading*` module, so the
  blind-route checks (brief committed alone before the reading, brief frozen, no answer in the brief:
  `check_blind_route.py` B1–B5, `check_brief_leak.py`) apply; an author who writes the "blind" reading himself in a
  separate commit passes them, the same residue as every second reading of the program (round L limit 1).
- *Both sides proved outright.* `iff_of_true` makes any two proved propositions equivalent. Two rules of
  `closureFaults` stand against it: no theorem of the program anywhere in the proof (controls `uses_head`,
  `uses_helper`, `uses_stored`), and no closed subterm of the proof is a proof of either side by itself (control
  `reproves`: both sides re-proved from the core library alone, rejected). A determined forger can still thread a
  bound variable through a re-proof so that no closed subterm proves a side (in the scratch test of this run, the
  attempt `fun w n => (fun _ => Nat.add_zero n) w` was still caught, through the closed constant `Nat.add_zero`, whose
  statement is the toy headline's); the residue is a re-proof of the whole headline written to avoid closed proofs of
  it, without any of the program's lemmas: cheap for a statement Mathlib proves in a line, costly for the
  certified-number statements. The second rule can reject an honest bridge whose proof uses a library lemma whose
  statement is one of the sides (scratch test: `forall_congr' fun m => by rw [Nat.zero_add, Nat.add_zero]` on the toy
  headline `∀ n, n + 0 = n`, which is itself `Nat.add_zero`); a headline that is a library lemma needs no closure.
  Valid bridges accepted in the scratch test: `Iff.rfl`, `forall_congr' fun _ => Iff.rfl`, `simp only [the reading]`.
- *A reading of a different source.* The page does not name the source the reading was made from; the reader's
  brief names it and B3 keeps the answer out of it.

**Measure:** readers who cite after a closure: V 2/2, E 2/2; O 0/2. Forged closures rejected by the generator's
controls: 6/6 (valid controls accepted 2/2). The proof-constant rule is the first check in the program that tells an
equivalence of meaning from an equivalence of truth values.
