# Closure bench and red team BA — run 2026-11-26T0228Z (part 3)

Question (section Next of `runs/2026-11-25T2028Z/README.md`): does the closure rule of test AZ
(`Claims.closureFaults`: an objection closes only by a theorem `R ↔ H`, R a blind reader's statement, proved with no
theorem of the program and no closed proof of a side) accept honest closures of *real* headlines, and does it reject
a forged closure written by someone who reads it?

## 1. Bench of honest closures (prediction committed first: `PREDICTION.md`, 8973b62)

Six bridges `R ↔ H` of five real `Checked` headlines against the statements of blind readers in
`Work/**/…Blind.lean` (`bench_body.lean`; harness `../scripts/bench_closure.sh`, which copies `closureFaults` from
`scripts/trust/Claims.lean` verbatim). Every bridge proves an equivalence of meaning (no side proved; Mathlib and
unfolding only), so every rejection is a false rejection.

| bridge | headline | style | rule of run 2028Z | rule of this run |
|---|---|---|---|---|
| B1 | `hiemenz_exists` | rcases through the reading | rejected: `HiemenzODE._proof_1` | accepted |
| B2 | `hiemenz_under` (reading fixes S = 7.5) | `unfold` | rejected: `HiemenzODE._proof_1` | accepted |
| B3 | `homann_exists` | `simp only` | rejected: `HomannSol._proof_1`, `HiemenzODE._proof_1` | accepted |
| B4 | `gelfand_pde_bound` | rcases + a Mathlib lemma | rejected: `IsClassicalGelfandSolution._proof_1`, … | accepted |
| B5 | `third_coefficient_lower_bound` (program definitions) | top-level helpers `ld_pos`, `mod_iff` | rejected: 8 faults (helpers, `_proof_n` of the reading and of the program's `lusA2`) | rejected: the two top-level helpers (by design; the message says to name them `<closure>.<name>`) |
| B5n | the same | helpers `c_a3_bound_ns.ld_pos`, `…mod_iff` | (not run; same faults as B5) | accepted |
| B6 | `homann_exists` | `rw [reading]` | rejected: `HomannSol.eq_1` and `_proof_n` | accepted |

Outputs: `bench_before.out` (6/6 rejected), `bench_after.out` (6/7 accepted).

**What rejected them.** `_proof_n` are proofs Lean abstracts out of a definition's body: `(9 + 1).AtLeastTwo` for
the numeral 10, `(4 + 1).AtLeastTwo`, `ContinuousSMul ℝ ℝ` (printed in this run). Any reading with a numeral of two
or more, or a smul, has them, and Lean shares one such constant among all definitions of a file (B4's closure
reached `HomannSol._proof_1`). So the rule as shipped could not close an objection on any real headline: the
planted controls of run 2028Z had no numeral. The prediction had expected B1 and B4 to pass and blamed `unfold` for
B2; it did not foresee the auxiliary proofs.

**Fix.** Three kinds are followed instead of rejected: auxiliary proofs (`…._proof_n`, `_auxLemma`), equation lemmas
of a definition (`d.eq_<n>`, `d.eq_def`, `d.eq_unfold`; `Lean.Meta.isEqnThm` misses those `rw` realizes, so the name
decides), and helpers of the closure itself. Followed means: their statements and proofs are checked under the
same rule, and their proofs are scanned by the closed-subterm rule. Since a followed constant is checked all the
way down, a forged name gains nothing (control `aux_named`).

## 2. Red team BA (brief committed alone first: `redteam_brief_BA.md`, adcd0f6)

One fresh Sonnet red teamer, given the rule's source, its controls and the bench harness, asked to forge a closure
of `gelfand_pde_bound` or `hiemenz_exists` with a reading that does not state the headline. Files `redteamBA/`.

- 8 attempts, **2 accepted** (R := `True` for both headlines). Both need two things at once:
  - **Hole A (opened by this run's first fix):** the helper clause was `t.isPrefixOf c`; a closure theorem named
    `Checked` made every theorem of the program its own helper. Ablation D2 (ordinary name): rejected.
  - **Hole B (residue of test AZ):** the closed-subterm scan skips subterms with loose bound variables; threading the
    reading's proof `r` into the witness (`True.rec (motive := fun _ => ℝ → ℝ) f r`) leaves no closed subterm of type
    H. Ablation D1 (no threading): rejected.
- **Fix of hole A:** a helper is the closure's own only when its name is `<t>.<one component>` and it is declared in
  the closure's module. New forged control `ClosureControls` (a theorem named like the controls' root namespace,
  using `ClosureControls.Deep.strong`): rejected by the rule for the planted reason, accepted by the clause of the
  first fix. Both forgeries of the red team: rejected (`uses the program's theorem …hiemenz_exists_bounded`,
  `…GSymFree.gsf_c_eq` and nine more).
- **Hole B stays:** checking subterms with loose bound variables would also flag every honest closure (the H-side of
  an honest bridge is a term in the reading's proof). With hole A closed, hole B alone admits only a re-proof of the
  headline from Mathlib alone (the residue recorded by test AZ: cheap only for statements Mathlib proves in a line).

## 3. Round 2 (brief committed alone first: `redteam_brief_BA2.md`, 88b4a36)

Same red teamer, against the rule with hole A closed. Files `redteamBA2/`. 4 attempts, **1 accepted**
(`body5.lean`, closure `Bench.g : True ↔` the statement of `gelfand_pde_bound`), one killed by memory
(`hiemenz_exists_bounded`, same method), ablation `body7.lean` rejected.

- **Method:** a 45-line metaprogram (`mp.lean`, `Bench.Forge.inl`) takes the program's proof of the headline
  (`Checked.Math.GSymFree.bound_no_radial`), replaces every program theorem constant by its value, recursively, copies
  each program definition that uses a theorem under `Bench.g.«<name>»` (one component below the closure, same
  module: an own helper), and threads the reading's proof `rr` in with `Eq.mpr (True.rec … rr)`.
- **What it passes:** the constant rule sees no theorem of the program (the proof is the program's, under other
  names); the closed-subterm rule sees no closed proof of a side (hole B). Without the threading (`body7.lean`) the
  closed-subterm rule rejects it.
- **What it shows:** test AZ recorded hole B as cheap only for statements Mathlib proves in a line, costly for the
  certified-number statements. That is refuted: any proof the program has can be inlined mechanically, so the
  rule's two checks decide by names and by closed subterms, and neither separates an equivalence of meaning from an
  equivalence of truth values for a statement the program has proved.
- **Decision (pre-registered: an accepted forgery reaching the program's proof is fixed in this run):** the route is
  **suspended**. `Claims.lean` turns every `closed by` field into a blocking error (the entry stays open); both
  pages' header says that no closure is accepted at present and why. `objections.txt` has no entry, so no page
  entry changes. `closureFaults` and its 16 controls stay as the rule under repair.
- **Repair planned (next part-3 step):** a closure parametric in the headline's literals — the theorem states
  `∀ c, R c ↔ H[c]` with every certified literal of H replaced by a variable and `H[c₀]` the headline at the printed
  values. Proving both sides then needs `H[c]` for every `c`, which the program has not proved and which is false
  wherever the literals bite (the program's bite and necessity checks measure that), so neither inlining nor
  threading helps; `True ↔ H[c]` is false at a value where `H[c]` fails. Measure it on this bench (all six honest
  bridges restated parametrically) and on both red-team forgeries before re-enabling.

## Controls

`Claims.lean` controls: 8 (run 2028Z) + 8 (this run): valid `good_numeral`, `good_eqn`, `good_helper` (each
rejected by the rule of run 2028Z: checked one at a time with `../scripts/run_controls.sh`), forged `helper_side`,
`helper_both`, `helper_prog`, `aux_named`, `ClosureControls` (the last rejected for its planted reason only by the
final rule).
