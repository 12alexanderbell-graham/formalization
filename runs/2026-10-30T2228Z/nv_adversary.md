# Adversarial review of the non-vacuity check (subagent, run 2228Z)

Reviewer: general-purpose subagent, told to break `Checked/Trust/NonVacuity.lean` +
`scripts/trust/StatementDeps.lean` (first version, commit d681e9c). Experiments in a temp dir; no
repo files changed by the reviewer. Findings (most severe first) and what this run did:

| # | Finding | Severity | Repo affected? | Action (same run) |
|---|---|---|---|---|
| 1 | Hypotheses hidden behind a `def`/`abbrev` (`theorem : Claim`, `def Claim := ∀ …, H → P`) were invisible to the non-reducing telescope: obligation `True`. | HIGH | No (all 26 `Claim` headlines are `¬ Claim` with `Claim` a `∀`; a refutation carries its own counterexample), but nothing prevented a positive `theorem : FooClaim`. | `unfoldHead`: heads that are `Checked` definitions (or reducible) are unfolded before telescoping. Toy `hiddenAbbrev` now needs a witness. Limitation: definitions outside the `Checked` namespace are not unfolded (none are used by headlines). |
| 2 | `¬ ∃ x, H x ∧ P x` (= `∀ x, H x → ¬ P x`) treated as a refutation. | MEDIUM | No | Negated existentials are rejected with an error ("state it as ∀ … → ¬ …"). |
| 3 | Hypotheses inside `∧` / `↔` conclusions ignored; `A ↔ B` with both sides unsatisfiable passes. | MEDIUM | The four `program ↔ blind` equivalences were unconditional. | `A ∧ B` ↦ obligations of both; `A ↔ B` ↦ `A` must hold somewhere. Four new witnesses (`isFlatLCDM_iff_friedmann`, `isFlatCPL_iff_friedmannCPL`, `friedmannEq_iff_blind`, `masterEq_iff_blind`). |
| 4 | Trailing-`False` rule could drop a data binder (`∀ x : {r // r < r}, False`). | LOW | No | Pop only if the last binder is a proposition. |
| 5 | Witnesses at degenerate points (`t = t₀`: redshift and distance 0). | LOW–MEDIUM (by design) | Six pin witnesses. | Pin witnesses now use `t = −1 < t₀ = 0`. General "typical instance" check left to T2 (manual list). |
| 6 | Impossible data types (`Fin 0`, `{x // False}`) | — | — | Correctly need witnesses (unprovable). |
| 7 | `==` matching: no false accepts found; false rejects for universe-polymorphic headlines and inhabited types not on the plain list. | LOW | No | Plain type := non-Prop with a `Nonempty` instance (`synthInstance?`). |

After the fixes: 101 headlines, 62 conditional, all witnessed (CI-blocking).
