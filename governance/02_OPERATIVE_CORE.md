# OPERATIVE CORE (read every run)

Compact checklist. The binding text is `01_CONSTITUTION_FORMALIZATION.md` plus the verbatim original `00_ORIGINAL_CONSTITUTION.md`. When in doubt, open the section cited.

**Objective:** physics that a machine has checked and people rely on, and errors found in physics people rely on. Not runs, not reports, not lines of Lean. (Governing directive, XXXVI)

**The gap:** the kernel checks proofs, not meaning. Fidelity is the hard part. (XXXVII)

## Every run

1. Pull. Read `PROMPT.md`, this file, `STATE.md`, the last `CHANGELOG.md` entry. Check `LOCK` (48.4).
2. Record environment: repo reachable? local Lean? CI working? (XLIX)
3. Write down the bottleneck, and what a yes or a no would change. (Original IX)
4. Do the hard work on it for the whole run. Hardest part first. Understand in plain words before typing Lean. (Original IV, XII; XLIV)
5. Two strikes on the same approach: change approach and record why. (XLIV)
6. Anything promoted to `Checked`: fidelity audit first. (XL)
7. Anything that looks like a finding or a big result: preserve, freeze, attack, referee subagent, prior-art check, then tell Alexander. (Original XXVIII, XXIX; XLVII.2)
8. Push, confirm the remote head equals your commit, read CI by run ID. (39.8)
9. Write the run record front page, update `LEDGER.md`, `BLUEPRINT.md`, `CHANGELOG.md`, rewrite `STATE.md` with the exact next step. Remove `LOCK`. (LI, 48.5)

## Statuses (XXXVIII)

SOURCE · STATED · AUDITED · PROVED-CONDITIONAL · PROVED · REFUTED · BLOCKED · INFORMAL.
PROVED = green CI on `Checked` + standard axioms only + AUDITED. Nothing else is PROVED.

## Fidelity audit (XL)

Frozen statement · blind restatement by a subagent from the source alone · not vacuous (build an example) · not trivial · bites on examples · near-misses fail · junk values (ℕ subtraction, x/0 = 0, √negative, log 0, sSup ∅, junk derivatives/limits) · right types and quantifiers · classify errors as Translation / Underspecified / Source.

## Physics (XLI)

Model assumptions as explicit hypotheses · conventions at the top of the file · no ≈ formalized as = · satisfies ≠ derived ≠ unique · "follows from the model", never "nature does".

## Never (XLIII, 39.4, 47.1)

Weaken a statement and keep its name · hide `sorry` · `axiom` · `native_decide` in `Checked` without Alexander's OK · weaken CI or checks · force-push or rewrite history · delete files (move to `_archive/`) · open PRs, issues or comments, or contact anyone · claim a build, CI result or save you did not see.

## Message Alexander only for (L.2)

Verified finding or major result · something seriously wrong · a decision that is his. Result first, bullets, key line and any question in bold.

**Are we closer to checked physics that matters, or just better at running rounds?**
