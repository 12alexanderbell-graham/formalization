# Run 2026-11-08T1228Z (scheduled)

**THE RESULT:** parts 2 and 5 (in progress, auditor role: run 1028Z holds the LOCK): the class of the Hiemenz/Homann uniqueness theorems widened from "f'' > 0" (a condition on the unknown's second derivative) to Coppel's physical class "−1 ≤ f' ≤ 1", and "same wall shear" upgraded to "the same solution"; compiled in scratch Lean, waiting for the LOCK to be released before freeze → Work.

## Start
- 12:27Z. Pre-cloned checkout detached with a stale local `main`; `git reset --hard origin/main` (local only) = c8c8253.
- LOCK: run 2026-11-08T1028Z, taken 10:37Z, heartbeat 12:05Z (alive, < 150 min) → rule 48.4: auditor/referee role; writes only in this folder plus a CHANGELOG append; next-step theorem built as scratch Lean here (PROMPT working note "A live LOCK is not idle time").
- Environment: repo reachable (push access); local Lean: elan installer + `lake exe cache get` ok; CI: not read yet.

## Bottleneck
The newest frozen claims (1028Z: `MonotoneWindow`, `MonotoneExists`) are about solutions with q = f'' > 0 on [0, ∞). A reader cannot check that hypothesis on a solution they do not have; the literature's class is 0 < f' < 1 (Coppel 1960). Run 1028Z's referee (`runs/2026-11-08T1028Z/referee_mw.md` §1) proposed "given f' → 1, q > 0 ⟺ f' < 1". Yes (a proof in Lean) → the theorems speak about the class physicists use, and "same wall shear" becomes "the unique solution". No → the hypothesis stays a condition on f''.

## Audit finding on the referee's equivalence (1028Z, §1)
The referee's argument for "f' < 1 ⇒ q > 0" says "once q < 0, p decreases, p < 1 stays, so q' < 0 at every later zero". That step needs p² < 1, i.e. also p > −1: at a zero of q, q' = −1 + p², which is ≥ 0 when p ≤ −1. A solution whose f' dips below −1 is not excluded by the argument. What does hold, and is now compiled (below): **−1 < f' < 1 ⇒ q > 0**, and (with f'(0) = 0) **−1 ≤ f' ≤ 1 ⇒ −1 < f' < 1**. Whether f' < 1 alone suffices is open; no statement should use it.

## Scratch Lean (compiled with `lake env lean`, Mathlib only)
- `lean/BoundedPos.lean`: `pos_of_abs_lt_one` — for f' = p, p' = q, q' = −k f q − 1 + p² (any real k), p → 1 and −1 < p < 1 on [0, ∞) give q > 0 on [0, ∞). Fencing theorem with barrier 0 (`image_le_of_deriv_right_lt_deriv_boundary'`), then p non-increasing after a non-positive q contradicts p → 1.
- `lean/BoundedUnique.lean`: `eq_of_start` (two solutions with the same (f, p, q)(0) agree on [0, ∞): forward uniqueness, Lipschitz constant on the compact union of the two trajectories), `abs_lt_of_abs_le` (f'(0) = 0 and −1 ≤ f' ≤ 1 ⇒ −1 < f' < 1: a touch of ±1 at η₁ > 0 is an interior extremum, so f''(η₁) = 0, and backward uniqueness against the straight line f' ≡ ±1 forces f'(0) = ±1).
