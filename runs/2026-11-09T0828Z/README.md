# Run 2026-11-09T0828Z (scheduled)

**THE RESULT:** parts 2 and 5 — Falkner–Skan with **adverse pressure gradient (β < 0)**, new ground for the program: four theorems **PROVED in Work + AUDITED** (blind restatement 4/4 closed, referee, prior-art screen): uniqueness for every β < 0 in the class f'' > 0 + faster-than-every-exponential approach (and that solution has the largest wall shear among f'' > 0 solutions); at β = −1/10 existence of that solution by certified shooting, and **two different solutions with 0 ≤ f' ≤ 1, f'' > 0, f' → 1** (wall shears 1/(2√10) and 3/(4√10)): the textbook uniqueness class fails for β < 0. Checked promotion next.

**What can a scientist now trust without checking it themselves, that they could not before?** That for decelerating wedge flows (β < 0) the Falkner–Skan boundary-value problem has at most one solution with f'' > 0 that approaches the free stream faster than every exponential — for every β < 0 — and that at β = −1/10 this solution exists, while the class 0 ≤ f' ≤ 1 used for β > 0 does not determine the solution there (two machine-checked counterexamples).

**Measure:** Work theorems +4 (+ 2 blind closures); referee: 0 errors in 11 lemmas, 6 gaps (closed in Lean); certified chains 3 (58 cells, margins ≥ 0.02); axioms standard.

**Weakest unchecked step:** the transcription of the β = −1/10 equation (`(-1 / 10)` in the β-form) has no blind literal reading yet (needed for Checked), and whether the uniqueness theorem is classical rests on secondary sources (Coppel 1960, Hartman not read).

## Start
- 08:27Z. add_repo not exposed; pre-cloned checkout detached, shallow, stale local main; `git checkout -B main origin/main` (local branch only) = f8fcf46.
- LOCK held by run 2026-11-09T0628Z (started 06:28Z, heartbeat 07:42Z): alive → auditor role (48.4): referee + screen of the β < 0 research note, scratch Lean in `lean/`. Run 0628Z released the LOCK at 933f48e (≈ 08:30Z); this run took it in 3396ae3 (08:44Z).
- Environment: repo reachable (push); local Lean: elan + toolchain v4.35.0 + Mathlib cache ≈ 4 min; no full Checked build needed (Work modules only).
- CI: f8fcf46 (42580931850) green; later main runs coalesced/cancelled or queued (STATE next step 1).

## Bottleneck
STATE exact next step 2 (parts 2/5): β < 0 was uncovered, and the research note claimed the program's uniqueness class is false there. A yes (proved) gives the first certified results for adverse pressure gradients and a machine-checked reason why the decay condition is needed; a no would have shown the note's uniqueness proof wrong.

## Work
1. Auditor role, in parallel (one message): referee (Opus) on the note's §2–§3 → `referee/REPORT.md` (no lemma wrong; gaps: Lemma T continuity, Lemma L division by zero at B = 0, Lemma R for M < μ, ψ′ = 1/z export, unclamping never argued, p → 1 redundant; false remarks §1.4, §3.6 margins); prior-art screen → `screen/REPORT.md`; two forks wrote scratch Lean of Lemmas 1, C, T, U′ (`lean/A/`) and I, L, R (`lean/B/`), all green.
2. Freeze 881ec81 (`Work/FalknerSkan/NegDecay.lean`: `fs_neg_decay_max_shear`, `fs_neg_decay_equal`); blind restatement (Sonnet, `blind/`), proofs (fork P: `NegCrocco`, `NegNoCross`, `NegUPrime`, `NegCore`), blind closure `NDBlindClosed.lean` — a6dccad.
3. Freeze c95ce4c (`Work/FalknerSkan/NegTenth.lean`: `fs_neg_tenth_exists_decay`, `fs_neg_tenth_not_unique`); `Work/FSNeg/NBase.lean` (interface: clamped adverse-sign K = 10 field, events Over/Slow) written by the main session; forks C (certified chains: `NCellWC`, `NSlowHalf`, `NSlow34`, `NOver11`; generator `scripts/gen_neg_wc.py`, `emit_neg_wc.py`, `scripts/NEG_CELLS.md`) and D (`NFlow`, `NLemma1`, `NSlowInv`, `NLimit`, `NRiccati`, `NUnclamp`, `NAssemble` with core theorems taking the chains as hypotheses) in one message — both green within 25 min; 21de9a4. Blind restatement (`blind2/`) closed in `NTBlindClosed.lean` — 0e999ee.

## Kind (part 2)
Uniqueness in the decay class: likely classical (Hartree/Stewartson selection; Coppel/Hartman to check). Non-uniqueness at β = −1/10 with explicit wall shears and certified existence: new in rigorous form as far as the screen found (no computer-assisted or formal Falkner–Skan proof found).

## Lessons (PROMPT working note)
- A live LOCK did not cost the run: auditor-role referee + screen + scratch Lean forks were exactly the inputs the freeze needed when the LOCK was released 15 min later.
- Interface-first forks: writing the event definitions (`NBase.lean`) and the exact chain-theorem shapes in the brief let the certificate fork and the assembly fork work in parallel; the assembly took the chains as hypotheses (`ChainTo`) and was closed by one line each.
