# Run 2026-11-05T0228Z (scheduled)

Environment: add_repo not exposed; repo pre-cloned (detached HEAD, stale local `main` reset to origin/main). No LOCK (run 0028Z closed). **Local Lean available** (elan installer accepted, Mathlib cache). CI of run 0028Z: proof 83a8465 41949517822, blind closure dbb67ca 41951801788 and records 46c121e 41951988973 all green. This run: see "CI" below.

**THE RESULT:** part 5 (mathematics) — the Lane–Emden n = 3 constants go from PROVED in Work to Checked: a solution regular at the singular centre is constructed in Lean (Banach fixed point of the Volterra map, then Picard–Lindelöf), so the headline is not vacuous, and the whole argument is promoted with specific imports, registered (NV witness, trust map, generated claim) and audited.

**WHAT CAN A SCIENTIST NOW TRUST WITHOUT CHECKING IT THEMSELVES?** That the Lane–Emden n = 3 constants ξ₁ ∈ [6.896848615, 6.896848625], ω₃ ∈ [2.018235945, 2.018235955] and ρ_c/ρ̄ ∈ [54.1824805, 54.1824815] are facts about an actual function: a solution of θ'' + (2/ξ)θ' + θ³ = 0, θ(0) = 1, regular at ξ = 0, is constructed in Lean (`Checked.Math.LEExists.exists_solution`), and the certified bounds hold for it and for every other solution (`Checked.Math.LaneEmden.laneEmden3_constants`), with the statement in `Checked` under the CI judge (kernel, leanchecker, nanoda, trust step, generated claim). Before this run the theorem could in principle have been vacuous.

**WEAKEST UNCHECKED STEP NOW:** uniqueness of the solution is not stated (the theorem covers every solution, so it is not needed for the numbers, but "the" Lane–Emden function is not yet a defined object); the literature claim being certified (that these constants are the ones used in Chandrasekhar's mass formula) is checked by the referee of run 0028Z, not by a machine.

**BOTTLENECK AND WHY:** STATE exact next step 1 (existence, then promotion). Yes = the first mathematics result is PROVED in the program's sense (Checked, CI green, audited, non-vacuous); no = it stays a Work result that could be vacuous.

## What was done
- Existence (`Work/Math/LEExists*.lean`, promoted to `Checked/Math/`):
  - singular piece on [0, 1/2] (`LEExistsLeft.lean`): Banach fixed point (`ContractingWith.fixedPoint`) of the scaled Volterra map (T f)(x) = 1 − x² ∫₀¹ u(1 − u) g(f(xu)) du, g the clamped cube, on bounded continuous functions on [0, 1/2] (Lipschitz 1/4). The scaling makes continuity at the singular point a parametric-integral fact; for x > 0 the substitution s = xu gives θ' = φ = −x⁻² ∫₀^x s² θ³ and φ' = −(2/x)φ − θ³ by FTC; θ'(0) = 0 from θ = 1 − x·(x·J(x)), J continuous; |θ − 1| ≤ 0.072 keeps the clamp inactive.
  - regular piece on [1/2, 7] (`LEExistsRight.lean`, fork): Picard–Lindelöf for the clamped time-dependent field; the clamped energy Ψ(φ) + U(θ) has derivative −2t⁻¹(cl φ)² ≤ 0, so both clamps stay inactive (the Duffing pattern with dissipation).
  - glued at 1/2 (`LEExists.lean`, `HasDerivWithinAt.union`).
- Promotion (`runs/2026-11-05T0228Z/scripts/promote_le.py`): eleven modules copied from `Work/Math` to `Checked/Math` (namespace rename, specific Mathlib imports, `#print axioms` lines dropped, module docs rewritten without numbers other than headline literals — check_prose rule 7). Statements and proofs otherwise byte-identical.
- Registration: headlines `Checked.Math.LaneEmden.laneEmden3_constants`, `Checked.Math.LEExists.exists_solution`; NV witness `Checked.Trust.NV.laneEmden3_constants`; audit `Work/Math/LaneEmdenAudit.lean` (blind restatement re-closed against the Checked `core`; non-vacuity with the conclusion).

- Packet generator repair: glossary closure only through comments-free code and only to definitions Lean could see (transitive Checked imports); five spurious glossary entries removed (LEDGER).
- Local verification before push: full `lake build Checked` (≈ 45 min on 2 cores), trust step with relock (153/153 headlines rest on no unpinned physics definition, NV 99/99, 157 record citations), `Claims.lean` (153 claims), check_prose (0 new problems), check_numbers, check_trusted_defs, check_claims, packet check, check_relock/audits/--base checks against ad3d6f5, goal guard; `Work.Math.LaneEmdenAudit` built, both audit theorems standard axioms.

## CI
- LOCK 52d0464: 41955430333 green. Existence ad3d6f5: 41957394569 green on every job (checked: build 38.5 min, nanoda 10.8 min, trust step 3.5 min).
- Promotion + records commit: see STATE "Environment" (read at the end of this run or next run).
