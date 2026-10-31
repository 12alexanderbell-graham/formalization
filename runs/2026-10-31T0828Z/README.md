# Run 2026-10-31T0828Z (scheduled)

Environment: repo pre-cloned (add_repo not exposed, not needed), fast-forwarded to f06b3c2; no LOCK. Local Lean via elan + cache + Checked build. Previous run's final CI 41181290751 green. PROMPT, operative core, STATE, last CHANGELOG read.

**THE RESULT:** part 4 (outside-expert validation) moves for the first time: everything the program can do is done; the round needs only Alexander to send the packet. Part 2 (new science, B1) moves: the first certified statement about where a cubic that agrees with exact ΛCDM must lie, including the side, which the referee's analysis puts opposite to the RL19 offset (C27).

**WHAT CAN A SCIENTIST NOW TRUST WITHOUT CHECKING IT THEMSELVES?** (1) Every one of the 125 certified headlines now carries a plain-words claim, and CI refuses a headline without one: before this run 27 had none, so a scientist reading them had to read Lean. (2) PROVED + AUDITED (Checked): in every flat ΛCDM model with Ω ∈ [0.2, 0.4], any cubic log-polynomial whose distance modulus agrees with the exact one within 0.05 mag at z = 3 and z = 7 (up to a common offset, any normalisation) has (a₂, a₃) more than 1.25 from the ΛCDM-implied point and satisfies a₂ − a₂^ΛCDM < 7 log₁₀2 (a₃ − a₃^ΛCDM) (`Checked.Cosmography.B1Sep.cubic_separation`, `cubic_direction`).

**WEAKEST UNCHECKED STEP NOW:** for part 4, that the packet's plain-words claims are the program's own prose (now required, not yet independently read by humans). For B1, that the two-point criterion stands in for a least-squares fit: the referee showed fits over z ≤ 5 do not meet it, so C27's claim about the RL19 fit rests on numerics and on one reading of a contour centre.

**BOTTLENECK AND WHY:** part rotation: part 4 had never moved. Yes = the validation round is ready and pre-registered so its outcome cannot be steered; no = the program cannot prepare it alone. It was yes; the pilot also found a real gap (unchecked prose) that a human round would have spent itself on. Second block: B1 separation, STATE's next decisive step for part 2.

**WHAT WE DID:**
1. `validation/PROTOCOL.md` (sample, planted controls, reviewers, scoring with burden of proof on the system, validity threshold, honest 7.2% bound) and `validation/make_packet.py` (items generated from the Lean sources and TRUST_MAP; draw seeded by the protocol hash; sealed key).
2. Pilot by two Sonnet reviewers (`pilot/`): planted 8/8 caught; genuine 0 material, 6 minor. Fixed: 27 headline docstrings + 8 claim-definition docstrings (`scripts/set_docs.py`), `F10_exceptions` overstatement, witness naming in `StatementDeps.lean`; new blocking CI job `validation-packet`.
3. B1: froze `cubic_separation` (8be0a7b); blind restater + referee in parallel; proved it (Riemann-sum enclosures from run 0428Z, seven Ω-subintervals, Cauchy–Schwarz); froze and proved `cubic_direction` (1229815) after the referee's remark; closed both blind restatements in Lean (`Work/Cosmography/B1SepAudit.lean`); built the NV witness (new J₇ secant certificate, `scripts/emit_j7up.py`) and promoted both to Checked.

**RESULT:** Part 4: prepared (no status change: experts not yet contacted). B1: `Checked.Cosmography.B1Sep.cubic_separation`, `cubic_direction` PROVED + AUDITED (both blind restatements closed in Lean; NV witness `B1SepWitness.hyps_satisfiable`; audit `audit_b1sep.md`; registered, relocked, new entries only). CI ids in STATE.

**WHAT COULD STILL BE WRONG:** the planted controls may be too easy (8/8 by a model); the RL19 contour centre is one reading of a figure; certified bound 1.25 vs true 1.98 (loose, not wrong).

**NEXT:** STATE "Exact next step".
