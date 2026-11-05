# Run 2026-11-05T0028Z (scheduled)

Environment: add_repo not exposed; repo pre-cloned (detached HEAD, stale local `main` reset to origin/main). No LOCK (run 2228Z closed). **Local Lean available** (elan installer accepted, Mathlib cache). CI of run 2228Z: final commits green (41935694964, 41938551731); two intermediate commits had failed only the goal guard (run directory before its README) and the packet check (fixed in the same run). This run: freeze 5a06f66 CI 41943224752 green; proof 83a8465 (41949517822) and blind closure dbb67ca (41951801788): read next run.

**THE RESULT:** part 5 (breadth) moves into mathematics: the first mathematics result — the constants of the Lane–Emden polytrope of index 3 proved for every solution, PROVED in Work (blind restatement closed, referee STANDS); Checked promotion waits on the existence proof.

**WHAT CAN A SCIENTIST NOW TRUST WITHOUT CHECKING IT THEMSELVES?** The first zero ξ₁ ∈ [6.896848615, 6.896848625] of the n = 3 Lane–Emden function, the Chandrasekhar-mass factor ω₃ = −ξ₁²θ'(ξ₁) ∈ [2.018235945, 2.018235955] and Eddington's central concentration ξ₁³/(3ω₃) ∈ [54.1824805, 54.1824815], as a Lean theorem about *every* solution regular at the centre, whose statement contains only Mathlib definitions (nothing for a reader to trust but the statement itself). Every value in print came from floating point; the screen and the referee found no rigorous enclosure. The printed values (Chandrasekhar 1939: 6.89685, 2.01824, 54.1825; Horedt 1986: 6.89684862) are confirmed.

**WEAKEST UNCHECKED STEP NOW:** existence. Until a solution is constructed in Lean the theorem could in principle be vacuous (the referee argues existence on paper: Volterra fixed point near 0, energy bound after); it is also not yet in `Checked` (no CI-enforced trust map, NV witness or generated claim).

**BOTTLENECK AND WHY:** part rotation (part 5 idle since 1828Z) and "mathematics: not started" in TARGETS part 5. Question chosen by a screen subagent for "answer not in print": the constants are cited constantly (the Chandrasekhar mass) and only ever computed in floating point. Yes = the pipeline covers mathematics, including an ODE singular point the simulator could not handle; no = it does not reach mathematics. Answer: yes, freeze to Work proof plus closed blind restatement in one run.

## What was done
- Screen (subagent): five candidates (Lane–Emden n = 3 recommended; Bonnor–Ebert / 3-D Gelfand, n = 3/2, 1-D Bratu, Shapiro constants).
- Freeze `Work/Math/LaneEmden.lean` (5a06f66) with the README stub (the goal guard needs `**THE RESULT:**` once `runs/<id>/` exists).
- In one message: blind restater (Sonnet), referee, fork A (singular-start lemma `Work/Math/LEStart.lean`), fork B (time-dependent tube cell `LECell.lean`, generated certificates `LECerts*.lean` from `scripts/gen_le.py` + `emit_le.py`, chaining, final proof). Then fork C closed the blind restatement (`LEBlindBridge.lean`), re-basing the certificates on [0, 69/10].
- Float reference `scripts/le_float.py`; referee's independent 40-digit computation by two methods agrees.

## Method notes
- Singular point: the generic tube cell cannot start at ξ = 0 (2/ξ). Instead u = ξ²(φ − P') has |u'| ≤ ξ²(Lη + R) given |θ − P| ≤ η, so |φ − P'| ≤ ξ/3 (Lη + R) and |θ − P| ≤ ξ²/6 (Lη + R) < η: a strict improvement, closed by continuous induction. With the degree-26 series and ξ₀ = 1/2 the start box is ≈ 10⁻¹⁷.
- Time-dependent field: Lipschitz constant per cell max(1, 2/t₀ + 3TH²) on the slab |θ| ≤ TH (TH per cell, not global: a global bound would amplify by e¹⁹). 90 cells, degree 10, final radius ≈ 5·10⁻¹¹.
- First zero without lower bounds on θ: θ' < 0 on (0, ξ_hi] gives strict decrease, so IVT between two grid points finishes; ω₃ from the polynomial (t₀ + σ)²p_φ on the last cell.
- Memory: a single 90-cell module is killed (exit 137); three serially importing modules of 30 cells, ≈ 4.7 GB and ≈ 3.5 min each.
