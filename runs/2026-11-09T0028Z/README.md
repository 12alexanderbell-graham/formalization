# Run 2026-11-09T0028Z (scheduled)

**THE RESULT:** parts 2 and 5 — the Hiemenz, Homann and Falkner–Skan β = 1/2, 1/5 wall-shear theorems now hold for **every** solution of the boundary-value problem: the hypothesis −1 ≤ f' ≤ 1 is removed by a machine-checked proof that for 0 < β ≤ 1 every solution has f'' > 0 (frozen, proved, blind-closed, refereed, promoted to Checked in one run; PROVED once a main CI run is green on every job).

**What can a scientist now trust without checking it themselves, that they could not before?** That the textbook boundary-value problems of stagnation-point and wedge flow (f(0) = f'(0) = 0, f' → 1) have exactly one solution each, with no side condition on f' (before: only within −1 ≤ f' ≤ 1), and that its wall shear lies in the ten-decimal window (Hiemenz 1.2325876568–9, Homann 1.3119376938–9, β = 1/2 0.927680039–40, β = 1/5 0.6867081809–11). Uniqueness without restriction for 0 ≤ β ≤ 1 is classical (Coppel 1960, Craven–Peletier 1972, per Fazio arXiv:2011.07725 read verbatim; primaries unread); new is the machine-checked proof together with the certified windows.

**Measure:** headlines 210 → 218 (CLAIMS.md), NV 137 → 145; the eight new headlines have one hypothesis fewer than the bounded ones they extend (no class assumption left besides the boundary conditions). Blind restatement (Sonnet, words only): 9/9 closed in Lean.

**Weakest unchecked step:** the windows' numerical side is unchanged (certified cells); the weakest step for these headlines is still the fidelity of the equation transcription, read blind twice (existing `Checked.Trust.SecondReading` readings). `fs_monotone_of_limit` (general β) is a Checked helper but not a headline: its β-form literals have no blind reading yet.

## Start
- 00:28Z. add_repo not exposed; pre-cloned checkout detached with a stale diverged local main; `git checkout -B main origin/main` (reset of the local branch only) = fb863a8. No LOCK; taken 6e00d7a, heartbeats 4eee63a, 5ae2ab6.
- Environment: repo reachable (push); local Lean: elan + toolchain v4.35.0 + Mathlib cache ≈ 3 min; full `lake build Checked` 00:35–01:48Z (73 min, 2 cores); StatementDeps with relock ≈ 6 min, Claims ≈ 3 min.
- CI read: ae8e18b (42535496360) **green on every job incl. the checked job** — first green checked job after the promotion 26d2718, so the β = 1/5 trio (`fs_fifth_bounded_window`, `_equal`, `fs_fifth_exists_bounded`) is **PROVED**. e16541a, fb863a8: cancelled by coalescing (their content is judged by later runs).

## Bottleneck
STATE exact next step 3 (parts 2/5, rotation after 2228Z's part 3): widen the class −1 ≤ f' ≤ 1. The upper half was automatic (scratch of 2228Z); the lower half was open (`runs/2026-11-08T1228Z/referee_bounded.md` §3: a counterexample must dip below −1 at a last zero of q and creep back to 1). A yes turns every bounded-class theorem into a theorem about the boundary-value problem itself; a no leaves the program's fluid-mechanics results conditional on a side assumption that the literature does not make.

## Work
1. Research subagent (Opus, background; `coppel/REPORT.md`): primary sources unreachable; it found a self-contained elementary proof for every K = 1/β ≥ 1 — exact identities (Λ r)' = (2 − K) Λ p q, Φ' = −Λ q (q + 2(K − 1) f p) for Φ = Λ(f q' − p q), Ω' = 2(K − 2) M f² q for Ω = M(p² − 1 − 2 f q); last zero of q; descent (f < 0 at the last zero, 1 ≤ K ≤ 2), ascent (then p overshoots 1), Ω monotone (K ≥ 2). K ≥ 1 enters only in the sign of Φ'; numerically the ascent lemma fails for K = 0.5, 0.9 and a non-monotone solution exists at K = 0.5. Every identity and step re-derived by hand in the main session before Lean.
2. Lean (main session, 01:10–01:15Z, `lean/Unrestricted.lean` → `Work/FalknerSkan/UnrestrictedCore.lean`): calculus tools on [0, ∞) (strict/weak monotonicity from interior derivatives, one-sided slopes, the weight exp(a ∫₀ f) by FTC), lemma (a) p ≤ 1, L4 (q eventually positive), L5 (last zero by sSup), L1 identities, descent, ascent, omega, main theorem; touch (L3) by backward uniqueness (`BoundedTools.uniq_left`). Compiled first time apart from three ring/linarith repairs.
3. Freeze d71bf54 (nine statements, all `sorry`); blind restater (Sonnet) and referee in ONE message; both committed 84609a7. Referee STANDS-WITH-CORRECTIONS (prose only; corrections appended to REPORT.md).
4. Proofs 5ae2ab6 (statements byte-identical to d71bf54; `git diff d71bf54` removes only the `sorry` lines and one `open`), blind restatement closed (`Work/FalknerSkan/UBlindClosed.lean`), axioms standard.
5. Promotion 3684e58 (`scripts/promote_unres.py`): `Checked/FalknerSkan/LimitCore.lean`, `Limit.lean`. **check_claim_vocab V13 rejected the Work name "Unrestricted" as a generality word in a headline name** (correctly: the name would assert more than the claim's words) → renamed after the remaining class condition, the limit. check_literals rejected the general-β theorem (no blind reading of `β ≤ 1` and the β-form right-hand side) → kept as a helper, not registered.

## Audit
- Statements: referee §1 (each = the Checked `*_bounded_*` theorem with only `hb` deleted; not vacuous; f(0) = 0 needed).
- Blind restatement: `runs/2026-11-09T0028Z/blind/UnrestrictedBlind.lean` (its own `f, f1, f2, f3` with the ODE as an equation) closed for all nine (`Work/FalknerSkan/UBlindClosed.lean`).
- Referee: `runs/2026-11-09T0028Z/referee_unrestricted.md` (independent derivation, sympy identities, own numerics K ∈ {1, 1.5, 2, 5}; prior art).
- Not done: `scripts/trust/audits.txt` not regenerated (needs a full Work build; growth is free, next run).

## CI
- Pushed: 6e00d7a, 4eee63a, d71bf54, 84609a7, 5ae2ab6, 3684e58, records. Read next run by run ID (the promotion 3684e58 and the records commit).

## Next
See STATE "Exact next step".
