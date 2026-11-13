# Run 2026-11-13T2228Z (scheduled)

**THE RESULT:** parts 2/5 by rotation (part 1 moved at 2028Z, part 3 at 1828Z, parts 2/5 last at 1640Z) — the Bonnor–Ebert critical mass is now a machine-checked *global* statement: for every regular solution of the isothermal equation, the first maximum of the pressure-confined mass (radius in [6.4507514, 6.4507515], mass in [1.1822265, 1.1822266]) is strictly larger than the mass at every other radius. Frozen before proof, proved, blind restatement closed, referee STANDS, promoted to Checked (`Checked.Math.BonnorEbertMax.bonnor_ebert_max`) with NV witness, literal readings and all five hypotheses classified.

**What can a scientist now trust without checking it themselves, that they could not before?** That no pressure-confined isothermal gas sphere, of any radius, holds more mass than the critical Bonnor–Ebert sphere (at fixed temperature and external pressure) — a fact used throughout star-formation theory and until now supported by numerics and the spiral picture, not by a proof with certified constants. Measure: Checked astrophysics headlines 1 → 2, fully classified (CI pending).

**Weakest unchecked step:** CI has not judged this run's push (nor 3cd85d2's, still running at the end); the "not in print" part rests on a referee search that was not exhaustive.

## Start
- 22:28Z. add_repo not exposed; pre-cloned checkout detached at 3cd85d2 with a stale local main; `git checkout -B main origin/main` = 3cd85d2. No LOCK → taken (feeb8ff).
- CI at start: 43511962008 (3cd85d2) goal guard, changes, packet green; nanoda 0–3, work and checked in progress (checked job started 21:59Z).
- Local Lean: elan + Mathlib cache ≈ 2 min; `checked-build` of 43462297471 (c5c2a35) restored in 36 s; incremental `lake build Checked` ≈ 9 min.

## Bottleneck (and what a yes/no changes)
- STATE 0e listed "the maximum over all radii (a tail beyond 7)" for the Bonnor–Ebert sphere. Yes: the physically used statement (the critical mass is the maximum) becomes a Checked theorem. No: record why a finite chain cannot reach [7, ∞).

## What we did
1. **Idea (float study first, `scratchpad`):** in homology variables u = s e^w/(−φ), v = −sφ the equation is the Lotka–Volterra system du/dt = u(3 − u − v), dv/dt = v(u − 1) (t = log s), and Volterra's function V = (u − 1 − log u) + (v − 2 − 2 log(v/2)) has dV/dt = −(u − 1)². Since 4π m² = u v³, it suffices that u v³ stays below 4π m(ξ₁)² on {V ≤ V(7)}: numerically max 17.4456 against 17.5635. The convex-duality bound x − 1 − log x ≥ a log x + a − (1 + a) log(1 + a) (one use of log y ≤ y − 1) with a = 4/25 for u and 6/25 for v/2 turns this into one linear inequality between five logarithms of rationals; margin 1.05·10⁻³.
2. **Freeze** (8a0f587) of `Work.Math.BonnorEbertGlobal.bonnor_ebert_global` with the hypotheses and windows of the audited critical headline; briefs committed (bf38451); blind restater (Sonnet) and referee (Opus) launched in one message.
3. **Proof** (37021eb; ≈ 25 min): `Work/Math/BEEnd.lean` re-chains the 381 existing cells of `BEChain` and exposes e^{w(7)}, φ(7) to 10⁻¹¹ (`bend_val`); `Work/Math/BETail.lean` (`dual`, five `log_*` enclosures by the alternating series, `uv_bound`, `tail`: s²φ strictly decreasing ⇒ φ < 0 on [7, S]; V' = −(u − 1)²/s by `field_simp; ring`; `antitoneOn_of_deriv_nonpos`); the headline combines `tail` with the critical headline's monotonicity. Axioms standard.
4. **Audit:** blind restatement closed (`Work/Math/BonnorEbertGlobalBlindClosed.lean`: ψ C² on [0, ∞), equation in deriv form, rpow mass, global ∀ ξ ≥ 0 — the maximiser does not depend on S, by applying the headline twice); referee STANDS (`referee/REPORT.md`).
5. **Promotion:** `Checked/Math/{BEEnd,BETail,BonnorEbertMax}.lean`, headline `bonnor_ebert_max` registered, NV witness, literal readings (the critical headline's, minus the decrease range), `Checked/Trust/NecessityZ.lean` (1, 2, 4, 5 NEEDED, 3 REDUNDANT), relock, CLAIMS, packet. The docstring needed one rewording: check_claim_vocab V7 attaches "for every s" to the claim's *first* binder named s (a hypothesis), so a conclusion-level "every s" after "there is ξ₁" reads as a scope swap; written with no quantifier word ("m(s) < m(ξ₁) for s in [0, S] with s ≠ ξ₁"; "at every other radius" then failed check_prose: no binder carries the noun).

## Not done / next
- The density contrast at ξ₁ is not repeated in the global headline (it stays in `bonnor_ebert_critical`).
- STATE 0k.

## Local checks and push
- `lake build Checked` green on the restored build (incremental); `#print axioms` of the Work headline and of the blind closure: propext, Classical.choice, Quot.sound.
- `TRUST_RELOCK=1 lake env lean scripts/trust/StatementDeps.lean` exit 0 (281 → 280 lines as printed: 280 headlines; NV 169/169; necessity: needed 548 → 552, redundant 153 → 154, open 261 unchanged — the new headline enters fully classified); `Claims.lean` regenerated CLAIMS.md; `make_packet.py` regenerated the packet.
- `records_check.py c5c2a35`: 41 commands, 0 failed (after two docstring rewordings: V7 of check_claim_vocab, then check_prose's bound-noun rule).
- Final push removes the LOCK; it starts the main run that judges 3cd85d2's content too.
