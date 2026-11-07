# Run 2026-11-07T0628Z (scheduled)

**THE RESULT:** parts 2 and 5 (new certified mathematics): the Townes bracket of run 0228Z became a statement about the ground state itself — a positive, strictly decreasing solution of the 2-D radial equation θ'' + θ'/r − θ + θ³ = 0 decaying to 0 exists with θ(0) strictly between 2.2062008646 and 2.2062008647 (`Work.Townes.Exists.townes_exists`, proved in Work + AUDITED; standard axioms). Part 3 (the judge): CI coalescing moved from whole runs to the heavy jobs, so a nanoda shard of hours no longer holds back the Work judge of later commits. Parts 1 and 4: no step this run.

**What can a scientist now trust without checking it themselves, that they could not before?** That the 2-D cubic NLS ground state (Townes soliton) has a central value in a window of width 10⁻¹⁰ — as a theorem about a genuine positive decaying solution, not about two shooting trajectories — with a blind restatement (C² on the whole line) closed from it in Lean. Caveat stated in the module doc: that it is *the* ground state needs Kwong's uniqueness theorem (1989), not formalised.

**Measure:** Work headlines with a closed blind restatement +1 (`townes_exists`); freeze → Work proof 62 min (four forks, 7–8 min each); judge latency for a Work proof on main: pending behind a nanoda shard of > 2 h → started within a minute (run 42352165146).

**Weakest unchecked step:** uniqueness of the ground state (Kwong 1989) is not formalised, so the theorem names *a* ground state in the window; and the Townes trio is in Work, not Checked (no nanoda, no literal readings yet). **CI:** work job of d6d6079 (run 42352165146) **green** at 07:57Z — it built `TownesExists` on the real shooting chain, `TownesExistsBlindClosed`, and the closed-audit check (no `sorry` warning outside the two blind statement files).

## Start
- 06:28Z: pre-cloned checkout detached with a stale diverged local main; `git checkout -B main origin/main` (109ac0d). add_repo not exposed. No LOCK on main (run 0428Z released it at 06:18Z); this run took it (6a19a3b).
- Environment: elan + Mathlib cache (local Lean available). CI: run 42343274596 (77803a1) checked job **green** (trust steps over everything since a4c4b03), work green, nanoda shards 1/2 green (22/25 min), shards 0/3 running.

## Bottleneck
STATE next step 3 (part rotation: 2/5 or 1): the Townes result stopped at two shooting events; "the ground state's θ(0) lies in the bracket" was not a theorem. Yes → a certified ground-state value; no → the bracket says nothing about any decaying solution.

## Work
1. **Freeze** 78498eb (06:33Z): `townes_exists` with `sorry`, only Mathlib definitions.
2. **Blind restatement** (Sonnet, question only): `runs/2026-11-07T0628Z/blind/TownesExistsBlind.lean` (ContDiff ℝ 2 on ℝ, deriv θ 0 = 0, ODE for r > 0). **Referee** STANDS (`referee_exists.md`, script `scripts/referee_shoot.py`): mpmath Q(0) = 2.2062008646507460747; every witness satisfies the shooting hypotheses, so `Ioo` is right; no rigorous 2-D enclosure in print to its search (3-D: Cohen–Li–Schlag 2024). Committed 1b53560.
3. **Proof** 14f7a24 (07:37Z): forks A (`TExLeft`, 464 lines), B (`TExFlow`, 376), C (`TExLimit`, 326), D (`TownesExistsBlindClosed`, 221, blind copy verbatim in `Work/Townes/TownesExistsBlind.lean`); assembly `TExAssemble` (≈ 420 lines, by hand, two compile iterations). `#print axioms core`, `of_program`: propext, Classical.choice, Quot.sound.
4. **CI change 3** d6d6079 (LEDGER): job-level concurrency groups. Cancelled by hand: 470 (14f7a24 on main, pending under the old group, superseded by 472 on a descendant), 471 (`wip/townes-exists`, a duplicate pushed to get the Work judge before the change).
5. Local build trap: `lake build Work.Townes.TownesShooting` (the certificate chain) took 17 min for TCertsA1 and OOM-killed TCertsB1 in parallel, and starved a `lake env lean` for 5 min; killed. Check by stubs instead (PROMPT note).

6. **Non-vacuity of the shooting pair** (`Work/Townes/TownesSolutions.lean`, `ivp_exists`): for every c ∈ [2.2, 2.21] and S > 1/5 the hypotheses of `townes_under`/`townes_over` are satisfiable with θ(0) = c (local `lake env lean` green, standard axioms) — the NV witness their promotion will need.

## Not done
Promotion of the Townes trio (needs the certificate rewrite first, STATE next step 2); uniqueness.
