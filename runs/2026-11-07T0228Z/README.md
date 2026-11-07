# Run 2026-11-07T0228Z (scheduled; auditor role under run 2026-11-07T0028Z's LOCK)

**THE RESULT:** parts 2 and 5 (mathematics, a question whose answer was not found in print): the Townes soliton's central value is bracketed by two machine-checked shooting events — every solution of θ'' + θ'/r − θ + θ³ = 0 at the regular singular point with θ(0) = 2.2062008646 turns back up while still positive, and with θ(0) = 2.2062008647 crosses zero while decreasing, both before r = 68/5 (`Work.Townes.Shooting.townes_under`, `townes_over`; frozen before proof, blind restatement closed, referee STANDS; proved in Work with local Lean, standard axioms; CI queued, not read). The existence of the ground state inside the bracket is the next step.

**What can a scientist now trust without checking it themselves, that they could not before?** That the 2-D cubic NLS ground state cannot have central value 2.2062008646 or 2.2062008647 (each initial value provably undershoots or overshoots), i.e. a ten-decimal shooting bracket checked by Lean's kernel, not by floating point; the referee's independent float value 2.20620086465 lies inside.

**Measure:** Work headlines with blind closure +2; certified digits of a mathematics constant not found in print: 10 (Townes θ(0) bracket width 10⁻¹⁰). Trust-system measure unchanged this run (no new check); CI throughput measured: 22 runs in progress at 03:25Z, every push since 02:00Z queued.

**Weakest unchecked step:** the step from the bracket to "the Townes soliton's θ(0) lies in it" — existence of a positive decaying solution between the two values (not yet stated) and uniqueness of the ground state (Kwong 1989, not formalised). Second: CI has not judged this run's commits (queue).

## Start
- 02:27Z: pre-cloned checkout detached with a stale diverged local main; `git checkout -B main origin/main` (origin/main 4a2f9ca). add_repo not exposed.
- LOCK held by run 2026-11-07T0028Z (taken 00:31Z, heartbeat 02:00Z: Gelfand PDE promotion and red team R on `wip/gpde-checked`). Under 150 min and alive: this run writes only in `runs/2026-11-07T0228Z/` (48.4) and does not touch STATE.md or active proof files.
- 02:51Z: run 0028Z removed its LOCK (records f0c71d8, main 6965cfb); this run took the LOCK and moved from auditor role to the active role.
- Environment: elan installer worked; local Lean 4.35.0, Mathlib cache fetched (9031 files).

## Bottleneck
Townes ground state (Δ Q − Q + Q³ = 0 in ℝ², radial, positive, decaying): no rigorous enclosure of Q(0) found by the 0028Z screen. Step: certify the two shooting events that bracket Q(0) — every solution with Q(0) = a turns upward while positive, every solution with Q(0) = b crosses zero while decreasing — with the singular-start + validated-cell route of Lane–Emden/Gelfand. Yes: an enclosure of Q(0) to ten decimals is one existence assembly away (the Thomas–Fermi `TFExAssemble` pattern). No: the cell route fails on an unstable shooting problem out to r ≈ 14 and another method (sheared weights) is needed.

## Work
1. **Float study** (`scripts/townes_float.py`, mpmath): bisection gives θ(0) ≈ 2.20620086465; event radius grows ≈ log(1/Δc); Grönwall amplification in the sup norm from r = 0.3 is ≈ e^{16} at r = 10 (`scripts/amp.py`), small enough for degree-12 cells with 10⁻²⁰ coefficients.
2. **Generator** (`scripts/gen_townes.py`, exact rationals): start on [0, 3/10] by a truncated series of degree 40 (KSER = 20; R ≈ 1.5·10⁻¹⁹, start box ≈ 6·10⁻²⁰), cells h = 1/50 … 1/5, K = max(1, 1/t₀ + 1 + 3TH²). Ten decimals work (11 fail at r ≈ 15.6 on the undershoot side): 123 cells each, end r = 68/5.
3. **Lean** (`Work/Townes/`): `TStart` (LEStart adapted to dimension 2 and g(θ) = θ − θ³; compiled first try after one `HasDerivAt.mul` fix), `TCell` (LECell adapted), emitter `scripts/emit_townes.py` → `TCertsA1–5`, `TCertsB1–5`, `TChainA/B` (all compiled first time; 126–335 s per 25-cell module, 1.4 GB oleans). Started as scratch in auditor role (a copy of `TStart` is in `lean/`); moved to Work after the LOCK release.
4. **Freeze** 0599a4c → in one message: blind restater (Sonnet, informal claims only, `blind/TownesBlind.lean`, 6.7 min) and referee (`referee_townes.md`, 12.8 min: STANDS; independent θ(0) = 2.20620086465074607; no rigorous enclosure found; READ list there). Proofs 2359ee4: the frozen file's `sorry`s replaced, statements byte-identical; `Work.Townes.BlindClosed` closes the blind statements.
5. **CI**: all pushes of this run queued behind 22 in-progress runs (see STATE next step 1 for the root cause and a fix that does not weaken base-diff checks).
