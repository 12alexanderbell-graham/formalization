# Run 2026-11-04T0628Z (scheduled)

Environment: add_repo not exposed; repo pre-cloned (detached at origin/main 9bbb9cb; a stale local `main` reset to origin/main). No LOCK (run 0428Z closed). **Local Lean worked** (elan installer accepted, Mathlib cache). CI of the previous run green (41777672804, 41781095697); this run's ids in STATE.

**THE RESULT:** part 1 moves ("every link machine-checked": the *simulations* link, which had nothing). The program has its first **rigorous simulator**: a validated ODE integrator whose output is a Lean theorem about every true solution, with no floating point trusted. First application: the Duffing oscillator x'' + x + x³ = 0, x(0) = 1, x'(0) = 0 (no elementary closed form).

**WHAT CAN A SCIENTIST NOW TRUST WITHOUT CHECKING IT THEMSELVES?** That every solution of that initial value problem is positive on [0, 1.192005] and negative at 1.192006, so its earliest zero lies in (1.192005, 1.192006), and that a solution exists. Proved with standard axioms; promoted to Checked in this run (`Checked/Sim/`), PROVED once the promotion CI is green (read next run). The frozen statements (3cf671f) are proved unchanged; the registered headlines are their one-sided form (LEDGER). Independent check: the closed form t₁ = K(m = 1/4)/√2 = 1.19200550727… (referee, four routes) lies inside the certified interval.

**WEAKEST UNCHECKED STEP NOW:** the blind spec's determining law is the textbook IVP itself, so the pin of `IsDuffingSolution` is close to a restatement; its independence rests on blind authorship and the anchors proved from it (energy, linear solutions, uniqueness, near misses), all by the same model family. Beyond this case: no simulation outside this one system yet.

**BOTTLENECK AND WHY:** part rotation named part 1 (and 5); inside part 1 the goal names "rigorous simulators" and the program had none — every simulation claim so far would have been floating point. Yes (a certified enclosure of a nonlinear ODE through the existing judge) = simulations join proofs as checkable output, and the method generalises to any polynomial vector field; no = the judge cannot carry simulations and part 1 needs another route.

**WHAT WE DID:**
1. Froze `Work/Sim/Duffing.lean` (3cf671f): `IsDuffingIVP`, `duffing_first_zero`, `duffing_exists`.
2. In ONE message: blind restater (`Work/Sim/DuffingBlind.lean`), referee (`referee_duffing.md`: STANDS-WITH-CORRECTIONS; docstring corrections 1–5 applied; prior art Immler (Isabelle), Park–Thies (Coq); "first in Lean/Mathlib to our search", pending arXiv 2610.02335), blind spec writer (`Work/Fidelity/DuffingSpec.lean`, no sorry: spec ⇔ textbook reference, uniqueness by Grönwall, energy, linear/cos anchors, near misses refuted).
3. Simulator (generic): `Work/Sim/ODETools.lean` (rational Horner polynomials, derivative, |p| ≤ Σ|cₖ|hᵏ, Grönwall cell bound with exp x < 1/(1−x)); `Work/Sim/DuffingCell.lean` (Lipschitz 41/10 on the box, energy keeps every solution in the box, one validated cell step from Mathlib's `dist_le_of_approx_trajectories_ODE_of_mem`); generated certificates `Work/Sim/DuffingCerts.lean` (24 cells of length 1/20, degree-7 Taylor polynomials with coefficients rounded to 10⁻¹¹, exact defect polynomials; `scripts/gen_duffing.py`, `emit_duffing.py`, `emit_main.py`; compile 130 s). Final enclosure 7·10⁻⁸ against a sign margin 5.5·10⁻⁷.
4. Existence (`Work/Sim/DuffingExists.lean`): Picard–Lindelöf for the clamped Hamiltonian field, whose exact invariant ∫cl + ∫(cl + cl³) = 3/4 keeps the solution where the clamps are inactive.
5. Audit (`Work/Sim/DuffingAudit.lean`): blind main theorem, existence and the first-zero corollary closed in Lean (the blind version, one-sided derivatives, is *stronger*; the core theorem `first_zero_within` proves it, the frozen statement is its corollary); `IsDuffingIVP` meets the blind spec.

**RESULT:** frozen `duffing_first_zero`, `duffing_exists` proved (axioms propext, Classical.choice, Quot.sound); promoted (6. below) as registered headlines on the pinned one-sided definition.
6. Promotion (main, after the records): Checked copies with specific Mathlib imports, new PHYSICS definition `IsDuffingSolution` pinned by the blind spec (`Checked/Sim/DuffingPin.lean`), two registered headlines, NV witness, glossary term `Duffing`, relock (new entries only), local trust step 133/133 pinned, NV 83/83; CI read next run. Measure: certified simulation results 0 → 1; parts of the "every link" list with a working checker: definitions, statements, transcriptions, numbers → + simulations.

**WHAT COULD STILL BE WRONG:** the number is not new (closed form known); the value of the run is the method. Grönwall with a global Lipschitz constant amplifies errors like e^{4t}: long horizons or chaotic systems need a better norm or per-cell contraction (Lohner-type). Existence covers only these parameters.

**NEXT:** STATE "Exact next step".
