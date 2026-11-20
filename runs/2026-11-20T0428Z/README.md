# Run 2026-11-20T0428Z

**THE RESULT:** parts 2 and 5 by rotation (STATE 2g → parts 2/5 as in section Next of `runs/2026-11-19T2228Z/README.md`). The Lean theorem of this run (its name is in the run record below) bounds, for every solution of the Lane–Emden equation of index nine halves with central value one on the range to thirty-two, the radius where the solution meets zero, the mass factor and the central-to-mean density ratio, each in a closed interval; a solution with every hypothesis is in Lean.

**What can a scientist now trust without checking it themselves, that they could not before?** A fourth row of the table of polytropes with a fractional index (nine halves), as one kernel theorem from the equation, for every solution; and the validated simulator now carries an enclosure over a range three times longer than before, because each cell may weigh the derivative by its own factor.

**Weakest unchecked step:** the judge's slowest jobs (leanchecker shards 1–3 and nanoda shard 1, each over an hour) bound every promotion, and this run adds five kernel-decided data modules to shard 0 (section Next).

## Start
- 04:28Z. Local main was a stale divergent clone (its tip on `origin/wip/leanchecker-shards`); `git checkout -B main origin/main` at fc55e07. No LOCK → taken (b4cf65a).
- CI at start: 44667501738 (fc55e07, records of run 0228Z) running; read at 04:45Z: green on every job (nothing to promote).
- Local Lean: elan + Mathlib cache ≈ 3 min; `checked-build` of 44655372746 (0792b21) restored with FORCE=1 DELETE_ZIP=1 (`~/.cache/mathlib` deleted first; 2.8 GB free after).

## Bottleneck (and what a yes/no changes)
- Parts 2/5: the next row of the polytrope table, index nine halves, whose first zero lies near ξ = 31.8 (three times the range of index seven halves). Does the fractional-index route reach it? Yes → the row is certified this run; no → record where the enclosure breaks.

## What we did
- **Freeze** 7251607 (before any proof): `Work.Math.LaneEmden92.laneEmden92_constants` on [0, 32], real power `θ ξ ^ ((9 : ℝ) / 2)`; first zero in [31.836463, 31.836464], mass factor in [1.7377988, 1.7377989], central concentration in [6189.4730, 6189.4733]. References `scripts/ref92.py` (mpmath, 40 digits: ξ₁ = 31.836463244694, ω = 1.737798867666, ratio 6189.473124954) and `scripts/ref92b.py` (scipy DOP853, agrees to 10⁻¹³).
- **Where the old route broke:** the index-seven-halves generator with the power changed (`scripts/gen_le92.py`, first version) failed at ξ = 31: the cell lemma bounds the field's Lipschitz constant in the max norm of (θ, φ), and θ' = φ forces K ≥ 1 there, so the Grönwall radius grows like e^ξ (3 · 10⁻⁴ at the zero even at thirty digits; a sign of θ at the bracket ends needs about 10⁻¹⁰).
- **New simulator step** (`Work/Math/LE92Cell.lean`, the only new mathematics): `cell` in the weighted norm max(|Δθ|, w |Δφ|) for any weight w > 0, by the generic tube lemma applied to (θ, w φ) with the field (p₂/w, −(2/ξ) p₂ − w g92 p₁); the Lipschitz conditions become 1 ≤ w K and 2/t₀ + w · 9/2 · S⁷ ≤ K, so K falls to about 2/ξ once w is large. `non_sub_le`, `g92_close` (ninth powers), `rpow92_eq`. `LE92CellQ`: the weight is a field of each cell; `linkOK` rescales the radius by the ratio of the weights of two cells; `negOK` and the last cell read φ in the cell's weighted norm. `LE92Glue` (`start92`, `last92`) by string replacement plus the weighted last cell. All compiled first time.
- **Generator** (`scripts/gen_le92.py`, `emit_le92.py`): weights 1, 4, 10, 20 from ξ = 0, 4, 8, 16 (`LE_WST`), steps 1/40, 1/20, 1/10, 1/2 (from 0.5, 1, 3, 6), crude cells from 0.2 before the zero: 146 cells, end radius 4 · 10⁻¹¹, bracket [31.8364631, 31.8364634], mass factor on the last cell in [1.737798865, 1.737798870], at the default precision. Five data parts of five-cell segments, 73–114 s and under 4 GB each; chain range [0, 796/25].
- **Existence** (Opus subagent, `scripts/mk_exists92.py`): left piece clamp 27/25 (S = 26/25) and the contraction's Lipschitz constant raised from 9/2 to 6 (factor unchanged); right piece on [1/2, 32] with clamp 81 (S = 9); energy at 1/2 ≈ 1.58 < 2.
- **Proof** 5048d50: statement and docstring byte-identical to the freeze; axioms propext, Classical.choice, Quot.sound; `exists_solution` checked by applying the headline to it.
- **Fidelity**: referee (Sonnet, `referee/REPORT.md`) STANDS: two Taylor integrators to 27 digits; margins 2.4 · 10⁻⁷ / 7.6 · 10⁻⁷ (ξ₁), 6.8 · 10⁻⁸ / 3.2 · 10⁻⁸ (ω), 1.2 · 10⁻⁴ / 1.8 · 10⁻⁴ (ratio); θ'(0) = 0 implied; the junk value of the real power below zero harmless. Blind restatement (Sonnet, `blind/`): θ continuous on [0, 32], right derivative 0 at the centre, differentiability and the equation on the open interval in `deriv` form, the first zero as `IsLeast`; closed in Lean from the helper `core` (`Work/Math/LaneEmden92BlindClosed.lean`, Opus subagent, `scripts/mk_blind_closed92.py`). Blind literal reading (Sonnet; brief d13b926 alone, reading 34e503d alone): A, B, E = 2, 9, 2; Z, C, D = 0, 1, 32; P, K = 2, 3; every window equal to the statement's (its own 40-digit computation from two series starts, scipy to 13 digits). Necessity: hypotheses 1, 3, 4 NEEDED (`Checked/Trust/Necessity.lean`), 2 REDUNDANT (`NecessityB.lean`), the index-seven-halves witnesses with the exponent and range changed.
- **Promotion** (`scripts/promote_le92.py`): thirteen modules to `Checked/Math/`, headline docstring in the promoted index-seven-halves wording (Work file synced), `Checked/Trust/SecondReadingLE92.lean`, witness in `Checked/Trust/Witnesses.lean`, registries `headlines.txt`, `literal_readings.txt`; the five data modules on judge shard 0 (`scripts/nanoda/shard_assignment.txt`), the lightest shard of both kernel judges (36 and 30 min on 44655372746).

## Measure
- Parts 2/5: polytrope rows certified 6 → 7 (indices two, three, four, three halves, five halves, seven halves, nine halves). Longest validated chain of the Lane–Emden family: ξ ≈ 9.5 → 31.8 (end radius 4 · 10⁻¹¹ with weights; ≥ 3 · 10⁻⁴ without).
- Experiment of run 2228Z (one cell file `LEKCell` for every half-integer power, so that index nine halves needs no new lemma file): not met — a new lemma file was written, because the long range needed the weighted norm, which a general-power file would not have given; the data part of the experiment (≤ 5 cells per segment from the start, no out-of-memory retry) met.

## CI read
- 44667501738 (fc55e07, records of run 0228Z) concluded green on every job.

## End
- Local before the final push: see the final commit message.

## Next
- CI read first: the run of this run's final push (promotion of `laneEmden92_constants`: thirteen new Checked modules, `SecondReadingLE92`, Witnesses, Necessity, NecessityB; the five data modules on shard 0). Green on every job → PROVED: the judged template in its STATE.md heading (`check_stale_status.py`) and one L.2 line to Alexander. Red → `python3 scripts/trust/records_check.py <base>` or `local_frozen_step.py --trust <base>`; a kernel shard over its time limit → move data modules by the new times.
- The judge (from run 0228Z's section Next, not done this run): refresh `scripts/nanoda/shard_times.txt` from the newest four leanchecker logs and reassign; nanoda's own per-module times for shard 1.
- Then by rotation (parts 2/5 at 0428Z, part 3 at 0228Z, part 1 at 0028Z): part 1 as in section Next of `runs/2026-11-20T0028Z/README.md`; part 3 as in section Next of `runs/2026-11-20T0228Z/README.md`. Parts 2/5 later: the weighted cell makes long ranges cheap — λ₃ of the Gelfand branch (fourth turning point near s ≈ 4532, blocked since run 2026-11-18T1028Z by the growth of unweighted cells beyond 429) with weights; index eleven halves and the indices below one; the general-power cell file (`LEKCell` with the weight) once a third weighted index needs it.
