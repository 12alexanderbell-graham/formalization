# Run 2026-11-19T1628Z

**THE RESULT:** parts 2 and 5 by rotation (STATE 2a → parts 2/5 as in section Next of `runs/2026-11-19T1028Z/README.md`). The Lean theorem of this run (its name is in the run record below) bounds, for every solution of the Lane–Emden equation of index five halves with central value one on the range to six, the radius where the solution meets zero, the mass factor and the central-to-mean density ratio, each in a closed interval; a solution with every hypothesis is in Lean.

**What can a scientist now trust without checking it themselves, that they could not before?** A second row of the table of polytropes with a fractional index (five halves), as one kernel theorem from the equation, for every solution; the validated simulator carried to a new power by changing the power alone, freeze to promotion in about forty minutes.

**Weakest unchecked step:** the statement is from one model three times (a subagent and two subagent readers); the intervals are kernel theorems.

## Start
- The theorem: `Checked.Math.LaneEmden52.laneEmden52_constants`. Frozen 1ed85a2 before any proof, proved in Work 207a1f20 (statement unchanged), promoted by `runs/2026-11-19T1628Z/scripts/promote_le52.py`. Existence `Checked.Math.LE52Exists.exists_solution` (NV witness). Referee STANDS (`referee/REPORT.md`); blind restatement closed (`Work/Math/LaneEmden52BlindClosed.lean`); blind literal reading `Checked/Trust/SecondReadingLE52.lean` (brief e28fcee, reading e230b02 committed alone): every coefficient, range end and window agrees.
- 16:28Z. Local main was a stale divergent clone; `git checkout -B main origin/main` at ab284de. No LOCK → taken (8e13d71).
- CI at start: 44521044439 (68c077a, promotion of `laneEmden32_constants`): concluded success, every job green incl. the checked job and nanoda 4/4 (nanoda shard 1 ended 15:49Z) → `laneEmden32_constants` PROVED (STATE heading rewritten; Alexander told). 44535193737 (7c52721), 44535498718 (73af250) and 44548457011 (ab284de) running.
- Local Lean: elan + `lake exe cache get` ≈ 2 min; `checked-build` of 44548457011 (ab284de, 2.7 GB) restored. Subagents (Sonnet, one message): referee ≈ 1 min, blind restatement ≈ 2 min, blind literal reader ≈ 2 min.

## Bottleneck (and what a yes/no changes)
- Parts 2/5 by rotation; the LEDGER experiment of run 1028Z asked whether the fractional-index generator gives the next fractional index in one run with the power changed only. Yes → the simulator's fractional-index route is a template (any √θ^k), and the table of polytropes grows by data, not by new methods. No → the certificate shape for higher powers needs a new cell type, recorded with its cause.

## What we did
- **Power as a square root to the fifth** (`Checked/Math/LE52Cell.lean`): `g52 θ = √θ ^ 5` equals Mathlib's `θ ^ ((5 : ℝ) / 2)` for every real θ (`rpow52_eq`: cos(5π/2) = 0). Lipschitz bound 5/2 · S³ on the slab |θ| ≤ TH ≤ S² (`quint_sub_le`: each of the five terms of u⁵ − v⁵ over u − v bounded by S³ times u or v), closeness `g52_close`: if y ≥ c > 0, y ≤ P and |y² − x| ≤ η < c², then |√x⁵ − y⁵| ≤ η/c · 5(P² + η)² (each term bounded by (P² + η)²). Every other module is the index-three-halves one with the power changed (`LE52CellQ`: `qquint`; `LE52Glue`: one `nlinarith` for L ≥ 0); the singular start `Checked.Math.LEGStart` is reused unchanged.
- **Generator** `scripts/gen_le52.py` (from `gen_le32.py`: series exponent five halves, Taylor recursion of w⁵, γ and K formulas) and `scripts/emit_le52.py`: 140 cells, 10 segments, enclosure 9.3 · 10⁻¹⁶ at the bracket [5.355275458, 5.355275460]; mass factor on the last cell in [2.18719956551705, 2.18719956551711]. `LE52QData` decides in 288 s locally. First run of the generator succeeded with the run-1028Z precision parameters.
- **Existence** (`LE52ExistsLeft/Right`, `LE52Exists`): the index-three fixed point with the clamped power (bound (11/10)⁵ ≤ 1.728, Lipschitz 5/2 · (11/10)³ ≤ 9/2: inside the index-three constants); Picard–Lindelöf on [1/2, 6] with clamps |φ| ≤ 2, |θ| ≤ 16 (Lipschitz 164, norm bound 1032), inactive by the clamped energy (U ≥ 0) and |θ'| ≤ 2.
- **Fidelity**: referee (Sonnet) STANDS: own 45-digit values from two starts; margins ξ₁ 9.0e-9 / 9.9e-10, ω 5.5e-9 / 4.5e-9, ratio 4.7e-8 / 4.3e-8; θ'(0) = 0 implied; the junk value of the real power below zero harmless. Blind restatement (Sonnet): θ twice continuously differentiable on [0, 6], θ'(0) = 0 within [0, 6], equation on the open interval in `deriv` form; closed in Lean from the helper `core` with φ = `derivWithin θ (Icc 0 6)` (`Work/Math/LaneEmden52BlindClosed.lean`, script `mk_blind_closed52.py`). Blind literal reading (Sonnet; two routes agreeing to 37 digits): A, B, E = 2, 5, 2; Z, C, D = 0, 1, 6; P, K = 2, 3; every window equal to the statement's. Necessity: hypotheses 1, 3, 4 NEEDED (`Checked/Trust/Necessity.lean`), 2 REDUNDANT (`NecessityB.lean`).
- Values (reference `scripts/ref52.py`; referee and reader agree to 35 digits): ξ₁ = 5.3552754590107794599, ω = 2.1871995655170789532, ρ_c/ρ̄ = 23.406462267062708503.

## Measure
- Certified rows of the polytrope table: indices two, three, four, three halves → plus five halves. Fractional-index route: the second fractional index needed one new lemma file (three lemmas) and string changes elsewhere; freeze 16:3xZ → Work proof with existence and blind closure 16:5xZ, promotion with relock and Claims by 17:30Z (experiment of run 1028Z: met). Necessity: four hypotheses of the new headline classified (3 NEEDED, 1 REDUNDANT); NEEDED 706 → 709, REDUNDANT 216 → 217, open 89; StatementDeps 301 headlines, NV 181/181.

## CI read
- 44521044439 (68c077a): concluded success, every job green incl. the checked job and nanoda 4/4 → `laneEmden32_constants` PROVED.
- 44535193737 (7c52721, `NecessityAY`, `NecessityAZ`) at 17:3xZ: every job green except nanoda shard 1 (checking since 14:06Z, past 3 h); 44535498718 (73af250) and 44548457011 (ab284de) running. Nanoda shard 1 is the slow shard again (part 3's next step: a timing line in `scripts/nanoda_shard.sh`, then reassign).

## End
- See the final commit message for the local checks run before the push.

## Next
- CI read first: the run of this run's final push (promotion of `laneEmden52_constants`: nine new Checked modules, `SecondReadingLE52`, Witnesses, Necessity, NecessityB; every nanoda and leanchecker shard replays the new modules, `LE52QData` ≈ 290 s locally). Green on every job → PROVED: the judged template in its STATE.md heading (`check_stale_status.py`) and one L.2 line to Alexander. Red → `python3 scripts/trust/records_check.py <base>` or `local_frozen_step.py --trust <base>`.
- Then by rotation (parts 2/5 at 1628Z, part 3 at 1428Z, part 1 at 1228Z): part 1 as in section Next of `runs/2026-11-19T1228Z/README.md`; part 3 as in section Next of `runs/2026-11-19T1428Z/README.md`. Parts 2/5 later: index one half and other fractional indices below one (the power is not Lipschitz at zero: the crude cell needs θ ≥ 0 only, but the start and the slab bound need a lower bound away from zero, or a one-sided argument); λ₃ of the Gelfand branch (fourth turning point near s ≈ 4532); the rows of the polytrope table at the other half-integer indices above two (seven halves, nine halves) by the same generator (LEDGER experiment of this run).
