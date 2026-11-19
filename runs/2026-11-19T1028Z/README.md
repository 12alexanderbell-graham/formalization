# Run 2026-11-19T1028Z

**THE RESULT:** parts 2 and 5 by rotation (STATE 1x → parts 2/5 as in section Next of `runs/2026-11-19T0428Z/README.md`). The Lean theorem of this run (its name is in the run record below) bounds, for every solution of the Lane–Emden equation of index three halves with central value one on the range to four, the radius where the solution meets zero, the mass factor and the central-to-mean density ratio, each in a closed interval; a solution with every hypothesis is in Lean.

**What can a scientist now trust without checking it themselves, that they could not before?** A row of the table of polytropes with a fractional index (three halves: the convective-star polytrope), as one kernel theorem from the equation, for every solution; the validated simulator now handles a power that is not a polynomial and not smooth where the solution meets zero.

**Weakest unchecked step:** the statement is from one model three times (a subagent and two subagent readers); the intervals are kernel theorems.

## Start
- The theorem: `Checked.Math.LaneEmden32.laneEmden32_constants`. Frozen a27bcab before any proof, proved in Work 5f1b1f0 (statement unchanged), promoted by `runs/2026-11-19T1028Z/scripts/promote_le32.py`. Existence `Checked.Math.LE32Exists.exists_solution` (NV witness). Referee STANDS (`referee/REPORT.md`); blind restatement closed (`Work/Math/LaneEmden32BlindClosed.lean`); blind literal reading `Checked/Trust/SecondReadingLE32.lean` (brief 82a25c4): every coefficient, range end and window agrees.
- 10:28Z. Local main was a stale shallow clone; `git checkout -B main origin/main` at a5b8314. No LOCK → taken (a27bcab, with the freeze).
- CI at start: 44478483601 (9594da2): every job green except nanoda shard 1 (running since 07:42Z). Read again at 11:17Z: nanoda shard 1 green (10:52Z), run concluded success → `gelfand_pde_radial_count_turning` and `laneEmden4_constants` PROVED (STATE headings rewritten; Alexander told).
- Local Lean: elan + `lake exe cache get` ≈ 3 min; `checked-build` of 44478483601 (2.6 GB) restored.

## Bottleneck (and what a yes/no changes)
- Parts 2/5 by rotation. Open since run 2026-11-08T0228Z: half-integer Lane–Emden indices ("θ^{3/2} has no polynomial Taylor recursion; needs a one-sided treatment at the zero"). Question: can the validated-cell simulator carry a non-polynomial, non-smooth nonlinearity with kernel-decided cells? Yes → the polytrope used for fully convective stars is certified and the simulator is no longer limited to polynomial fields. No → the method limit is real and recorded with its cause.

## What we did
- **Power as a square root cubed** (`Checked/Math/LE32Cell.lean`): `g32 θ = √θ ^ 3` equals Mathlib's `θ ^ ((3 : ℝ) / 2)` for every real θ (`rpow32_eq`: for a negative base Mathlib's real power is exp(log x · y) cos(yπ), and cos(3π/2) = 0). Lipschitz bound 3/2 · S on the slab |θ| ≤ TH ≤ S² (`g32_lip`, from u³ − v³ = (u − v)(u² + uv + v²) and |√a² − √b²| ≤ |a − b|), closeness `g32_close`: if y ≥ c > 0, y ≤ P and |y² − x| ≤ η < c², then |√x³ − y³| ≤ η/c · (3P² + 3η/2). Grönwall cell `cell` on the generic tube lemma of `LENCell`.
- **Kernel-decided cells** (`LE32CellQ.lean`): the defect of the second component uses `pw³`, `pw` the Taylor polynomial of √θ, with the square certificate decided per cell; next to the zero a crude cell (`pw = []`, θ^{3/2} of the polynomial ≤ P³ from pt ≤ P²) uses the Taylor polynomial of the equation without the power. Singular start generic in the nonlinearity (`LEGStart.lean`, from `LENStart`); start and last cell each one rational proposition (`LE32Glue.lean`; list identities through `qeqB`, structural and built from ≤).
- **Generator** `scripts/gen_le32.py` (mpmath Taylor coefficients rounded to 10⁻²¹, every inequality re-checked in Fractions) and emitter `scripts/emit_le32.py`: start at one half (series of θ and √θ in ξ², rational by Miller's recurrence), 72 bulk cells, geometric cells toward the zero (ratio five) to distance 10⁻⁴, one crude cell to the bracket and the crude last cell [3.653753735, 3.653753737]; 106 cells, 7 segments; enclosure 1.6 · 10⁻¹¹ there; mass factor on the last cell in [2.7140551198, 2.7140551203]. `LE32QData` decides in ≈ 100 s.
- **Existence** (`LE32ExistsLeft/Right`, `LE32Exists`): the index-three fixed point at the centre with the clamped power (bound and Lipschitz constant inside the index-three constants); Picard–Lindelöf on [1/2, 4] for the field clamped at |φ| ≤ 2, |θ| ≤ 9: the clamped energy Ψ(φ) + U(θ) is nonincreasing and U ≥ 0 (the power vanishes below zero), so |φ| < 2, and |θ'| ≤ 2 keeps |θ| < 9; glued.
- **Fidelity**: referee (Sonnet, brief 82a25c4) STANDS: own 40-digit values by two methods; margins ξ₁ 6.2e-9 / 3.8e-9, ω 1.01e-8 / 9.9e-9, ratio 1.63e-8 / 1.37e-8; θ'(0) = 0 implied; the junk value of the real power below zero is harmless (conclusions on [0, ξ₁]). Blind restatement (Sonnet): equation on the open interval in `deriv` form, `IsLeast` first zero; closed in Lean (`Work/Math/LaneEmden32BlindClosed.lean`, the index-four bridge with |θ^{3/2}| ≤ (C + 1)³). Blind literal reading (Sonnet): A, B, E = 2, 3, 2; Z, C, D = 0, 1, 4; every window equal to the statement's. Necessity: hypotheses 1, 3, 4 NEEDED (`Checked/Trust/Necessity.lean`), 2 REDUNDANT (`NecessityB.lean`, `cont_at_zero_of_continuous`).
- Values (reference `scripts/ref32.py`, referee and reader agree to 30 digits): ξ₁ = 3.6537537362191224, ω = 2.7140551201086457, ρ_c/ρ̄ = 5.9907045163035336.

## Measure
- Certified rows of the polytrope table: indices two, three, four → plus three halves (the first non-integer index). The simulator's field class: polynomial → any field with a square-root certificate. Necessity: four hypotheses of the new headline classified (3 NEEDED, 1 REDUNDANT).

## CI read
- 44478483601 (9594da2): concluded success, every job green incl. the checked job and nanoda 4/4 → `gelfand_pde_radial_count_turning` (cf5003e) and `laneEmden4_constants` (37e93d9) PROVED.
- 44502936666 (a5b8314): in progress at 11:17Z (same Checked input as 9594da2).

## End
- See the final commit message for the local checks run before the push.

## Next
- CI read first: the run of this run's final push (promotion of `laneEmden32_constants`: ten new Checked modules, `SecondReadingLE32`, Witnesses, Necessity, NecessityB; every nanoda and leanchecker shard replays the new modules, `LE32QData` ≈ 100 s locally). Green on every job → PROVED: the judged template in its STATE.md heading (`check_stale_status.py`) and one L.2 line to Alexander. Red → `python3 scripts/trust/records_check.py <base>` or `local_frozen_step.py --trust <base>`.
- Then by rotation (parts 2/5 at 1028Z, part 3 at 0828Z, part 1 at 0628Z): part 1 as in section Next of `runs/2026-11-19T0628Z/README.md`; part 3 as in section Next of `runs/2026-11-19T0828Z/README.md`. Parts 2/5 later: index five halves (same generator: `LE_*` parameters, the start series by Miller's recurrence at exponent five halves; the cell module needs the power `√θ ^ 5` and its Lipschitz bound), λ₃ of the Gelfand branch (fourth turning point near s ≈ 4532).
