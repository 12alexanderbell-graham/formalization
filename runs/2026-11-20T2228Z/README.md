# Run 2026-11-20T2228Z

**THE RESULT:** parts 2/5 by rotation (STATE 2p). The Lean theorem of this run and its statement are in section What we did.

**What can a scientist now trust without checking it themselves, that they could not before?** That the bound on the parameter of the Gelfand problem in the three-dimensional ball holds for every solution, radial or not, as a headline of the claims page with a blind restatement, a referee and a non-vacuity witness (section What we did).

**Weakest unchecked step:** whether the regularity hypothesis of the new headline is needed (section What we did; the necessity section of `TRUST_MAP.md`).

## Start
- 22:28Z. Local main was the stale divergent clone (fa47717, its commits are on origin/wip/leanchecker-shards); worked on branch `run-main` tracking origin/main at ecc9fc7 and pushed to main. No LOCK → taken (0e83987).
- Env: repo ok (add_repo not exposed; the session clone was present). **Local Lean installed this run** with the official elan installer (toolchain v4.35.0), `lake exe cache get`, the judge's build restored by streaming (`scripts/restore_checked_build.sh`, artifact of 44818441588, ecc9fc7; 17 GB, `lake build --no-build Checked` up to date). Subagents: one Sonnet (blind restatement), one Opus (referee).
- CI at start: 44818441588 (ecc9fc7, run 2028Z's final push) completed.

## CI read
- 44818441588 (ecc9fc7): **green on every job** (21:13Z → 22:03Z); the kernel shards were memoised on unchanged input, so this run reads no nanoda time (the refit question of run 2028Z's Next stays for a run with all four shards running). No headline changed: nothing to promote.

## Bottleneck (and what a yes/no changes)
- Run 1828Z proved the Gelfand bound with no symmetry hypothesis (`Checked.Math.GSymFree.bound_no_radial`) only as a necessity witness: no listed headline said it, so no claims page, blind restatement or referee covered it. Can it go freeze → Checked as a headline of its own in one run? Yes → the claims page gains the statement every classical solution obeys, audited. No → the step of the pipeline that blocks is recorded.

## What we did
- **Freeze** d069e5f: `Work.Math.GelfandPDEBound.gelfand_pde_bound`, the statement of `gelfand_pde_radial_bound` with the radial hypothesis removed (docstring: the parent's, without 'a function of ‖x‖ on the closed ball').
- **Blind restatement** (brief ac0adc9 committed alone; Sonnet; output committed alone): a predicate `IsClassicalGelfandSolution` (C² on the open ball, continuous on the closed ball, the equation on the open ball, zero on `Metric.sphere 0 1`), conclusion `lam ≤ 3.321992119` from the existence of a solution. Copied to `Work/Math/GelfandPDEBoundBlind.lean` with one compile repair (`InnerProductSpace.laplacian` is not a Mathlib name; written `Laplacian.laplacian`, the function behind `Δ`) and closed from the frozen statement (`Work/Math/GelfandPDEBoundBlindClosed.lean`, `blind_closed`).
- **Referee** (Opus, statement file only; `referee_gelfand_pde_bound.md`): STANDS. Own mpmath integration (40 and 55 digits, two starts): s* = 4.0714968442981393476, λ* = 3.3219921183398239884, margin 6.6e-10 below the bound; with 3.3219921 the statement is false (the radial solution at s* meets every hypothesis). Near-misses: without the boundary condition every λ > 0 has a solution; the bound 2 is false. Its one open item, that `Checked.Math.GSymFree` might redefine `Δ`: it does not (the module adds theorems and definitions in its own namespace; the Laplacian is Mathlib's, as in the parent).
- **Proof** 01c1905 (statement byte-identical to the freeze): `exact Checked.Math.GSymFree.bound_no_radial lam u hu hc hb hpde`; axioms propext, Classical.choice, Quot.sound (local `#print axioms`, both the headline and `blind_closed`).
- **Promotion:** `Checked/Math/GelfandPDEBound.lean` (statement and docstring byte-identical up to the namespace); non-vacuity witness `Checked.Trust.NV.gelfand_pde_bound` (the radial solution at 3.321992118 from `gelfand_pde_radial_exists`); literal readings: those of `gelfand_pde_radial_bound` (space, open and closed ball, regularity, continuity).
- **Necessity** (`Checked/Trust/NecessityBH.lean`): hypotheses 2 (continuity on the closed ball), 3 (zero on the sphere), 4 (the equation) NEEDED, by the counter-examples of the radial statement (`NecessityM`, `NecessityB`) with the radial component left out: u − 2 for the solution at λ = 1 solves the equation with λ = e² > 3.321992119, with boundary value −2 (3) or redefined as 0 on the sphere (2); the zero function with λ = 4 (4). Hypothesis 1 (C²) stays open: `NecessityBF` proved it redundant for the radial statement through symmetry (isolated bad radii); without symmetry the same question needs a maximum principle for functions only twice differentiable.

## Measure
- Listed headlines: 305 → 306; the Gelfand statement for every classical solution is now on the claims page with a blind restatement closed in Lean, a referee verdict and a non-vacuity witness. Necessity: NEEDED +3, open +1 (disclosed in LEDGER).

- **Second relock, and a tool for it:** the first records_check failed V1 of `check_claim_vocab.py` on the frozen docstring ('classical', 'symmetry', words copied into the parent's docstring and never tested) and `check_literals` rule 1 on the parent's reading `gelfandPdeClosedBall` (its body matched the parent only through the radial hypothesis). The Checked docstring's first clause was reworded (statement unchanged; LEDGER), the reading left out (`gelfandPdeContinuous` covers the closed ball), and StatementDeps + Claims run again (≈ 20 min). `scripts/trust/check_freeze_name.py --file` now also lists such docstring words at freeze time (`DOCWORD`; control: it names exactly 'classical' and 'symmetry' on this run's freeze and passes the reworded docstring; advisory: it flags 49 of the 155 listed headlines it parses, whose words reach the generated claim through definitions). PROMPT working note; LEDGER experiment.

## Local checks
- `lake build Checked` (restored build of ecc9fc7; 3755 jobs), `lake build Work.Math.GelfandPDEBoundBlindClosed`, `#print axioms` of the headline and the blind closure, `precheck_names.py`, `check_prose.py`, `precheck_citations.py`, `check_status_lines.py`, `TRUST_RELOCK=1 … StatementDeps.lean` twice (306 headlines, NV 185/185, necessity 750 / 223 / 58 open), `Claims.lean` twice (after the last registry edit), `validation/make_packet.py --check`, `check_headline_mentions.py --base ecc9fc7`, `records_check.py ecc9fc7` (43 commands, 0 failed).

## Next
- CI read first: the run of this run's final push (new Checked modules `GelfandPDEBound`, `NecessityBH`; `Witnesses` changed). Green on every job → `gelfand_pde_bound` PROVED: the judged template in its STATE.md heading (`check_stale_status.py`) and one L.2 line to Alexander. Red → `python3 scripts/trust/records_check.py <base>`.
- Part 1 candidate: hypothesis 1 of `gelfand_pde_bound` (C² on the open ball). With λ > 0 the equation makes Mathlib's Laplacian nonzero, so u is twice differentiable at every point of the ball (as in `NecessityBF`); the question is whether `GMaxPrinciple.superharmonic_nonneg` and the comparison of the iterates hold for functions twice differentiable at every point with a continuous Laplacian (the classical weak maximum principle needs only pointwise second derivatives at an interior maximum).
- Parts 2/5 next: the contracting cell as in section Next of `runs/2026-11-20T1628Z/README.md` (start from `GLamChain`'s end box, log radius, fifth turning value), or the existence side for every λ ≤ 3.321992118 is already `gelfand_pde_radial_exists`; a count of all (not only radial) solutions needs the symmetry of every solution and is not covered by the minimal-solution route.
