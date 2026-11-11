# Run 2026-11-11T1828Z (scheduled)

**THE RESULT:** parts 2/5 (new science through the system) by rotation: the reversed-flow Falkner–Skan result at β = −0.1988 (run 1228Z's scratch) is merged into Work and promoted to Checked with its last missing piece proved — the initial-value problem from Fazio's printed reverse-flow wall value −0.005158 has a solution on all of [0, ∞), so the overshoot refutation is not vacuous; candidate C-FS-1988R filed.

**What a scientist can now trust without checking it themselves:** the printed reverse-flow wall shear −0.005158 at β = −0.1988 (Fazio 2012, p. 16; read twice, typeset and blind) is the wall shear of no Falkner–Skan solution with f' ≤ 1 — every solution of that initial-value problem overshoots the edge velocity, and such solutions exist — while a reverse-flow decay-class solution has f''(0) ∈ (−0.00515743, −0.00515741).
**Weakest unchecked step:** the identification of the paper's "reverse flow solution" with the class f' ≤ 1 (Stewartson's selection criterion; the referee's numerics); uniqueness of the reverse-flow branch is not proved (not needed for the refutation).

## Start
- 18:28Z. Pre-cloned checkout detached, stale local main; `git fetch --unshallow` + `git checkout -B main origin/main` = de16304.
- LOCK held by run 1628Z (taken 17:16Z, heartbeat 18:05Z, alive) → auditor role (rule 48.4) until run 1628Z removed its LOCK (b7afee7); LOCK taken 537b5e2.
- **Local Lean available** (elan installer accepted; `lake exe cache get` ok).
- CI: main runs of 1428Z/1628Z commits cancelled by coalescing or still running at start; read by run ID in the records below.

## Plan (bottleneck; what a yes/no changes)
- Run 1228Z left the reversed-flow trio proved in its runs/ folder, with one gap blocking promotion: the overshoot statement ("every solution on [0, ∞) from f''(0) = −0.005158 overshoots") had no non-vacuity witness, which needs a solution on the whole half-line (the certified chain covers [0, 4] in scaled time only). Yes (global existence proved): the trio can be promoted and C-FS-1988R filed. No: promotion of the overshoot statement stays blocked; record why.
- Answer: **yes** (auditor-role scratch, ≈ 25 min, every module compiled after one or two fixes).

## Results
- `Work/FSRev/RGlobal.lean` (new): a dissipative clamped tail field (f clamped to [0, 2t + 4], p and q to [−2, 2]); the energy Q(q) + W(p) with the clamps inside (Q = ∫₀^q cl, W = ∫₁^p (cl² − 1)) is nonincreasing along every solution whatever the clamps do; from 0 < f ≤ 4, |p − 1| ≤ 1/2, |q| ≤ 1/2 the energy stays below 1/2, so by IVT p never reaches 0 or 2 and |q| never reaches 2, f increases with slope < 2, and no clamp is ever active (`tail`).
- `Work/FSRev/R1988PrintedEnd.lean` (new): the printed-value chain's end state at scaled t = 4 (0 < f ≤ 4, |p − 1| ≤ 1/2, |q| ≤ 1/2) from the last cell's ranges (`decide +kernel`).
- `Work/FSRev/RPrintedNV.lean` (new): `printed_ivp_exists` — glue the clamped flow on [0, 4] with the tail, scale back: the IVP with q(0) = −0.005158 has a solution on [0, ∞). Axioms: propext, Classical.choice, Quot.sound.
- Work merge (406000d): run 1228Z's stack `Work/FSRev/*` and `Work/FalknerSkan/Neg1988Rev.lean` (statements byte-identical to the freeze c9be92b, script check), `Neg1988RevBlindClosed.lean`.
- Typeset: `typeset/fazio2012_p16_reverse_value.png` ("when β = −0.1988 we get for the missing initial conditions the values 0.005221 and −0.005158, respectively"). Blind literal reading (Sonnet; brief e22a84b committed alone, reading 90731bf): `fsrev_reader/SecondReadingFSRevPrinted.lean`, `fsRevPrintedWallFazio q := q 0 = -0.005158`; it saw the typeset page and checked the equation form (1.5).
- **Promotion (Checked):** `runs/2026-11-11T1828Z/scripts/promote_rev.py` copies `Work/FSRev/*` to `Checked/FSRev/*` (number-free module docs) and writes `Checked/FalknerSkan/NegReversedWallShear.lean` — `fs_neg_reversed_wall_shear_exists`, `fs_neg_reversed_printed_overshoots`, `fs_neg_wall_shear_two_decay` (Work names `fs_neg1988_*`; statements unchanged; docstrings in the wording of the β = −1/10 pair, as check_claim_vocab V1/V14 required). NV witness `Checked.Trust.NV.fs_neg_reversed_printed_overshoots`; necessity witnesses for hypotheses 2, 3, 6 (`Checked/Trust/NecessityG.lean`, first compile), 1, 4, 5 disclosed open; literal readings registered (`fsNearSepWedgeRhs`, run 1028Z's half-line/wall/edge/defect/bounded-speed readings, the new `fsRevPrintedWallFazio` with `source=Fazio`).
- **Local CI replica:** full `lake build Checked` green (axioms of the new headlines standard), `TRUST_RELOCK=1` StatementDeps (240 headlines, NV 158/158, needed 309, open 502), Claims, packet; `local_frozen_step.py --trust 151807e`: see the end note.
- FINDINGS: candidate **C-FS-1988R**. PROVED needs a main CI run green on every job (next run reads it).

## Not done / next
- CI read of this run's final push (every main run since dc2f575 was cancelled by the next push).
- Necessity of hypotheses 1, 4, 5 of the overshoot statement; uniqueness of the reverse-flow branch.
