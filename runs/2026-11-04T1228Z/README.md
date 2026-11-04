# Run 2026-11-04T1228Z (scheduled)

Environment: add_repo not exposed; repo pre-cloned (detached HEAD, stale local `main` reset to origin/main). No LOCK (run 1028Z closed). **Local Lean available** (elan installer accepted; Mathlib cache; full Checked build ≈ 25 min uncached). Previous CI: 7d4553b (strengthenings) **41824437583 green**; 1028Z records 41826756512 running at start (read at close, STATE "Environment").

**THE RESULT:** part 2 (AI doing new science through the system) moves: B1 extended to the second paper of the dispute, the Lusso et al. 2019 fourth-order fits, frozen, proved, audited and promoted in one run.

**WHAT CAN A SCIENTIST NOW TRUST WITHOUT CHECKING IT THEMSELVES?** That the quasar-driven fourth-order fits of Lusso et al. 2019 (Table 2: SNe + quasars, SNe + quasars + GRBs) are not flat-ΛCDM shaped between 1 + z = 2√2 and 4√2: compared with the *exact* distance (not the Taylor point), the fitted curve's residual distance modulus rises by more than 7/20 mag (3/10 mag with GRBs) for every Ω ∈ [0, 1] and every normalisation, and strictly for every quartic beyond the printed 1σ ends (a region containing the whole ±1σ box, whatever the covariance). So this part of the reported deviation is not the truncation artefact of the critique. Certified in Lean for every scale factor obeying the flat ΛCDM expansion law; the SNe + GRBs fit, by contrast, is matched (Ω ≈ 0.354, floating point).

**WEAKEST UNCHECKED STEP NOW:** the meaning of the comparison for the dispute rests on the referee's reading (two-redshift shape test, flat models only — closed ΛCDM reproduces the ratio —, no significance: the box corresponds to ≈ 1–1.5σ, not 4σ). And the transcription of Table 2 is two readings by the same model (identical across arXiv v1–v4).

**BOTTLENECK AND WHY:** part rotation (part 2 idle for 4 runs, due) and STATE B1 "Not yet: the Lusso et al. 2019/2020 fourth-order fits". Yes = the dispute's second paper gets a certified curve-level statement; no = the L19 curves are ΛCDM-shaped and the critique stands for them.

**WHAT WE DID:**
1. Exploration (floating point, `scripts/l19.py`, `box.py`, `s.py`): the ratio d_L(4√2−1)/d_L(2√2−1) of exact flat ΛCDM decreases from 5.09 (Ω = 0) to 2.859 (Ω = 1); the central quartics give 2.401 / 2.470, the 1σ corners 2.821 / 2.829. Two redshifts suffice and every normalisation cancels.
2. Froze four statements (6dd5bc8, `Work/Cosmography/B1L19.lean`), then in one message: blind restater, referee, blind second reader of Table 2 (all four arXiv versions), and the prover (fork).
3. Proof (9384fd4): generated certificates `B1L19Certs.lean` (8 Ω-pieces × 20 tangent/chord cells: 2J₅ ≥ 2.84 J₃ for every Ω ∈ [0, 1]), exact polynomial algebra, logb monotonicity. Axioms standard.
4. Audit (`audit_l19.md`): blind restatement (weaker hypotheses: no differentiability, no order of the emission times, free k, no positivity) closed in Lean from the frozen theorems (`Work/Cosmography/B1L19Audit.lean`); referee STANDS-WITH-CORRECTIONS (`referee_l19.md`), module docstring corrected; Table 2 second reading agrees digit for digit.
5. Promotion to Checked (`Checked/Cosmography/B1L19.lean`, `B1L19Certs.lean`): headlines registered, `logPolyDL4` PRINTED, NV witnesses (`Checked.Trust.NV.l19_*`), relock, trust map, packet; FINDINGS candidates C28 (L19's "below 2%" sentence false except in narrow Ω windows; prior art Yang et al. 2020 Fig. 1) and C29 (this result).
6. Two PROMPT working notes (stale pre-cloned `main`; part 2 should ask "is the answer already in print?" before freezing; LEDGER experiment).

**RESULT:** 4 new AUDITED headlines, PROVED once the main CI of the promotion commit is green (STATE).

**WHAT COULD STILL BE WRONG:** the qualitative conclusion (the quasar Hubble diagram prefers flat models with Ω_m near 1) is already in print (Yang et al. 2020, Khadka & Ratra 2020, Bargiacchi et al. 2021); what is new is the certified, Ω-uniform, normalisation-free form. The z ≈ 4.66 point reads the quartic where the data are sparse. Table 2's confidence level and "central value" meaning are not stated by the paper.

**NEXT:** STATE "Exact next step".
