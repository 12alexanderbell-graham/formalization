# Run 2026-11-13T1522Z

Scheduled run (14:27Z slot, fired 15:22Z). LOCK of run 2026-11-13T1228Z (taken 12:28Z, task STATE 0g) had no push or heartbeat for 177 min: taken over by rule 48.4 (32b3c79). That run left nothing on any branch; its task was redone here.

**THE RESULT:** part 1 (statement fidelity, T2b hypothesis necessity): 13 open hypotheses of six Checked claims classified by machine-checked proofs — run 0828Z's compiled scratch promoted (`b > 0`, `b < v_l` of `vdW_coexistence_unique` and `b < v_l` of `pr_omega1_unique`, `pr78_omega1_unique` REDUNDANT; all four hypotheses of `printedEta20_false_at`, `printedEta30_false_at` classified) and one new witness: `0 < b` of the Redlich–Kwong existence claim `rk_coexistence_exists` NEEDED. Open hypotheses 280 → 267, fully classified headlines 61 → 63 of 160 (local; CI pending).

**What can a scientist now trust without checking it themselves, that they could not before?** That in the Redlich–Kwong acentric-factor existence claim the assumption "positive co-volume" carries the result: with b = −1 a junk critical point at a zero of the attraction denominator meets every other assumption and no coexistence state with the certified ratio exists (Lean proof, standard axioms) — and the five claims of run 0828Z's scratch now carry their classifications in the CI-generated trust map rather than in an unmerged branch.

**Weakest unchecked step:** CI has not judged this push (the checked job of 028d5c4 took 150 min of build); the coexistence hypothesis of the cubic-EOS claims is still classified only as a bundle (four conjuncts), and every remaining open hypothesis of the RK/SRK/PR family is a bundled one.

## Steps
1. Start: stale detached checkout; `git checkout -B main origin/main` = 7fae04a; LOCK of run 1228Z stale → takeover. elan + Mathlib cache ≈ 4 min; CI artifact `checked-build` of 43422957898 (028d5c4) restored in 35 s.
2. CI read: 43422957898 (028d5c4, run 1028Z's FB8/FB9 push) **green on every job** (checked job: build 12:13–14:43Z, trust step 13 min, nanoda memoised 4/4).
3. Promotion (STATE 0g): `runs/2026-11-13T0828Z/lean/*.lean` → `Checked/Trust/MaxwellRightVdW.lean`, `MaxwellRightPR.lean`, `NecessityEta.lean` (byte-identical to `wip/necessity-0828z` 2bcc1a9b); LEDGER lines and PROMPT note copied verbatim from that branch; baseline lines removed as there. Built in 24 s on the restored build.
4. New: `Checked/Trust/NecessityW.lean`, `rk_coexistence_exists_h3` (b = −1, R = 1, A = 4, T_c = 10/7; the isotherm 1/(v + 1) − 4/(v² − v) at 0.7 T_c takes a pressure in (3/50, 1/15) at most once above b: strictly decreasing on (−1, 0), equal to 1 and 1/2 at the poles by x/0 = 0, above 1/2 on (0, 1), below 1/17 on (1, ∞)). Compiled first try; axioms propext, Classical.choice, Quot.sound.
5. `TRUST_RELOCK=1` StatementDeps (≈ 12 min): 930 hypotheses of 160 headlines, needed 514, redundant 149, open 267; frozen.txt +50 entries (new modules only).
6. CI replica `local_frozen_step.py --trust 028d5c4` (see below).
