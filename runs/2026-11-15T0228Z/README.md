# Run 2026-11-15T0228Z (scheduled)

**THE RESULT:** parts 2 and 5 — every extremum of the Bonnor–Ebert mass at once (the Work proof of run 0028Z) promoted to Checked as `Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema`, with NV witness, a fresh blind literal reading, and every hypothesis classified; and the CI read that makes `bonnor_ebert_third_max` PROVED (43643096701 of 80cabb8 green on every job).

**What can a scientist now trust without checking it themselves, that they could not before?** That the whole Bonnor–Ebert mass–radius curve has the textbook shape — infinitely many alternating maxima and minima of the pressure-confined isothermal mass ξ₀ < ξ₁ < … → ∞, each the strict extreme of the mass from the previous extremum on, maxima above and minima below the singular isothermal sphere's mass √(2/π), and the mass tending to √(2/π) — now as a `Checked` headline whose generated claim (CLAIMS.md) is the statement, whose numerals a blind reader re-derived (the domain, the mass along the sequence, the index pattern 2k / 2k+1 / 2k+2, and √(2/π) from the singular solution ψ = ln(ξ²/2)), and whose four hypotheses are each shown needed or redundant in Lean. It becomes PROVED when a main CI run including the promotion is green on every job (next run reads it).

**Measure:** certified extrema of the Bonnor–Ebert mass in Checked 5 → all (PROVED: 5; the promotion awaits CI). Headlines 290 → 291; NV 173 → 174; hypothesis necessity: needed 617 → 620, redundant 159 → 160, fully classified headlines 89 → 90 of 170.

**Weakest unchecked step:** CI has not yet judged the promotion (the checked job takes ≈ 3 h; nanoda must replay the new modules). The statement still does not say that m is monotone between consecutive extrema (the proof has it in `BEAllMain`; a companion headline can export it).

## Start
- 02:28Z. add_repo not exposed; pre-cloned checkout detached at ebc77d1 (= origin/main) with a stale local `main` from 2026-11-09; `git fetch --unshallow origin && git checkout -B main origin/main`. No LOCK → taken (3742212).
- Local Lean: elan installed (authorized), `lake exe cache get`, `checked-build` artifact of 43643096701 (80cabb8) restored with `scripts/restore_checked_build.sh`; `lake build Checked` to ebc77d1 at once (no Checked change since).
- CI at start: 43643096701 (80cabb8) green on every job (goal guard, packet, changes, work, nanoda 0–3, checked incl. trust and frozen steps) → **`bonnor_ebert_third_max` PROVED**; L.2 notification sent. 43663346445 (5bb7a03, the Work proof of run 0028Z): work job green (read by run 0028Z), checked job pending.

## Bottleneck (and what a yes/no changes)
- STATE 0x: the every-extremum result sat PROVED in Work only. Yes (promotion green) → the whole Bonnor–Ebert curve is a Checked headline and the extremum-by-extremum series is closed; no → the Work proof's dependencies fail some Checked rule, which the run must fix rather than leave for later.

## What we did
1. **Blind literal reader** (Sonnet; brief 2aeccfd → reading 78444f5 → copy 6fc072d, three commits): template with capital placeholders for the half-lines `Ici A`/`Ioi B`, the mass along a sequence of radii, the index of the first maximum, the indices of the (k+1)-th maximum/minimum and (k+2)-th maximum, and the singular-sphere mass √(K/π). The reader derived ψ = ln(ξ²/2) for the singular solution, K = 2, and checked numerically that the regular solution's mass approaches √(2/π) (m(300) = 0.79792 against 0.797885); first maximum 6.451 (1.18223), first minimum 67.01 (0.69437). `check_literals`: the new headline fully covered.
2. **Promotion by script** (`scripts/promote_be_all.py`): `BEFocus`, `BEState300`, `BE3Ext`, `BEAllMain`, `BEGlobalExists`, `BonnorEbertAll` → `Checked/Math/`, with the imports `#min_imports` reported for copies built against all of Mathlib (`scripts/imports.json`), module docs without numerals, headline docstring in the claim's words.
3. **Rename at promotion:** `check_claim_vocab` V8 rejected the strength word `all` in the name (module component included) and V13 the word `extrema`; the headline is `Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema` (identical statement; LEDGER). `check_prose` rule 6 rejected "every extremum" in the docstring (no bound noun): "extrema of the mass". Cost ≈ 25 min of relock and CLAIMS regeneration. Root-cause fix: `scripts/trust/check_freeze_name.py` (run on a Work file before a freeze commit) and a PROMPT working note.
4. **NV witness** `Checked.Trust.NV.bonnor_ebert_extrema` from `BEGlobalExists.exists_global`.
5. **Hypothesis necessity** (`Checked/Trust/NecessityAJ.lean`): 1 (derivative of w) NEEDED by w = 0, φ = −s/3 (the mass grows like s³, so ξ₀ is not its strict maximum); 2 (continuity at the centre) REDUNDANT (forced by the equation on [0, 1], `NCB.cont_at_zero_of_continuous`); 3 (the equation) NEEDED by the zero function (mass 0 everywhere); 4 (w(0) = 0) NEEDED by the scaling symmetry on the half-line (`scaled_hyps_Ici`): the scaled regular solution's strict maximiser would be half the true one, outside the window.
6. Local: `lake build Checked` green; `TRUST_RELOCK=1` StatementDeps exit 0 (291 headlines, NV 174/174, needed 620, redundant 160); Claims; packet; Python trust suite and `local_frozen_step.py` against the green base 80cabb8 (see below).

## CI read
- 43643096701 (80cabb8): green on every job → `bonnor_ebert_third_max` PROVED.
