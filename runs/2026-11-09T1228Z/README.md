# Run 2026-11-09T1228Z (scheduled; auditor role 12:27–13:38Z, then LOCK)

**THE RESULT:** parts 2 and 5 — Falkner–Skan β = −1/10 **reversed-flow (Stewartson) solution PROVED in Work + AUDITED**, with its wall shear certified to ten decimals (−0.1405462131 < f''(0) < −0.1405462129), hence two solutions in the decay class (f'' > 0 is needed for uniqueness); and the **ten-decimal window 0.3192697598 < f''(0) < 0.3192697599 of the attached solution** (every solution with f'' > 0 and the decay property). Built as scratch under run 1028Z's LOCK, frozen 9149f56 and moved to Work 9f7db47 after the release.

**What can a scientist now trust without checking it themselves, that they could not before?** That at β = −1/10 the Falkner–Skan problem has a reversed-flow solution approaching the edge faster than every exponential, with f''(0) = −0.14054621… to ten decimals (the printed six digits −0.140546 agree), so that the decay class alone does not determine the solution; and ten decimals of the attached solution's wall shear, 0.31926975984… (no printed value at β = −0.1 found).

**Measure:** 4 theorems PROVED in Work (standard axioms, local lake build), blind restatements 2/2 closed, referee: 0 defects in statements or route, independent values by two methods inside both windows; the research note's Lemma D replaced by a certified tube over the whole parameter window.

**Weakest unchecked step:** CI has not yet built the new modules (work job of 9f7db47, run 42628334624, queued at 13:46Z); the four theorems are not in Checked (window ends and β need blind literal readings; NV witnesses).

## Start
- 12:27Z. add_repo not exposed; pre-cloned checkout detached, shallow, stale local main; `git fetch --unshallow` and `git checkout -B main origin/main` (local branch only) = 8eb3ece.
- LOCK held by run 2026-11-09T1028Z (started 10:27Z, heartbeat 12:06Z, promotion build of the β < 0 stack running): alive, so this run writes only in its own folder plus a CHANGELOG append (48.4). STATE.md, LOCK and active proof files untouched.
- Local Lean: elan installer + `lake exe cache get` worked.

## Scratch: ten-decimal window of the attached β = −1/10 solution (compiled locally)
- Certified chains (generator and emitter of run 0828Z unchanged; `scripts/make_window.sh`): Slow at scaled 1.009619629 on [0, 3] (96 cells, h = 1/32, degree 12, 10⁻¹⁸ coefficients; path margin q − B ≥ 2.2·10⁻¹², end margins 1 − p ≈ 2.8·10⁻¹¹ above 0, 3(1 − p) − q ≈ 8.2·10⁻¹¹), Over at 1.0096196292 on [0, 11/4] (44 cells, h = 1/16, degree 16; end margin p − 1 ≈ 2.0·10⁻¹¹); `lean/NWinLo.lean` 95 s, `lean/NWinHi.lean` 78 s (`lake env lean`, green).
- `lean/NWindow.lean`: `core_window` (the supremum argument of `Work.FSNeg.NAssemble.core_exists` for any certified window lo < hi ≤ 11/10; the neither-point is strictly inside because lo has Slow and it has not), √10 enclosures, `ten_window`, `ten_monotone_lt`; green against the built Work modules.
- `lean/NegWindow.lean` (statements to freeze in Work): `fs_neg_tenth_window` (every solution with q > 0 and the faster-than-every-exponential approach has 0.3192697598 < f''(0) < 0.3192697599) and `fs_neg_tenth_monotone_lt` (every solution with q > 0 has f''(0) < 0.3192697599); green against a stub of the two chain theorems (scratchpad, outside the repository).
- Update 13:25Z: `NegWindow.lean` and `NWBlindClosed.lean` also compiled against the real chains (`lake build` of local untracked copies under `Work/`, not committed); blind restatement (`blind/`, Sonnet, words only) closed; prior-art screen `screen/REPORT.md`: no printed attached-branch value at β = −0.1 found.

## Scratch: a reversed-flow (Stewartson) solution at β = −1/10, and two solutions in the decay class (compiled locally)
- `lean/low/`: chains by `scripts/make_lower.sh` (`gen_low.py`, `emit_low.py`: variants of run 0828Z's with modes slowL and tube) — Over at scaled −0.4444461497 (120 cells, [0, 15/4]), the lower Slow event `SlowL` at −0.4444461493 (128 cells, [0, 4]), and a **tube for the whole window** (radius 2·10⁻¹⁰ around −0.4444461495, 48 cells on [0, 3/2]: inside the clamps, p > −1/2, ends in 0 < f < 1, 0 < p < 1, 0 < q < 6/5). The tube replaces the research note's dip comparison (Lemma D).
- `LCell` (cell_box, sideP, endT, endSL, SlowL), `LInv` (Lemma I for the clamped field) and `LUnclamp` (no clamp after 3/2 when p ≤ 1; energy) — the last two by forks with exact statements (≈ 2–3 min each); `LAssemble` (events open and disjoint, neither-point in the decay class with −1/2 < p < 1, `core_lower`).
- `NegReversed.lean`: `fs_neg_tenth_reversed` (a solution with −1 ≤ f' ≤ 1, f' → 1, faster-than-every-exponential approach and −0.1405462131 < f''(0) < −0.1405462129) and `fs_neg_tenth_two_decay` (two such solutions with different f''(0): the hypothesis f'' > 0 of `fs_neg_decay_equal` is needed). `#print axioms`: propext, Classical.choice, Quot.sound.
- Audit: blind restatement (`blind2/`, Sonnet, words only) closed in `lean/low/NRBlindClosed.lean`; referee (Opus, `referee/REPORT.md`): no defect in the statements or route; own values −0.14054621297867 and 0.31926975984254 (two methods) inside both windows; printed −0.140546 (Asaithambi; arXiv 1212.5057 Table 4) consistent; documentation defects 2–6 fixed.
- Kind (part 2): the reversed-flow value is printed to 6 digits; the certified 10-digit window, the rigorous existence and the decay-class non-uniqueness are, as far as the two screens found, new in rigorous form.

## LOCK and move to Work
- 13:36Z run 1028Z released its LOCK (8cd5eb6, promotion 83ebad4 of the β < 0 stack); LOCK taken 5c5c02f (13:38Z).
- Freeze 9149f56 (four statements, `sorry`, identical to the scratch statements read blind); proofs 9f7db47 (statements unchanged, checked by script; ten `Work/FSNeg/` and four `Work/FalknerSkan/` modules, `Work.lean` imports). Local: `lake build Work.FalknerSkan.NWBlindClosed Work.FalknerSkan.NRBlindClosed` green (13:40–13:44Z).
- CI: freeze 9149f56 → run 42627421262; proofs 9f7db47 → run 42628334624 (queued); run 1028Z's promotion 83ebad4 → 42626827566 (in progress). Read next run.

## Lessons
- **A tube over the whole parameter window replaces comparison lemmas** (PROMPT working note): the plan's Lemma D (cooperative dip comparison) and an a-priori q-bound were the hard part of the reversed branch; one certified chain started from a ball of radius 2·10⁻¹⁰ around the window centre (48 cells, < 2 min) gives every trajectory of the window inside the clamps on [0, 3/2] and a good end state, after which the attached-branch energy argument applies unchanged. Events must also be robust (strict at their time): a threshold on q added to an event to bound the neither-point fails at a tangency; a tube does not.
- **Auditor role can carry a whole result:** under a live LOCK, scratch Lean in `runs/<run>/lean/` (build checks by local untracked copies under `Work/`, never committed from there) plus blind restatements and a referee took both theorems to "move to Work" before the LOCK was released; the freeze and proof commits then took 6 minutes.
