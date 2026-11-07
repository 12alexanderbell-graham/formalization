# Run 2026-11-07T2028Z (scheduled)

**THE RESULT:** parts 2 and 5 moved: a new shooting constant in fluid mechanics — Hiemenz stagnation-point flow (Falkner–Skan β = 1), wall shear f''(0) ∈ (1.2325876568, 1.2325876569): both shooting events and the existence of a boundary-value solution between them PROVED in Work, blind restatement closed, referee STANDS-WITH-CORRECTIONS. Not yet in Checked.

**What can a scientist now trust without checking it themselves, that they could not before?** That the Hiemenz boundary-value problem has a solution whose wall shear lies in (1.2325876568, 1.2325876569), and that every solution started from either end of that window leaves the physical branch (overshoots or turns back) by η = 7.5 — machine-checked from the equation, with a blind restatement closed against it (in the Work library; the strict Checked library and its second kernel come with the promotion). Not yet: that it is *the* solution (uniqueness is cited, not proved).

**Measure:** certified answers whose digits are in print only as floating point +1 (10 digits; ≤ 8 printed); Work headlines with a closed blind restatement +3; screen → freeze → three Work proofs ≈ 45 min.

**Weakest unchecked step:** uniqueness of the boundary-value solution (Coppel 1960; the referee read only secondary surveys), so the theorem places *a* solution in the window; and the statement literals have no blind literal reading yet (needed for promotion).

## What we did
- CI read: 0b9051c (branch run 42401643361) green on every job: Townes trio and Blasius pair PROVED.
- Float study (`scripts/hz_fast.py`) and exact-rational generator (`scripts/gen_hiemenz_w.py`) before freezing: 60 cells per end, radius 7·10⁻¹⁴, event margins ≥ 2.9·10⁻¹⁰.
- Freeze 41967e1 (`Work/Hiemenz/Hiemenz.lean`, three statements with `sorry`).
- In one wave: fork for the generic cell module (`HCellW.lean`, ≈ 7 min), blind restater (Sonnet, `blind/`), referee + prior art (`referee_hiemenz.md`).
- Under/over proved (98f2211): emitter `scripts/emit_hiemenz_w.py`, `HUData`/`HOData` (kernel evaluation, ≈ 70 s each); blind under/over closed (f22426b).
- Existence (4d99d89): three forks in one message (`HExFlow`, `HCellWC` + `HUDataC`/`HODataC`, `HExLimit`), assembly `HExAssemble.lean` by hand; blind `exists_closed`.
- Records: STATE (Hiemenz section, environment, daily review, exact next step: promotion), BLUEPRINT, CHANGELOG, TARGETS part 2, PROMPT working note (shooting constants without a symmetry).

## CI
- Freeze 41967e1 (42411760912): work job **green** (20:44–21:33Z, full Work rebuild 49 min; Hiemenz.lean with `sorry`, closed audits). 98f2211, f22426b, 4d99d89: replaced while pending by later pushes (job-level coalescing). Records b0ee28e (42415096502) and this note: judge the Hiemenz proofs; read next run.

## Start
- 20:28Z: pre-cloned shallow checkout detached with a stale local main; `git checkout -B main origin/main` = f995f92. add_repo not exposed. No LOCK; taken in b622fa0.
