# Run 2026-11-11T2228Z (scheduled)

**THE RESULT:** part 1 (trust system, T2b hypothesis necessity): **the wall condition f(0) = 0 is machine-checked NEEDED in 24 boundary-value headlines (34 hypotheses)** — Blasius, Falkner–Skan β = 0, and the Hiemenz, Homann, β = 1/2, 1/5, 1/10 window/equality headlines in the bound-free, bounded and monotone classes — by suction solutions certified with the program's own shooting stacks, now generic in the wall value f(0).

**What a scientist can now trust without checking:** that none of these 24 theorems carries a decorative wall condition: for each, Lean exhibits a genuine solution of the same equation with f(0) ≠ 0 meeting every other hypothesis and violating the conclusion; the ten bounded-class headlines and the Blasius / β = 0 wall-shear headlines are now fully classified (every hypothesis needed or redundant).

**Weakest unchecked step:** the far-field condition f' → 1 of the bound-free (`_limit_`) and monotone headlines stays open (a witness needs a global solution with f' unbounded); the suction windows are author-chosen (1.5–1.6 etc.), certified, not read blind (they are witnesses, not claims).

## Start
- 22:27Z. Pre-cloned checkout detached with an unrelated stale local `main`; `git fetch` + `git checkout -B main origin/main` = e6c3f47.
- LOCK held by run 2028Z (taken 21:24Z, heartbeat 22:10Z: alive) → auditor role (rule 48.4): this run writes only in this folder until the LOCK is released.
- Local Lean: elan installer accepted, `lake exe cache get` ok (≈ 3 min).
- Rotation: parts 1/3 due (2/5 at 1828Z); run 2028Z works on the bounded-class velocity bundles (part 1), so this run takes a disjoint part-1 family.

## Plan (bottleneck; what a yes/no changes)
- `Blasius.blasius_wall_shear | 4` and `FalknerSkan.fs_zero_wall_shear | 4` (`f 0 = 0`) are the last open hypotheses of both headlines. Witness idea: suction. From the wall state (f, p, q) = (1, 0, 1) the Blasius system has a global solution with f ≥ 1, q > 0 decreasing and p + 2q non-increasing (its derivative is q(1 − f) ≤ 0), so p increases to a limit α ∈ (0, 2]; scaling by c = √α gives p → 1, f(0) = 1/c ≠ 0 and wall shear α^(−3/2) ≥ 2^(−3/2) > 0.3320574, outside the Blasius window; the β = 0 form by the √2 scaling has wall shear √2·α^(−3/2) ≥ 1/2 > 0.4696, outside its window.
- Yes: both headlines fully classified (two witnesses, no new certificate). No: record which step resists.

## Work
- 22:55Z. **Yes, first compile.** `lean/BlasiusSuction.lean` (namespace `Checked.Trust.NCH`, scratch; imports built Checked modules; standard axioms only: propext, Classical.choice, Quot.sound):
  - `exists_flow1`: global solution of the clamped Blasius field `BExBase.vF` from (1, 0, 1) (Picard–Lindelöf on [0, n + 1], glued by `BExFlow.agree`; copy of `BExFlow.exists_flow` with the start changed).
  - `suction`: along it every clamp is inactive (q > 0 by backward uniqueness, p ≥ 0, f ≥ 1, q ≤ 1, f ≤ 4t + 1; p + 2q non-increasing since its derivative is q(1 − f) ≤ 0, so p ≤ 2) and p increases to a limit α with 0 < α ≤ 2.
  - `suction_profile`: scaled by c = √α (`BTail.scale`): a solution of the Blasius system on [0, ∞) with f(0) = 1/c, p(0) = 0, p → 1, q(0) = 1/c³, c² ≤ 2.
  - `blasius_wall_shear_h4 : necessity% Checked.Blasius.blasius_wall_shear 4` (q(0) = 1/c³ > 100/283 > 0.3320573362152) and `fs_zero_wall_shear_h4 : necessity% Checked.FalknerSkan.fs_zero_wall_shear 4` (`FSScale.scale` with factor √2/2: wall shear √2/c³ > 0.4696).
- Effect once integrated (needs the LOCK, then a `Checked/Trust/` module, baseline lines `Blasius.blasius_wall_shear | 4` and `FalknerSkan.fs_zero_wall_shear | 4` removed, StatementDeps): both headlines fully classified (+2).

- 22:52Z. **LOCK released by run 2028Z (53d4d4c); LOCK taken 22:53Z (647b974).**
- 22:45–23:00Z. **Suction boundary-value problems for every positive-β stack** (scripts in `scripts/`): `gen_hiemenz_wc_s.py` / `gen_k_wc_s.py` (copies of the clamped cell generators with the start g(0) = S from `FS_S`), `emit_hiemenz_wc_s.py` (Checked cell modules), `port_suction_all.py` (ports `<P>ExFlow`, `<P>ExLimit`, `<P>ExAssemble` of the Hiemenz, Homann, K = 5, K = 10 stacks to a wall value a0 by asserted replacements; `no_eventS` also exports 0 ≤ p < 1, q > 0). Rows: Hiemenz a0 = 1/2, shooting interval (1.5, 1.6), 16 + 16 cells; Homann a0 = 1/10, (1.4, 1.5), 32 + 32; K = 5 a0 = 1/20, (1.65, 1.75), 32 + 32; K = 10 a0 = 1/100, (1.89, 1.95), 48 + 48 (the clamps |q| < 2 force small suction for large K; float shooting `runs/2026-11-11T2228Z/data/`). Every generated and ported module compiled first time (one `refine` arity fix in the Hiemenz assemble port).
- Witnesses: `gen_witness.py` emits 25 (Homann form; β = 1/2, 1/5, 1/10 via `FSScale.scale` with c = √K); 7 Hiemenz by hand; all compiled first time. Promoted by `promote_suction.py`: `Checked/Suction/` (20 modules, no headline), `Checked/Trust/NecessityI.lean` (Blasius, β = 0), `NecessityJ.lean` (Hiemenz), `NecessityK.lean` (Homann and the three rows).
- 23:42Z. First full `lake build Checked` OOM-killed (B1L19 curved certificates beside TFQData, exit 137); rebuilt with those certificate modules first, serially: **full build green** (00:15Z).
- **Local checks:** `TRUST_RELOCK=1 StatementDeps`: NEEDED 309 → 343, open 487 → 453, **fully classified 38 → 50 of 154**; Claims unchanged (240); `local_frozen_step.py --trust 89d717f`: 19/20 green, `check_necessity --base` failed reading the base map (`conjuncts of`, a label renamed in 12d6cdc) — **repaired** (LEDGER; base read with the legacy label as `parts of`), then green.
- CI: one combined push (integration + repair + records + LOCK removal); read by run ID next run.

## Next step
STATE item 0d: MonotoneWindow 5 (p(0) = 0 dropped: start (0, c, α), same route) and 2; Duffing/MM/Robertson initial values by a parametrised start (0c).
