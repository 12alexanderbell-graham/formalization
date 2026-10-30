# Run 2026-10-30T2028Z (scheduled)

Environment: repo pre-cloned (add_repo not exposed, not needed); local main fast-forwarded; pushes verified (remote head = local each time). Local Lean via elan + `lake exe cache get` (~4 min). CI read by ID (STATE). Governance: PROMPT, core, STATE, CHANGELOG read. Previous run's CI (41115616706, 41116631712) green.

**WHAT CAN A SCIENTIST NOW TRUST WITHOUT CHECKING IT THEMSELVES?** For 63 of the 82 physics headline theorems (F0–F11), every program-written physics definition the statement uses is pinned: a Lean theorem says any function obeying blind-written textbook laws equals the program's definition on the physical domain. At the start of the run this held for at most 15 of 88 headlines. And which definitions each headline rests on is now computed by machine (CI), not listed by hand.

**WEAKEST UNCHECKED STEP NOW:** for the 19 remaining physics headlines, their unpinned definitions: the metric F(R) field equations (`FRCosmo.curv`, `rhoM`, `FriedmannEq`, `MasterEq`, `IsFRCosmo`; F9, F10), the CPL model `IsFlatCPL` (F2), the deceleration distance `dQFlat` (F5). For all headlines: the textbook laws themselves (blind subagents of the same model, refereed, anchored by closed forms), and transcriptions of printed formulas (T3).

**BOTTLENECK AND WHY:** STATE's next step was to close the `FlatLCDMSpec` gaps. Doing so exposed the real question: "4 of 5 central definitions pinned" was a hand-picked list. Which definitions do the headlines actually rest on? A machine answer (trust map) showed `cosmoCoeff` (67 headlines) and `redshift` (58) were unpinned: the run's main block went there. Yes = the trust metric moves on what the findings actually use.

**WHAT WE DID:**
1. `IsFlatLCDM` pinned by a first-principles formulation: a subagent, reading no repository Lean, wrote `FriedmannLCDM` (flat Friedmann + dust continuity + Λ). Referee STANDS. `isFlatLCDM_iff_friedmann` (every Ω, a, t₀; Darboux's theorem gives the sign of H near t₀), `FlatLCDMSpec2`, `flatLCDMSpec2_pins`. Promotion CI 41125393349 green.
2. Trust map: `scripts/trust/StatementDeps.lean` walks each headline's statement through the definitions it uses (stopping at pinned ones), classifies them (`def_kinds.txt`: PHYSICS / PRINTED / CLAIM / FORMULA / …), writes `TRUST_MAP.md`; CI step (registry errors block). Negative control branch `control/bad-pin-registry` (a pin claiming `decelSpec_pins` pins `redshift`): rejected locally; CI in STATE.
3. Blind specs for `redshift` and `cosmoCoeff`, then for `yred`, `Ω₀`, `k`, flat CPL: frozen before proofs (7c6bcb7, f15af15). Proved the definitions meet them and pinned each through its general law only: z by the integrated wavelength-stretching law 1+z = exp∫H; Cₙ by the cosmographic Taylor law (new lemma: uniqueness of Taylor coefficients); y, Ω₀, k by their determining laws. Flat d_L and χ pinned through `LumDistSpec2`. Referee: all laws STAND (Ω₀ = total density parameter, k = −Ω_k noted in docs).

**RESULT (metric):** physics headlines resting only on pinned definitions: 63/82 (start ≤ 15/88). Pinned definitions: 12 (start 4). Blind kill rate unchanged 30/30.

**WHAT COULD STILL BE WRONG:** same-model authorship of specs, referee and proofs (correlated misconceptions); the dependency walk counts only `Checked`-namespace definitions (Mathlib's `deriv`, `iteratedDeriv`, `∫` are trusted as Mathlib); `def_kinds.txt` classification is by hand (a physics definition misfiled as FORMULA would hide a gap — 43 FORMULA entries, all explicit polynomial/rational expressions in parameters).

**NEXT:** STATE.
