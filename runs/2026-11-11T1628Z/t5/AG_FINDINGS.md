# Blind red team AG — first reading (run 2026-11-11T1628Z, auditor role; NOT yet judged with a build)

Red team: Sonnet, brief `briefAG.md` (committed locally before the round, f90a7dd; same text here), snapshot = run
1628Z's parts version (c6fab97: run 1428Z's wip patch with conjuncts replaced by monotone-position *parts*). Output
copied verbatim to `redteamAG/` (d01–d06 + REPORT.md). Status: defects **not yet compiled or judged** (the build
here is still running); reading below is by inspection of the code on main (af33783, run 1428Z's version).

| d | weakness | applies to main (af33783)? | proposed repair |
|---|---|---|---|
| d01 | hypothesis `∃ Ω, IsFlatLCDM Ω a t₀`: `necShape` flags `bundled i` only when the unfolded head is `And` | yes (pre-existing since run 0428Z; independent of conjuncts/parts) | flag `bundled i` whenever the hypothesis has ≥ 2 parts (walk through ∃/∀/∀ᶠ/→-conclusion), not only a top-level `∧` |
| d02 | same with `∀ s, s = t₀ → IsFlatLCDM Ω a s` | yes (pre-existing) | same |
| d03 | `c : NNReal` assumes `0 ≤ c` silently: `subtype` looks only for `Subtype`/`Set.Elem` as written | yes (pre-existing) | `subtype` after unfolding the binder type's head constant (`whnfD`/`unfoldDefinition?` to a `Subtype`) |
| d04 | `partsWalk` fuel 64: a 67-conjunct right-nested hypothesis leaves an unsplit 3-conjunct tail as one "part" and `bundled 1` closes | **yes, same hole in `hypConjuncts` (fuel 32 returns the unsplit rest as one conjunct)** unless `hidesAnd` also inspects that conjunct | out of fuel ⇒ error (no obligation, `bundled i` stays), never a silent atom |
| d05 | `∃!` (Mathlib, not unfolded) hides existence + uniqueness as one atom | yes (pre-existing) | unfold `ExistsUnique` in the walk (and in `necShape`) |
| d06 | `x ∈ Set.Ioi b` restates the conclusion `b < x`; `restated` compares after `whnfR` only | yes (pre-existing) | compare after unfolding `Membership.mem`/`Set.Ioi`… (`whnfD` on both sides, or `isDefEq` with default transparency) |

Measured consequence (by inspection): d01, d02, d05 are one family — any hypothesis whose head is not `∧` hides a bundle
from the shape layer; fixing it will ADD shape reasons to some existing headlines (the shape baseline must then be
allowed to gain reasons for headlines that exist unchanged at the base: a gained reason only lowers the fully-classified
tally, so the gain direction cannot mislead; new headlines stay blocked as now).

Next (this run, once a build is available): compile the six defects on main, judge with StatementDeps + check_necessity
(BEFORE column), implement the repairs above, judge again (AFTER, not blind: written after reading the report).
