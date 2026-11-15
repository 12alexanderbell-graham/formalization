# Run 2026-11-15T1828Z (scheduled)

**THE RESULT:** parts 2/5 (rotation) — the multiplicity of radial solutions of the Gelfand problem Δu + λeᵘ = 0 in the unit ball of ℝ³ (Joseph–Lundgren, dimension 3) is now one Checked headline (`Checked.Math.GelfandPDEManyCentre.gelfand_pde_radial_many_centre`), derived from existing Checked headlines with no new certificates. The first freeze of the claim fell to the referee: its distinctness compared functions outside the ball, so it said nothing beyond existence. The corrected statement was frozen, proved and audited, then promoted.

**What can a scientist now trust without checking it themselves, that they could not before?** That the Gelfand (thermal-explosion) problem in the unit ball of ℝ³ with u = 0 on the sphere has, among its radial classical solutions, a sequence with pairwise distinct values at the centre for λ = 2; for every N, N such solutions for every λ close enough to 2; and two such solutions for every λ in [2, 3.321992118). The program's PDE headlines previously gave existence of one solution for λ up to 3.321992118 and none above 3.321992119.

**Measure:** certified multiplicity statements for the Gelfand PDE: 0 → 1 (Checked; PROVED once CI is green on every job). Fidelity audit: 1 frozen formalization caught as trivially satisfiable before it was promoted (Translation error).

**Weakest unchecked step:** CI has not yet judged this run's promotion. The prior-art line (Joseph–Lundgren 1973) was read only through a summarising web fetch (UNVERIFIED). The exact number of solutions (for example exactly one at the critical parameter) is not claimed: it needs uniqueness for the singular initial-value problem, which is not formalised.

## Start
- 18:28Z. add_repo not exposed; pre-cloned checkout detached at 4bad0a8 with a stale local main (Nov 9, its commits on origin/wip/*); `git checkout -B main origin/main` at 4bad0a8. No LOCK → taken (025498c).
- Local Lean: elan (authorized) + `lake exe cache get`; `checked-build` of 43721065108 (b7d5a44) downloaded to the scratchpad (≈ 2 min) and restored with DELETE_ZIP=1; `lake build Checked` replayed.
- CI at start: 43731774283 (878502b) in progress; 43745518217 (82ebb61) pending.

## Bottleneck (and what a yes/no changes)
- Rotation: parts 2/5 (STATE 1f: other functionals of the isothermal sphere). The Gelfand PDE had existence (λ ≤ 3.321992118) and non-existence (λ > 3.321992119) but not the classical multiplicity. Question: does `gelfand_extrema` plus the radial construction already give the multiplicity with no certificates? Yes → a classical PDE theorem certified in one run; no → it needs ODE uniqueness or new chains.

## What we did
1. Freeze `Work/Math/GelfandPDEMany.lean` (4195e32): infinitely many radial solutions at λ = 2 (an injective sequence), at least N for |λ − 2| < ε(N), at least two for 2 ≤ λ < 3.321992118.
2. One message: blind restater (Sonnet), referee (Opus), proof fork. The fork proved the freeze in ≈ 6 min (`Work/Math/GelfandPDEManyMain.lean`; 8a77532). **Referee: FALLS** (`referee/REPORT.md`): `Function.Injective u` and `u ≠ v` compare functions on all of ℝ³, but every condition of the solution class reads only the closed ball, so one solution changed outside the ball is an "injective sequence"; the proved statement reduces to existence. The blind restater had independently compared solutions only on the closed ball.
3. Corrected freeze `Work/Math/GelfandPDEManyCentre.lean` (0c57528): the solutions must differ at the centre of the ball. Proof d900e3a (`main_centre`, `ne_of_centre`; axioms standard). Blind restatement copied verbatim to `Work/Math/GelfandPDEManyBlind.lean` and closed first time in `Work/Math/GelfandPDEManyBlindClosed.lean` (5bd78e6).
4. Blind literal reader (Sonnet; brief e6e124f, reading d2f08cf): D = 3, C = 0, S = 2 from the explicit singular solution −2 log r, L = 3.321992118 from its own 30- and 45-digit computation of λ* = 3.32199211833982…
5. Promotion by `scripts/promote_gelfand_many.py` (statement byte-identical up to the namespace), `Checked/Trust/SecondReadingGelfandMany.lean`, NV witness, headline and literal-reading registries, relock, TRUST_MAP, CLAIMS.

## Next
- STATE 1g: CI read (the final push of this run → `gelfand_pde_radial_many_centre`); then part 1 by rotation.
