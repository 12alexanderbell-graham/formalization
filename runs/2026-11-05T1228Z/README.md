# Run 2026-11-05T1228Z (scheduled)

**THE RESULT:** part 5 (breadth: chemistry) by rotation, and part 1 (rigorous computation of a published model): the certified-coexistence method now covers the third classic cubic equation, Peng–Robinson, and with it the question whether PR's own published κ(ω) correlation reproduces the acentric factor it is fed. At ω = 1 it does not: the equation's own ω is 0.942, proved for every critical point and every coexistence state, with existence.

**What can a scientist now trust without checking it themselves, that they could not before?** That the Peng–Robinson equation with Soave's α and the 1976 κ(ω) = 0.37464 + 1.54226ω − 0.26992ω², entered at ω = 1, has vapour pressure p_s/P_c = 0.0114 at 0.7 T_c and therefore acentric factor 0.942 (not 1) — at every critical point of the fluid, for every Maxwell coexistence state, and such a state exists (`Checked/Chemistry/PRAcentric.lean`, `pr_omega1_unique`, `pr_omega1_exists`; no floating point, no sign assumed for R or T_c). The statement uses only pinned definitions (`IsCriticalIsotherm`, `IsMaxwellCoexistence`) and the generic `cubicP`, `acentric`, `RoundsTo`; a blind restatement written from the claim in words is proved from it.

**Weakest unchecked step:** the transcription of the κ(ω) coefficients (0.37464, 1.54226, 0.26992) from the Peng–Robinson 1976 paper — taken from the program's knowledge and from the referee's independent sources (DWSIM, pychemqt documentation), not from a typeset crop; the claim is stated for those coefficients, so a misprint would change which correlation it is about, not its truth. Second: CI of the promotion (read next run).

**Kind of result (PROMPT note "Part 2 needs questions whose answer is not already in print"):** the qualitative effect is in print (Robinson & Peng 1978 replaced the 1976 correlation for ω > 0.491 because it makes heavy compounds too volatile); the exact figure 0.942 was not located in print by the referee (`referee_pr.md`); new is the certified value with uniqueness and existence.

## Start
- 12:28Z: no LOCK; add_repo not exposed; pre-cloned detached HEAD, stale local main (Oct 30, shallow) reset to origin/main. LOCK + stub cfbe7ca.
- Local Lean: elan installer accepted, Mathlib cache.
- Bottleneck (part rotation: part 5 idle since 0228Z, four runs): does the certified-coexistence route survive an equation whose primitive is not rational-logarithmic in x (PR: ∫ dx/(x²+2x−1) brings logs of x + 1 ± √2)? Yes = the whole classic cubic family (vdW, RK, PR; SRK is the RK form) is covered by one generator pattern; no = PR needs a different route. The question chosen: PR's own κ(ω) at ω = 1 (floating point of run 2026-11-04T1828Z: shortfall ≈ 0.058).

## Work
1. **Freeze** 3c53e40 (`Work/Chemistry/PRAcentric.lean`, statements before proof work; minimal hypotheses: no `0 < R`, no `0 < T_c`). Floating point `scripts/pr_float.py`.
2. **Blind restatement** (Sonnet, from the claim in words, no access to the frozen file): `Work/Chemistry/PRAcentricBlind.lean`, notes `blind/notes_pr.md`. **Referee** (in parallel): `referee_pr.md`, STANDS-WITH-CORRECTIONS; two independent numerical routes (equal fugacity on the Z-cubic; dimensional equal areas) agree to 40 digits, p_s/P_c = 0.0114180538, ω = 0.9424079165; unique Maxwell state; prior art as above; corrections to the prose only (applied in the Checked module doc).
3. **Uniqueness** (8cbdd87): `scripts/gen_pr.py` (exact-rational certificates: θ interval of width 1.3·10⁻⁸, √2 and √0.7 enclosed, five sign covers of q and q′, four certified logarithms, two area certificates monotone in √2), `emit_pr.py` (the RK reduced module adapted: new g, ψ, q, dq, piece lemmas; generic root-structure and window proofs copied with constants replaced), `emit_pr_core.py` (θ_c, Soave factor, p_s/P_c = π_s·α·D²/N, ω by certified logs). First full compile of the 720-line generated module had 3 errors, all in hand-written lemmas (derivative bookkeeping); the generated certificates passed first time.
4. **Existence** (c677cb0): `emit_pr_exists.py` from `RKExists` (window maxima continuous in π, IVT), brackets `gen_pr_exists.py`.
5. **Audit**: `Work/Chemistry/PRAcentricAudit.lean` proves the three blind theorems from the frozen headlines (`closed_pr_acentric` has exactly the type of `Blind.PRAcentric.pr_acentric`, checked by `rfl` on the types); registered in `scripts/trust/audits.txt`.
6. **Promotion** (`scripts/promote_pr.py`): the four modules copied to `Checked/Chemistry/` (namespaces, specific Mathlib imports, module docs for the prose rules; statements and proofs unchanged); headlines registered, NV witnesses (`pr_crit_witness`: the PR critical point of R = b = a = 1), relock, TRUST_MAP, CLAIMS.md, packet.

## CI
- Read at start/end: 1783fe6 (Moresco promotion) 42022359372 **green on every job** (checked build 78 min, nanoda 19.6 min) ⇒ the ten Moresco headlines are PROVED; 70d33e3 42023102604 checked job lost 2 min into nanoda (no log; same Checked tree as 1783fe6: runner loss); 9927362 42023945496 green.
- This run: LOCK cfbe7ca 42027481780, freeze 3c53e40 42028443863, uniqueness 8cbdd87 42032131290, existence + audit c677cb0 42032947506 — **all green** (work job: PR Work proofs and the blind closure compile in CI). Promotion 6a32db1 42039795953 and the records commit: in progress at the close, read next run.

## Measurement
| | before | after |
|---|---|---|
| headlines | 163 | 165 |
| classic cubic equations with certified coexistence | vdW, RK | vdW, RK, PR |
| certified self-consistency checks of a published EOS correlation | 0 | 1 |
