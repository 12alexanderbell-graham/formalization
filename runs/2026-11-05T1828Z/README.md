# Run 2026-11-05T1828Z (scheduled)

**THE RESULT:** part 2 (new science through the system) by rotation (parts 1/2 idle since 1028Z), with part 5 (chemistry): the question run 1228Z left open — does the published *fix* of the Peng–Robinson κ(ω) correlation (Robinson & Peng 1978) reproduce the acentric factor it is fed? — answered with a certified theorem (yes at ω = 1: 1.000), and the same machinery turned on a widely used software implementation of that fix (Cantera), whose coded coefficients do not (0.998; candidate C31).

**What can a scientist now trust without checking it themselves, that they could not before?** That the Peng–Robinson equation with Soave's α and the revised (1978) κ(ω) = 0.379642 + 1.48503ω − 0.164423ω² + 0.016666ω³, entered at ω = 1, has p_s/P_c = 0.0100 at 0.7 T_c and acentric factor 1.000 — at every critical point, for every Maxwell coexistence state, and such a state exists (`Checked/Chemistry/PR78Acentric.lean`, `pr78_omega1_unique`, `pr78_omega1_exists`; on pinned `IsCriticalIsotherm`, `IsMaxwellCoexistence`; no sign assumed for R or T_c). Together with run 1228Z's 0.942 for the 1976 correlation, the size of the defect the 1978 revision repaired is now certified at both ends. And that the coefficients Cantera codes for the same correlation give 0.998 instead (Work, PROVED; candidate C31).

**Weakest unchecked step:** the transcription of the 1978 coefficients. The primary report (GPA RR-28) was not reachable; the coefficients agree across thermo, pychemqt, DWSIM and four arXiv papers (referee), and they are the only variant of the three found that is self-consistent (to 10⁻⁴ over ω ∈ [0.6, 1.5], floating point) — a mechanical argument, not a typeset reading. The claim is stated for these coefficients, so a different original would change which correlation it is about, not its truth.

**Kind of result (PROMPT note "Part 2 needs questions whose answer is not already in print"):** qualitative answer in print (the revision fits heavy-compound vapour pressures better: Robinson & Peng 1978; ACS Omega 9 (2024) 50385), exact figure not located (referee); the referee notes that near self-consistency is expected by construction. New: the certified value with uniqueness and existence; and, unplanned, a discrepancy in Cantera's implementation (C31), which no source we found reports.

## Start
- 18:28Z: no LOCK; add_repo not exposed; pre-cloned checkout on main = origin/main (2f294cd). LOCK + stub 9c02ded.
- Local Lean: elan installer accepted, Mathlib cache.
- Bottleneck: part rotation (parts 1/2 next). Candidates in STATE: PR 1978 κ at ω = 1 (one constant away from run 1228Z's generators), four-decimal Moresco minimum, other published fits. Chosen: PR 1978 — a yes certifies that the published repair works (and makes the 1228Z result a measured defect rather than an out-of-range evaluation); a no would be a finding against a correlation in every process simulator.

## Work
1. **Floating point** `scripts/pr78_float.py`: ω_out = 1.0000888 (1976: 0.9424); across ω ∈ {0.5, 1, 1.5}: PR78 within 10⁻⁴, PR76 0.496, 0.942, 1.310.
2. **Freeze** 7bcfeb8 (`Work/Chemistry/PR78Acentric.lean`): the 1228Z statements with κ(1) written out as the 1978 cubic, p_s/P_c = 0.0100 (4 d.p.), ω = 1.000 (3 d.p.).
3. **Blind restatement** (Sonnet, claim in words; `blind/PR78AcentricBlind.lean`, notes) and **referee** (`referee_pr78.md`, STANDS-WITH-CORRECTIONS: two routes to 44 digits, p_s/P_c = 0.0099979544…, ω = 1.0000888…; binding margin 9.5·10⁻⁶ in p_s/P_c; unique Maxwell state; coefficients confirmed in six sources; **Cantera's code and header differ**; prior art as above) launched in one message.
4. **Proof** 529cd99: run 1228Z's generators copied and parametrised (`scripts/gen_pr78.py`, `emit_pr78*.py`): κ = 1716915/10⁶, θ interval width 1.3·10⁻⁸, reduced-pressure window [8.0700, 8.0735]·10⁻⁵, gas root ≈ 887 (existence bracket 1000), liquid bracket 6/5. **All four generated modules compiled first time** (≈ 3 min). Axioms standard. Statements byte-identical to the freeze.
5. **Audit** (same commit): `Work/Chemistry/PR78AcentricAudit.lean` proves both blind theorems from the frozen headlines; types matched by `rfl`.
6. **Cantera variant (C31)**: second fetch of Cantera main (`src/thermo/PengRobinson.cpp`: 0.374642 + 1.487503ω − 0.164423ω² + 0.016666ω³; header: 0.379642 + 1.487503ω − … + 0.016667ω³). Floating point `scripts/cantera_variant_float.py`: consensus self-consistent to 10⁻⁴ on [0.6, 1.5]; Cantera code 1–3·10⁻³ low; header 1–4·10⁻³ high. Frozen ecf67d2, proved db8d795 (`Work/Chemistry/PRCanteraAcentric.lean`: ω = 0.998, p_s/P_c = 0.010, every critical point and coexistence state, existence; generators `scripts/cantera/`). Work only (candidate, not promoted).
7. **Promotion** 414e080 (`scripts/promote_pr78.py`): `Checked/Chemistry/PR78{Reduced,Core,Exists,Acentric}.lean` (statements and proofs unchanged; headline docstrings: "the Robinson–Peng 1978 κ(ω)" → "the revised (1978) κ(ω) correlation" for check_prose rule 9; module docs carry the referee's corrections, including the Cantera warning). Headlines registered, NV witnesses, relock (new entries only), audits.txt +7, TRUST_MAP, CLAIMS.md, packet. Local: full `lake build Checked` green (after a rerun: a parallel Work build had killed MMCerts, exit 137), StatementDeps 167/167 on pinned definitions, NV 108/108, check_prose 0 new, every `--base` check vs db8d795 green.

## CI
- Read: 52459ff (merged round-K rules) 42079443594 **green**; 2f294cd (1628Z records) 42079627838 **green**; freeze 7bcfeb8 42085085012 **green**.
- 9c02ded, 529cd99 (PR78 proofs + audit), ecf67d2, db8d795 (PRCantera), heartbeat 85ab963, promotion 414e080 and the records commit: in progress at the close, read next run.

## Measurement
| | before | after |
|---|---|---|
| headlines | 165 | 167 |
| certified self-consistency checks of published EOS correlations | 1 (PR 1976: fails) | 2 (PR 1978: holds) |
| software implementations of a published correlation checked against it | 0 | 1 (Cantera: differs; Work) |
| generated certificate modules that compiled at the first attempt, new κ | — | 8/8 (two variants) |

## Next step
See STATE.md "Exact next step".
