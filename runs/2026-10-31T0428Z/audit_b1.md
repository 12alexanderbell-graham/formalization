# Fidelity audit (annex XL): B1 headlines, run 2026-10-31T0428Z

Headlines: `Checked.Cosmography.B1.lumDistFlat_flatLCDM`, `cubic_misses_z3`, `cubic_misses_z7`, `cubic_shape_miss`.
Definitions: `lusA2`, `lusA3` (PRINTED, Lusso et al. 2019 Eq. (8), crop `runs/2026-10-30T1628Z/screen/L19_p3_eq8_a2_a3.png`), `logPolyDL3` (PRINTED, Risaliti & Lusso 2019 Methods p. 15, crop `.../RL19_p15_methods_a2_a3.png`). Pinned definitions used: `lumDistFlat`, `hubble`, `redshift`.

| Check | Result |
|---|---|
| Frozen before proof | commit 23eb28e; statements byte-identical in Work proof (2040ba0) and in Checked (diff shows only `sorry` removed) |
| Blind restatement | subagent from informal claims only, `Work/Cosmography/B1Blind.lean`; **closed in Lean** (`Work/Cosmography/B1Audit.lean`: every blind statement derived from the program's theorems; the blind shape claim is weaker in hypotheses — no `t₇ ≤ t₃` — and is still derived, the order following from `a` increasing in the model) |
| Not vacuous | `Checked.Cosmography.B1.exists_flatLCDM_on`: exact solution `a = sinh(3t/2)^{2/3}`, Ω = 1/5, H₀ = √5/2, sources at z = 3 and z = 7 on one interval; `Checked.Trust.NV.*` witnesses for all four (CI-checked obligations) |
| Not trivial / bites | thresholds sit below the true minima (referee, mpmath: 0.115, 0.368, 0.245 mag) and the statements are false for thresholds above them (e.g. z = 3 with 0.12 fails at Ω ≈ 0.35); the bridge is an equality with the pinned `lumDistFlat` |
| Junk values | `logb` of a negative ratio would take an absolute value: excluded by the proved positivity conjunct (polynomial > 0) and `d_L > 0`; `√` arguments are positive on the domain (proved); `H₀ > 0` is a hypothesis (with `H₀ = 0` the bridge is false: referee item 1) |
| Types, quantifiers | Ω ∈ [1/5, 2/5] universally; every model satisfying the Friedmann law on the closed interval; `c = 1` conventions as `Checked.Cosmography` |
| Classification | no Translation or Underspecified error found. Referee corrections were to the module docstring only (normalisation wording, RL19 also drops Ω² → Ω, z = 7 is an extrapolation of the cubic), applied in Checked |
| Referee | `referee_b1.md`: STANDS-WITH-CORRECTIONS (statements true and faithful; prior art numerical only) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` only (local `#print axioms`; CI audit) |

Protocol note: the referee consulted ar5iv HTML pages of two arXiv papers for prior art (PROMPT forbids ar5iv for formula transcription; no formula from it was used). Briefs now say so (PROMPT working note).

Weakest unchecked step: `lusA2`, `lusA3` are PRINTED (screen 1628Z read them from the typeset crop and re-derived them with sympy; referee re-derived them independently) but have no machine-checked tie to the Taylor expansion of d_L; and the claim's relevance to the RL19 tension (fit-level statement) is prose.
