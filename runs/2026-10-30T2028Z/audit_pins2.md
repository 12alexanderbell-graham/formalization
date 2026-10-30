# Fidelity audit (annex XL): pins for redshift, cosmoCoeff, yred, omega0, curvK, lumDistFlat, comoving (run 2028Z)

Files: `Checked/Fidelity/RedshiftCoeffSpecs.lean`, `YOmegaKSpecs.lean`, `FlatPins.lean`.

| Check | Result |
|---|---|
| Frozen specs | `Work/Fidelity/BlindSpecsZC.lean` (commit 7c6bcb7), `Work/Fidelity/BlindSpecs3.lean` (f15af15), frozen before any proof about them. |
| Blindness | Both written by subagents told not to read `Checked/`, `Work/`, `runs/`, `*.md`. Interfaces (argument order, meaning) were given; definitions were not. |
| Verbatim | Checked structures are copied by script; field-by-field substring check against the frozen files passed (RedshiftSpecCore 14/17 fields, CosmoCoeffSpecCore 13/16 fields — omitted fields listed in each docstring, never used by the pins; YRedSpec, Omega0Spec, CurvKSpec complete). |
| Referee | `referee_specs2.md`: Redshift, CosmoCoeff, YRed STAND; Omega0, CurvK STAND-WITH-CORRECTIONS (docstring only: Ω₀ is the total density parameter; k = −Ω_k). Corrections applied in the module docstring of `YOmegaKSpecs.lean`. |
| Meets spec | `redshift_meets_core`, `cosmoCoeff_meets_core`, `yred_meets_spec`, `omega0_meets_spec`, `curvK_meets_spec` (every field proved, including anchors and near misses). |
| Pinning | `redshiftCore_pins` uses only the integral law (not the ratio law); `cosmoCoeffCore_pins` uses only the Taylor law plus uniqueness of Taylor coefficients (`poly_littleO_coeff_zero`), not the defining formula; `yRedSpec_pins`, `omega0Spec_pins`, `curvKSpec_pins` use the determining laws; `lumDistFlat_pins`, `comoving_pins` go through `lumDistSpec2_pins`. |
| Domains | Pins hold on: C¹ positive rays (z); a > 0, Cⁿ near t₀, ȧ ≠ 0 (C_n); a(t₀), a(t) > 0 (y); a₀ > 0, H₀ ≠ 0 (Ω₀, k); t ≤ t₀, a > 0 continuous (d_L flat, χ). Every headline using these definitions assumes at least this. |
| Junk values | No field asks for a value outside the physical domain (referee). |
| Axioms | propext, Classical.choice, Quot.sound only (local `#print axioms`). |
| Residual | Same-model authorship (spec writers, referee, prover). `comoving_pins` and `lumDistFlat_pins` pin relative to `LumDistSpec2`'s laws. |

Verdict: AUDITED.

## Addendum: `IsFlatCPL` (`Checked/Fidelity/FriedmannCPL.lean`)
- Blind `FriedmannCPL` frozen in f15af15, copied verbatim (diff of the def body: identical). Referee `referee_friedmannCPL.md`: STANDS (continuity sign, CPL rewrite, quantifiers, no junk loophole; sympy closed form).
- `isFlatCPL_iff_friedmannCPL` for every Ω, w₀, wₐ, a, t₀ (backward direction integrates the differential continuity equation on a ball and uses Darboux for the sign of H); `flatCPL_pins : (∀ …, P … ↔ FriedmannCPL …) → P = IsFlatCPL`. Axioms: standard three. AUDITED.

## Addendum: F(R) definitions (`Checked/Fidelity/FRSpecs.lean`)
- Blind `RicciFlatFLRWSpec`, `DustDensity`, `FRFirstEq`, `FRSecondEq` frozen in ff9272f, copied verbatim (block substring check passed; the blind file's unused `hubble` helper not copied). Referee `referee_FR.md`: STANDS (sympy re-derivation from the metric F(R) field equations, mapped to the review's convention R = −R_c, F(R) = −f(−R); GR limit; ΛCDM = R + 2Λ consistent with the review's (11.39)–(11.40)).
- `curv_meets_spec` (all fields), `ricciSpec_pins` (a > 0, twice differentiable), `rhoM_eq_dust` (`rfl`), `friedmannEq_iff_blind`, `masterEq_iff_blind` (every Ω, a, F, t₀, t, with R = curv a). `IsFRCosmo` reclassified COMPOSITE (fields: pinned definitions + the source's explicit assumptions F′(R₀) = 1, F⁽⁴⁾(R₀) = 0). Axioms: standard three. AUDITED.
- Referee's caution kept for downstream statements: the blind equations take R as a parameter; the program always instantiates R = curv a, and `IsFRCosmo` carries C⁵/C⁴ smoothness, so no `deriv^[n]` junk enters the headlines.
