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
