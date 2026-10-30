# TRUSTED DEFINITIONS

**Machine-checked fidelity (trust track T1, run 1828Z).** The prose rows below are being replaced by Lean specs in `Checked/Fidelity/` (benchmarks in `Work/Fidelity/`) (`python3 scripts/fidelity_killrate.py` prints the status):

| Definition | Spec | Pinned? (spec ⇒ equal to the definition on the physical domain) |
|---|---|---|
| `BambaK.lumDist` | `LumDistSpec2` (anchors + Etherington d_L = (1+z)²d_A) | yes, `lumDistSpec2_pins` (every K, t ≤ t₀, a > 0 continuous on [t, t₀]) |
| `BambaA.angDist` | `AngDistSpec` | yes, `Checked.Fidelity.angDistSpec_pins` |
| `hubble` | `HubbleSpec` | yes, `hubbleSpec_pins` (a > 0, differentiable at t) |
| `decel` | `DecelSpec` | yes, `Checked.Fidelity.decelSpec_pins` (a > 0, twice differentiable, ȧ ≠ 0) |
| `Aviles.IsFlatLCDM` | `FlatLCDMSpec2` (anchors + blind Friedmann law `FriedmannLCDM`) | yes, `flatLCDMSpec2_pins` (P = IsFlatLCDM everywhere); `isFlatLCDM_iff_friedmann` |
| `redshift` | `RedshiftSpecCore` (blind, verbatim core) | yes, `redshiftCore_pins` (a > 0, C¹ on the ray) |
| `Aviles.cosmoCoeff` | `CosmoCoeffSpecCore` (blind, verbatim core) | yes, `cosmoCoeffCore_pins` (a > 0, Cⁿ near t₀, ȧ ≠ 0) |
| `BambaY.yred` | `YRedSpec` (blind) | yes, `yRedSpec_pins` (a(t₀), a(t) > 0) |
| `BambaK.omega0` | `Omega0Spec` (blind; total Ω₀) | yes, `omega0Spec_pins` (a₀ > 0, H₀ ≠ 0) |
| `BambaZ.curvK` | `CurvKSpec` (blind; k = −Ω_k) | yes, `curvKSpec_pins` (a₀ > 0, H₀ ≠ 0) |
| `BambaY.lumDistFlat`, `BambaY.comoving` | via `LumDistSpec2` | yes, `lumDistFlat_pins`, `comoving_pins` |

Which definitions each headline rests on, and which are still unpinned: `TRUST_MAP.md` (generated, CI).

Every `def`, `structure` or `class` the program writes: what it is meant to capture, and the tests showing it behaves correctly on known examples (annex 40.5). Prefer Mathlib and Physlib definitions.

| Definition | Meant to capture | Mirrors | Tests (Work/Cosmography/LookbackAudit.lean) |
|---|---|---|---|
| `Checked.Cosmography.hubble a t := deriv a t / a t` | Hubble parameter H = ȧ/a | Physlib `Cosmology.FLRW.hubbleConstant` (same formula) | `hubble_exp` (de Sitter: 1), `hubble_sq` (a = t², t=1: 2 = n/t) |
| `Checked.Cosmography.decel a t := -(deriv (deriv a) t * a t) / deriv a t ^ 2` | deceleration q = −äa/ȧ² | Physlib `decelerationParameter` (same formula) | `decel_exp` (−1), `decel_sq` (−1/2 = (1−n)/n); `decel_eq_blind` (= Visser's −(ä/a)H⁻²) |
| `Checked.Cosmography.redshift a t₀ t := a t₀ / a t - 1` | 1 + z = a(t₀)/a(t) | Physlib `FLRW.redshift` (same formula) | used in `lookback_deSitter` (z = e^{−t} − 1) |
| `Checked.Cosmography.Aviles.cosmoCoeff n a t := iteratedDeriv n a t / (a t * hubble a t ^ n)` | a⁽ⁿ⁾/(aHⁿ): j, s, l, m for n = 3…6 (Aviles et al. Eq. 3; Visser's jerk/snap) | none in Physlib | `l0_eds` = 35/2, `m0_eds` = −455/4 (a = t^{2/3}, direct Pochhammer computation); de Sitter `exp`: l₀ = m₀ = 1 (AvilesAudit) |
| `Checked.Cosmography.Aviles.IsFlatLCDM Ω a t₀` | H = H₀√(Ω(1+z)³ + 1 − Ω) near t₀, H₀ = H(t₀) > 0, a > 0 and differentiable near t₀ | Aviles et al. text before Eq. 15 | satisfied by EdS (Ω = 1), de Sitter (Ω = 0), sinh^{2/3} (Ω = sech²t₀); blind restater's `FlatLCDM` implies it (`BlindC2.toOurs`) |
| `Checked.Cosmography.CPL.IsFlatCPL Ω w₀ wₐ a t₀` | H = H₀√(Ω(1+z)³ + (1−Ω)(1+z)^{3(1+w₀+wₐ)}e^{−3wₐz/(1+z)}) near t₀ (CLS 2011 Eq. 17), H₀ = H(t₀) > 0, a > 0 and differentiable near t₀; real power of 1+z = a₀/a > 0 | CLS 2011 Eq. 17 | ΛCDM ⇒ CPL(w₀=−1, wₐ=0) (`C4Audit.lcdm_isFlatCPL`, returns the F1 l₀); EdS is CPL(Ω=1, any w₀, wₐ) with l₀ = 35/2 = `l0_eds`; explicit model `cplW` (l₀ = 24 by hand); exists for every parameter point (`exists_flatCPL`); blind restater's `CPLModel` implies it (`C4Audit.blind_implies`) |
| `Checked.Cosmography.CCS.series d4 q j s z`, `remainder D4 a t₀ t` | H₀D(z)/c = z[1 + D¹z + D²z² + D³z³ + D⁴z⁴] (CCS 2008 Eq. A2, D¹–D³ as printed, D⁴ a parameter); remainder H₀(t₀ − t) − series at z(t) | CCS 2008 Eq. (A2) | de Sitter: correct coefficients = ln(1+z) series (`lookback_fifth_order` at exp); restater's `dist − A2rhs` equals ours on de Sitter (`C3Audit.blind_rem_exp`) |
| `Checked.Cosmography.BambaY.yred a t₀ t := z/(1+z)`, `comoving a t₀ t := ∫ s in t..t₀, 1/a s`, `lumDistFlat a t₀ t := a₀(1+z)χ`, `seriesY`, `remainderY` | y-redshift (Cattoën–Visser); comoving distance (c = 1); flat luminosity distance (Bamba et al. Eqs. 10.26, 10.28 with K = 0); y-series with D¹, D² | Bamba et al. 2012 (10.26), (10.28), (10.52)–(10.54) | de Sitter: theorem gives D¹ = 2, D² = 3 = exact y/(1−y)² series (`C5Audit`); blind restater's independent definitions agree pointwise (`C5Audit.residual_eq`) |
| `Checked.Cosmography.CVdQ.dQFlat a t₀ t := lumDistFlat / (1+z)^(3/2 : ℝ)`, `seriesQ`, `remainderQ` | deceleration distance d_Q = d_L/(1+z)^{3/2} (Cattoën–Visser Eq. 5), flat | CV 2007 Eqs. (5), (59) | de Sitter: theorem gives 3/8 = exact y(1−y)^{−1/2} coefficient; blind restater's definitions agree pointwise (`C1Audit.remainder_eq`); rpow base > 0 near t₀ |
| `Checked.Cosmography.Transverse.transverse K χ` (sin(√K χ)/√K, χ, sinh(√−K χ)/√−K), `Checked.Cosmography.BambaK.omega0 K a t₀ := 1 + K/(H₀²a₀²)`, `lumDist K a t₀ t := a₀(1+z)·transverse K (comoving a t₀ t)`, `seriesY4`, `remK` | comoving transverse distance S_K for any real curvature constant K (K = ±1, 0 are Bamba Eq. 10.28); Ω₀ (Bamba p. 110, c = 1); luminosity distance with curvature (Eq. 10.26); y-series to y⁴ and its remainder | Bamba et al. 2012 Eqs. (10.26), (10.28), p. 110 | blind closure `Work/Cosmography/BambaCurvedAudit.lean` (`S_eq`: K = ±1, 0 give sin, id, sinh; `dLnorm_eq`, `Omega0_eq` agree with the blind definitions); Milne: theorem gives D³ = 5/2, D⁴ = 3 = exact y(2−y)/(2(1−y)²) series (referee, blind) |

Junk: `deriv` of a non-differentiable function is 0 and `x/0 = 0`; every theorem using these assumes the derivatives exist and a(t₀), ȧ(t₀) ≠ 0.
| `Checked.Cosmography.FREta.qL jL sL lL`, `eta20Of eta30Of`, `eta20 eta30`, `printedDen printed20 printed30`, `correct20 correct30` | ΛCDM (q₀…l₀) (Bamba (11.39)); F″H⁴/F and F‴H⁶/F from the review's P/Q (R cancels); the same on the common-ε family (11.41); printed (11.42)–(11.43) coefficients verbatim; derived coefficients | Bamba et al. 2012 (11.39), (11.41)–(11.43) | `eta_ratios` (= the true ratios in every F(R) model, via `fR_values`); `printed_numbers` (printed formulas give the printed 0.152, −0.119, 4.02, −0.184); blind closure `FREtaAudit` (blind's ratios with printed R agree near ε = 0) |
| `Checked.Cosmography.DemianskiZ.demDL4 demDA4` | printed flat D⁴_L, D⁴_A of Demianski et al. 2017 (verbatim; readings in module doc) | 1609.09631 p. 3; 1907.07692 p. 2 | blind's independent transcription equal (`DemianskiZAudit.same_transcription`); `flat_corrections` vs Checked `correctDL4z`, `correctDA4z` at k = 0 |
