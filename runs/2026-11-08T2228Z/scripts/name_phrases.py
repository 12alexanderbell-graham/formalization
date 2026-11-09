#!/usr/bin/env python3
"""Second pass (P6, run 2026-11-08T2228Z): put each blind NAME into its phrase word for word. Each replacement must
match exactly once."""
import sys
from pathlib import Path
ROOT = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
SUBS = [
("the luminosity distance, at the observation time {t₀}, of a source at the emission time {t}, in the FLRW model with scale factor {a} and spatial curvature constant {K}",
 "the luminosity distance in FLRW with curvature, at the observation time {t₀}, of a source at the emission time {t}, with scale factor {a} and spatial curvature constant {K}"),
("the angular-diameter distance, at the observation time {t₀}, of a source at the emission time {t}, in the FLRW model with scale factor {a} and spatial curvature constant {K}",
 "the angular diameter distance in FLRW with curvature, at the observation time {t₀}, of a source at the emission time {t}, with scale factor {a} and spatial curvature constant {K}"),
("obeys the flat ΛCDM expansion law", "obeys the flat ΛCDM Friedmann expansion law"),
("Checked.Cosmography.redshift | the redshift at", "Checked.Cosmography.redshift | the cosmological redshift at"),
("BambaK.omega0 | the total density parameter Ω₀", "BambaK.omega0 | the present total density parameter Ω₀"),
("BambaZ.curvK | the curvature parameter at", "BambaZ.curvK | the dimensionless spatial curvature parameter at"),
("BambaY.lumDistFlat | the spatially flat luminosity distance, at", "BambaY.lumDistFlat | the luminosity distance in flat FLRW, at"),
("CPL dark-energy expansion law", "CPL dark-energy Friedmann expansion law"),
("FRCosmo.curv | the Ricci scalar of spatially flat FLRW with", "FRCosmo.curv | the Ricci scalar of flat FLRW with"),
("FRCosmo.rhoM | the dust density at", "FRCosmo.rhoM | the dust matter density at"),
("FRCosmo.FriedmannEq | the expansion-rate (Friedmann) equation of metric F(R) gravity with dust, Bamba et al. 2012 Eqs. (11.1)–(11.2) multiplied",
 "FRCosmo.FriedmannEq | the metric F(R) gravity Friedmann equation with dust (the expansion-rate equation, Bamba et al. 2012 Eqs. (11.1)–(11.2)) multiplied"),
("FRCosmo.MasterEq | the second field equation of metric F(R) gravity with dust, Bamba et al. 2012 Eq. (11.5) multiplied",
 "FRCosmo.MasterEq | the metric F(R) gravity second equation with dust (the second field equation, Bamba et al. 2012 Eq. (11.5)) multiplied"),
("Transverse.transverse | the transverse factor S_K(χ) for", "Transverse.transverse | the FLRW transverse distance function S_K(χ) for"),
("CubicEOS.IsCriticalIsotherm | the molar volume at the point {v} is a critical point of the isotherm pressure function of molar volume {p} (pressure",
 "CubicEOS.IsCriticalIsotherm | the critical point condition of an isotherm holds for the isotherm pressure function of molar volume {p} at the molar volume at the point {v} (pressure"),
("Coexistence.IsMaxwellCoexistence | the liquid molar volume {vl} and the gas molar volume {vg}, with {vl} below {vg}, are in Maxwell coexistence on the isotherm",
 "Coexistence.IsMaxwellCoexistence | the Maxwell equal area coexistence condition holds for the liquid molar volume {vl} and the gas molar volume {vg}, with {vl} below {vg}, on the isotherm"),
("Duffing.IsDuffingSolution | the position as function of time {x} solves the Duffing equation",
 "Duffing.IsDuffingSolution | the position as function of time {x} is a Duffing oscillator initial value problem solution: it solves the Duffing equation"),
("the product concentration over time {p} solve the mass-action rate equations",
 "the product concentration over time {p} are a Michaelis Menten mass action initial value problem solution: they solve the mass-action rate equations"),
("the concentration of species C over time {y₃} solve the rate equations",
 "the concentration of species C over time {y₃} are a Robertson chemical kinetics initial value problem solution: they solve the rate equations"),
]
p = ROOT / "scripts/trust/phrases.txt"
t = p.read_text(encoding="utf-8")
for old, new in SUBS:
    assert t.count(old) == 1, old
    t = t.replace(old, new)
p.write_text(t, encoding="utf-8")
print("applied", len(SUBS))
