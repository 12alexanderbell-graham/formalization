#!/usr/bin/env python3
"""Rewrite the 23 phrases so that every placeholder is preceded by its blind role and every blind sign convention
occurs word for word (check_claims.py P3/P4, run 2026-11-08T2228Z). Roles and sign clauses are copied from
scripts/trust/phrase_roles.txt; everything else of each phrase is kept where it still reads correctly."""
import re, sys
from pathlib import Path
ROOT = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
NEW = {
"Checked.Cosmography.hubble": "the Hubble rate of the scale factor {a} at the cosmic time of evaluation {t}",
"Checked.Cosmography.decel": "the deceleration parameter of the scale factor {a} at the cosmic time of evaluation {t} (minus acceleration times scale factor over velocity squared)",
"Checked.Cosmography.redshift": "the redshift at the observation time {t₀} of light at the emission time {t} (scale factor {a}; positive when emission precedes observation in an expanding universe)",
"BambaK.lumDist": "the luminosity distance, at the observation time {t₀}, of a source at the emission time {t}, in the FLRW model with scale factor {a} and spatial curvature constant {K} (units in which the speed of light is one; positive curvature constant means closed, negative means open)",
"BambaA.angDist": "the angular-diameter distance, at the observation time {t₀}, of a source at the emission time {t}, in the FLRW model with scale factor {a} and spatial curvature constant {K} (units in which the speed of light is one; positive curvature constant means closed, negative means open)",
"Aviles.IsFlatLCDM": "the scale factor {a} obeys the flat ΛCDM expansion law with present matter density parameter {Ω} on some neighbourhood of the observation time {t₀}, with a positive Hubble rate at {t₀} and a positive, differentiable scale factor on that neighbourhood",
"Aviles.cosmoCoeff": "the cosmographic coefficient of the scale factor {a} at the time of evaluation {t} for the derivative order of the coefficient {n} (j, s, l, m for the orders 3, 4, 5, 6; the deceleration parameter is minus the order 2 coefficient)",
"BambaY.yred": "the y-redshift at the observation time {t₀} of light at the emission time {t} (scale factor {a}; positive for redshift, negative for blueshift)",
"BambaK.omega0": "the total density parameter Ω₀ at the observation time {t₀} for spatial curvature constant {K} and scale factor {a} (units in which the speed of light is one; one plus curvature term, positive curvature constant gives above one; Ω_k is one minus Ω₀)",
"BambaZ.curvK": "the curvature parameter at the observation time {t₀} for spatial curvature constant {K} and scale factor {a} (units in which the speed of light is one; has sign of curvature constant, minus the curvature density parameter)",
"BambaY.lumDistFlat": "the spatially flat luminosity distance, at the observation time {t₀}, of a source at the emission time {t} (scale factor {a}; units in which the speed of light is one)",
"BambaY.comoving": "the comoving radial distance between the emission time {t} and the observation time {t₀} (scale factor {a}; units in which the speed of light is one)",
"CPL.IsFlatCPL": "the scale factor {a} obeys the flat matter plus CPL dark-energy expansion law with present matter density parameter {Ω}, present dark energy equation of state {w₀} and equation of state evolution parameter {wₐ} on some neighbourhood of the observation time {t₀}, with a positive Hubble rate at {t₀} and a positive, differentiable scale factor on that neighbourhood",
"FRCosmo.curv": "the Ricci scalar of spatially flat FLRW with scale factor {a} at the cosmic time of evaluation {t} (sign convention of Bamba et al. 2012, Eq. (11.6): negative convention, de Sitter has negative Ricci scalar)",
"FRCosmo.rhoM": "the dust density at the time of evaluation {t} for the present matter density parameter {Ω} referred to the present time {t₀} (scale factor {a}; units in which the coupling κ is one)",
"FRCosmo.FriedmannEq": "the expansion-rate (Friedmann) equation of metric F(R) gravity with dust, Bamba et al. 2012 Eqs. (11.1)–(11.2) multiplied through by three times the derivative of F at the Ricci scalar, holds at the time of evaluation {t} for the scale factor {a}, the gravity Lagrangian function of Ricci scalar {F} and the present matter density parameter {Ω} referred to the present time {t₀} (negative Ricci scalar convention, minus the common one)",
"FRCosmo.MasterEq": "the second field equation of metric F(R) gravity with dust, Bamba et al. 2012 Eq. (11.5) multiplied through by minus two times the derivative of F at the Ricci scalar, holds at the time of evaluation {t} for the scale factor {a}, the gravity Lagrangian function of Ricci scalar {F} and the present matter density parameter {Ω} referred to the present time {t₀} (negative Ricci scalar convention, minus the common one)",
"Transverse.transverse": "the transverse factor S_K(χ) for the spatial curvature constant {K} at the comoving radial distance {χ} (sine form for positive, identity for zero, hyperbolic sine form for negative curvature; positive curvature constant gives sine, closed spherical case)",
"CubicEOS.IsCriticalIsotherm": "the molar volume at the point {v} is a critical point of the isotherm pressure function of molar volume {p} (pressure as a function of molar volume at fixed temperature): its first and second derivatives vanish at {v}",
"Coexistence.IsMaxwellCoexistence": "the liquid molar volume {vl} and the gas molar volume {vg}, with {vl} below {vg}, are in Maxwell coexistence on the isotherm pressure function of molar volume {p} at the saturation pressure {ps}: the isotherm takes the value {ps} at both, and its integral from {vl} to {vg} equals {ps} times the volume difference",
"Duffing.IsDuffingSolution": "the position as function of time {x} solves the Duffing equation with linear stiffness coefficient {k} and cubic stiffness coefficient {β}, initial position {x₀} and initial velocity {v₀} on the time interval from 0 to the final time of the interval {T} (derivatives taken within [0, {T}]; restoring force for positive stiffness, acceleration equals minus force terms)",
"MichaelisMenten.IsMMSolution": "the substrate concentration over time {s}, the free enzyme concentration over time {e}, the complex concentration over time {c} and the product concentration over time {p} solve the mass-action rate equations of the mechanism in which E and S bind reversibly to C and C releases E and P, with binding rate constant {k₁}, unbinding rate constant {km₁} and catalytic rate constant {k₂}, on the time interval from 0 to the final time of the interval {T} (derivatives taken within [0, {T}]), with initial substrate concentration {s₀}, initial free enzyme concentration {e₀}, initial complex concentration {c₀} and initial product concentration {p₀} at time 0 (binding consumes substrate and free enzyme, forms complex)",
"Robertson.IsRobSolution": "the concentration of species A over time {y₁}, the concentration of species B over time {y₂} and the concentration of species C over time {y₃} solve the rate equations of the reaction network in which A turns into B with rate constant of the first reaction {k₁}, B and C turn into A and C with rate constant of the second reaction {k₂}, and two B turn into B and C with rate constant of the third reaction {k₃}, on the time interval from 0 to the final time of the interval {T} (derivatives taken within [0, {T}]), with initial concentration of species A {a₀}, initial concentration of species B {b₀} and initial concentration of species C {c₀} at time 0",
}
p = ROOT / "scripts/trust/phrases.txt"
lines = p.read_text(encoding="utf-8").split("\n")
done = set()
for i, l in enumerate(lines):
    if " | " in l and not l.startswith("#"):
        d = l.split(" | ", 1)[0].strip()
        if d in NEW:
            old = set(re.findall(r"\{([^}]*)\}", l.split(" | ", 1)[1]))
            assert old == set(re.findall(r"\{([^}]*)\}", NEW[d])), d
            lines[i] = f"{d} | {NEW[d]}"
            done.add(d)
assert done == set(NEW), set(NEW) - done
p.write_text("\n".join(lines), encoding="utf-8")
print("rewrote", len(done))
