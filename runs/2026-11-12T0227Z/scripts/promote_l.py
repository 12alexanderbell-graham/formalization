"""Copy the scratch runs/2026-11-12T0227Z/lean/NecessityL.lean to Checked/Trust/NecessityL.lean:
replace the scratch module doc by the Checked one (no fractions or decimals: check_prose rule 7) and turn the
inner section docs into plain comments. Run from the repository root."""
src = open('runs/2026-11-12T0227Z/lean/NecessityL.lean').read()
i = src.index('/-!'); j = src.index('-/', i) + 2
header = '''/-!
# Hypothesis necessity, B1 family and pinning specifications (trust track T2b, run 2026-11-12T0227Z)

Scratch: `runs/2026-11-12T0227Z/lean/NecessityL.lean`. Witnesses for the fourteen B1 headlines (log-polynomial
luminosity-distance fits tested against flat ΛCDM, with and without curvature):
* differentiability of the scale factor and positivity of today's Hubble rate are REDUNDANT: the expansion law
  with a positive radicand forces differentiability (a junk derivative would make the Hubble rate vanish), and
  with a non-positive Hubble rate today the law makes the scale factor non-increasing, so no earlier source has
  positive redshift (`diff_of_law`, `H0_pos_of_redshift`);
* each source-redshift condition is NEEDED: moving one source onto the other makes the two residuals equal;
* the expansion law is NEEDED: the radiation-like model `a = √t` meets every other hypothesis and has `d_L = 2z`;
* a positive normalisation `H` is NEEDED where the statement allows `H = 0` (junk division makes every residual
  zero), and in the box theorems through a negative `H`;
* the coefficient box and the positivity at the far source of the two box theorems are NEEDED: in the exact
  ΛCDM model the far distance is at most four times the near one (`model_ratio`), and a quartic whose far value
  exceeds four times its near value makes the far residual no larger (`no_rise`);
* each residual condition of the separation pair is NEEDED: the ΛCDM coefficients match the remaining residual.

And for the twelve pinning theorems of `Checked/Fidelity/`: the specification hypothesis is NEEDED (a constant
function meets every other hypothesis and differs from the program definition in the static or de Sitter model);
for `hubbleSpec_pins`, `decelSpec_pins`, `yRedSpec_pins`, `omega0Spec_pins` and `curvKSpec_pins` the positivity, differentiability and nonzero-rate
conditions are NEEDED as well (the program definition shifted by one off that domain still meets the
specification), except differentiability in `omega0Spec_pins` and `curvKSpec_pins`, which is REDUNDANT (a nonzero
Hubble rate needs a genuine derivative).
-/'''
out = src[:i] + header + src[j:]
k = out.index('-/', out.index('# Hypothesis necessity, B1 family')) + 2
out = out[:k] + out[k:].replace('/-!', '/-')
open('Checked/Trust/NecessityL.lean', 'w').write(out)
