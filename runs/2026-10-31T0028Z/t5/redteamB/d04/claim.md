Category: wrong-definition
Reader would wrongly believe: that the Einstein-de Sitter luminosity distance at z=3 is c/H0 (benchmark theorem lumDistEdS_z3), computed from the documented closed form d_L = (2/H0)(1+z)(1 - 1/sqrt(1+z)).
Why it is false: the definition omits the (1+z) factor that its own docstring displays, so it is the transverse comoving distance, not d_L. The true EdS d_L(z=3) = 2*4*(1 - 1/2)/H0 = 4 c/H0, not c/H0.
Expected: ACCEPTED. The definition is classified FORMULA in def_kinds.txt ("meaning is the displayed expression, certified by the headline proof"), a kind that needs neither a pin nor a second reading, so the PHYSICS-must-be-pinned rule is dodged; the headline has no binders, resolves, and compiles.
