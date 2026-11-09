# d04 – an argument's role is never required (CPL parameters dropped from the phrase)

Generated line (every use of `IsFlatCPL`; e.g. headline premises F2_toy, F2_error at CLAIMS.md l.3065, 3093):
"the scale factor `a` obeys the flat matter plus CPL dark energy Friedmann expansion law with the present matter density parameter `Ω := 245 / 1000` and the observation time `t₀` (spatially flat universe with dust and separately conserved dark energy; redshift z is measured from `t₀`; ...)"

False/overstated: IsFlatCPL has five arguments; the equation-of-state parameters w₀, wₐ are no longer named in the premise, so F2_toy ("then cosmoCoeff 5 a t₀ rounds to 0.809 ...") reads as a statement about every flat matter plus CPL scale factor with Ω = 0.245, and F2_error ("for every w₀ ... difference 2.345") about a premise in which w₀ plays no role. The values w₀ := -93/100, wₐ := -41/100 disappear from the hypothesis (they remain in the conclusion's `printedCLSL0 ...` in F2_toy, which is the disclosure; in F2_error only wₐ = -1/2 survives there).

Mechanism: P3 only binds placeholders that occur; P7/P9 require NAME, SIGN and CLAUSE texts but never a ROLE text or an occurrence of each binder; Claims.lean only checks that placeholders are binders. LEDGER line names IsFlatCPL.
Rules passed: all Python rules (see REPORT). Expected: survives snapshot; DOES NOT survive P11 (the fixed template lists every role); P10 does not touch it.
