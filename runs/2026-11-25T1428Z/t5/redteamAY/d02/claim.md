Category: unregistered-or-misregistered (phrase_certs.txt: a line shown as "proved in Lean" by a theorem that proves something else)
Reader would wrongly believe: for `flatLCDM_coeffs` that Lean proves "spatially flat universe with dust and a cosmological constant" of `IsFlatLCDM` (and likewise CPL), when the cited theorem `flatLCDM_expanding` only proves the Hubble rate is positive.
Why it is false: see `Checked/Trust/PhraseCerts.lean` flatLCDM_expanding/flatCPL_expanding (conclusion 0 < hubble ...).
Expected: CAUGHT by Claims.lean itself (tested): "the docstring of ...flatLCDM_expanding does not quote the line ... (P13)". Attempt reported only; apply.py is a valid test of that control. Same for any cert of a baselined line: no Checked docstring quotes those lines.
