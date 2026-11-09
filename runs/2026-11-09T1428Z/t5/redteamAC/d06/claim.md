# d06 – case folding / Greek letters in P7 token matching (low severity)

Generated line (every use of `omega0`):
"the present total density parameter ω0 with the spatial curvature constant `K`, the scale factor `a` and the observation time `t₀` (one plus curvature term, positive curvature constant gives above one; ...)"
Blind NAME: "present total density parameter Ω0". Small omega is the physical density (omega = Omega h^2) or an angular frequency; the Lean body `1 + K / (...)` is the dimensionless total density parameter. A reader is told the function returns ω0.
Mechanism: `_ntok` NFKC-lowercases, so Ω0 == ω0 for P7; P4/P6 (`role_binding`) use WORD, which drops Greek letters and digits (the NAME check only sees "present total density parameter"). Same for every Greek symbol or case-distinct letter of a blind text (F/f, R/r, K/k, Λ/λ in "flat ΛCDM").
Rules passed: all (LEDGER line names omega0). Expected: survives snapshot; killed by P11 (phrase must equal the template output).
