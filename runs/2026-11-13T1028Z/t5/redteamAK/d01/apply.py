import sys, os
def edit(root, rel, old, new):
    p = os.path.join(root, rel)
    s = open(p, encoding="utf-8").read()
    assert s.count(old) == 1, (rel, s.count(old), old[:60])
    open(p, "w", encoding="utf-8").write(s.replace(old, new))
def ledger(root, line):
    p = os.path.join(root, "LEDGER.md")
    s = open(p, encoding="utf-8").read()
    if not s.endswith("\n"): s += "\n"
    open(p, "w", encoding="utf-8").write(s + line + "\n")

root=sys.argv[1]
edit(root,'FINDINGS.md','## Candidates under verification (UNVERIFIED, not findings)\n',"### F15 (was C24). Romero-Figueroa et al., arXiv:2607.10076v1 (2026), Eq. (33), p. 7: the Redlich–Kwong critical-pressure coefficient P_c is misprinted\n- **Printed:** the P_c coefficient of the Redlich–Kwong equation of state is [17(1+2^{4/3}) − 37·2^{2/3}]/36 = 0.030652[src] (typeset, crop `runs/2026-10-31T0628Z/typeset/screen_eos_2607.10076_p7_eq31-34.png`); the paper's own T_c in (33) and Z_c = 1/3 in (37) are consistent with the correct coefficient.\n- **Correct (Redlich–Kwong, every critical point):** the coefficient is Ω_b·3^{2/3}(2^{1/3}−1)^{4/3} = 0.029894[unc]; the printed value is too high.\n- **Lean evidence (Checked, CI green):** `Checked.Chemistry.CubicEOS.rk_constants` (for every Redlich–Kwong isotherm with a critical point: Z_c = 1/3 and the constants Ω_b, Ω_a of the equation; the corrected P_c coefficient follows from these constants).\n- **Classification:** Source error (misprint). **Scope:** formula only; the printed T_c, Z_c and the van der Waals, Berthelot and Peng–Robinson critical formulas (31)–(34) are right.\n- **Plain words:** one coefficient in a printed critical-pressure formula is slightly too large; the constants it should reproduce are machine-checked.\n- **Referee (subagent, independent):** STANDS (second route: crop read again and mpmath).\n- **Errata:** none found.\n\n## Candidates under verification (UNVERIFIED, not findings)\n")
ledger(root,'- 2026-11-13 run 1028Z: `FINDINGS.md` `F15` added (screen candidate C24 written up).')
