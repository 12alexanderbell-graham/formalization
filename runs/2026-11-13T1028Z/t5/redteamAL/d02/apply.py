import sys, subprocess
import sys, re
root = sys.argv[1]
def rd(p): return open(f"{root}/{p}", encoding="utf-8").read()
def wr(p, t): open(f"{root}/{p}", "w", encoding="utf-8").write(t)
def sub(p, old, new):
    t = rd(p); assert t.count(old) == 1, (p, old[:40], t.count(old)); wr(p, t.replace(old, new))
def ledger(line):
    t = rd("LEDGER.md")
    if not t.endswith("\n"): t += "\n"
    wr("LEDGER.md", t + line + "\n")
new = """### F15a (was C-BE-1). Galli, Walmsley & Gonçalves, A&A 394, 275 (2002), arXiv:astro-ph/0208416, p. 2, Sect. 2: the critical density contrast of the Bonnor–Ebert sphere is printed as 13.98[src], the certified value is 14.04[unc]
- **Printed:** "equilibrium configurations with center-to-boundary density contrast ρ_c/ρ_b < 13.98[src] are stable, whereas equilibrium solutions with ρ_c/ρ_b > 13.98[src] are unstable to radial collapse" (typeset, read twice).
- **Correct:** the stability boundary lies at ρ_c/ρ_b = 14.04[unc], for every Bonnor–Ebert sphere; the printed threshold misplaces it by 0.06[unc] in contrast.
- **Lean evidence (Checked, CI green):** `Work.Math.BonnorEbert.bonnor_ebert_critical` (the mass increases strictly up to ξ₁ and decreases after it; the contrast there is 14.042032[unc]).
- **Classification:** Source error (numerical). **Scope:** a stated threshold, not a computed number of that paper's results; no other printed value of the threshold in the literature is affected.
- **Plain words:** a widely used stability threshold for isothermal gas spheres is printed slightly too low in this paper; the true boundary is 14.04[unc].

"""
sub("FINDINGS.md", "## Candidates under verification (UNVERIFIED, not findings)", new + "## Candidates under verification (UNVERIFIED, not findings)")
ledger("- 2026-11-13 run 1028Z: `FINDINGS.md` new finding `F15a` added (Bonnor–Ebert threshold).")
for cmd in (["python3","scripts/trust/check_numbers.py","--write"],["python3","validation/make_packet.py"]):
    subprocess.run(cmd, cwd=root, check=True, stdout=subprocess.DEVNULL)
