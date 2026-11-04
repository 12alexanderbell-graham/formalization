import sys, os
root = sys.argv[1]
def rd(p):
    return open(os.path.join(root, p), encoding="utf-8").read()
def wr(p, s):
    open(os.path.join(root, p), "w", encoding="utf-8").write(s)
def rep(p, old, new):
    s = rd(p); assert s.count(old) == 1, (p, old[:40], s.count(old)); wr(p, s.replace(old, new))
def app(p, add):
    s = rd(p); wr(p, s + add)

LEAN = 'import Checked.Chemistry.Coexistence\n\nnamespace Checked.Chemistry.Coexistence\nopen Checked.Records Checked.Chemistry.CubicEOS\n\n/-- Law of corresponding states for the Maxwell construction at T = 0.7 · 8a/(27Rb) (that is 0.7 T_c):\nevery Maxwell coexistence state with liquid volume above the co-volume b has p_s = 0.20046 · a/(27b²)\n(that is 0.20046 P_c) to five decimals. This reduced saturation pressure is the same for the\nRedlich–Kwong, Soave and Peng–Robinson equations alike, which is why the acentric factor can be\ndefined once from it. -/\ntheorem vdW_coexistence_corresponding (R a b vl vg ps : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)\n    (hl : b < vl)\n    (h : IsMaxwellCoexistence (cubicP R a b 0 0 (7 / 10 * (8 * a / (27 * R * b)))) vl vg ps) :\n    RoundsTo (ps / (a / (27 * b ^ 2))) 0.20046 5 :=\n  vdW_coexistence_unique R a b vl vg ps hR ha hb hl h\n\nend Checked.Chemistry.Coexistence\n'
wr('Checked/Chemistry/CoexistenceCorresponding.lean', LEAN)
app("Checked.lean", "import Checked.Chemistry.CoexistenceCorresponding\n")
app("scripts/trust/headlines.txt", 'Checked.Chemistry.Coexistence.vdW_coexistence_corresponding\n')
rep("Checked/Trust/Witnesses.lean", 'import Checked.Chemistry.Coexistence\n', 'import Checked.Chemistry.Coexistence\nimport Checked.Chemistry.CoexistenceCorresponding\n')
rep("Checked/Trust/Witnesses.lean", "\nend Checked.Trust.NV", '\ntheorem vdW_coexistence_corresponding : nonvacuity% Checked.Chemistry.Coexistence.vdW_coexistence_corresponding := by\n  obtain ⟨vl, vg, ps, hl, h, -⟩ :=\n    Checked.Chemistry.Coexistence.vdW_coexistence_exists 1 1 1 one_pos one_pos one_pos\n  exact ⟨1, 1, 1, vl, vg, ps, one_pos, one_pos, one_pos, hl, h, trivial⟩\n\nend Checked.Trust.NV')
