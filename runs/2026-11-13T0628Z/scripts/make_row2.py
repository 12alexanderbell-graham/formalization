#!/usr/bin/env python3
"""Run 2026-11-13T0628Z: copy of runs/2026-11-13T0228Z/scripts/make_row3.py for row -0.02 (output path, namespace, header,
cell directory and the proof route changed: the stack with a wider shear clamp, Checked/FSRevW; statement text unchanged). Run 0228Z: copy of runs/2026-11-12T2228Z/scripts/make_table.py for row -0.03. Writes OUT (default Work/FalknerSkan/ReversedRowThree.lean). Original: the statement file Work/FalknerSkan/ReversedTable.lean for the reversed-flow Falkner–Skan rows of
runs/2026-11-12T2228Z/scripts/rows_rev.json (the rest of Ganapol 2010 Table 7). Statements: copy of
runs/2026-11-12T1828Z/scripts/make_rev_rows.py's `fs_rev_<row>_exists` (= `fs_neg1988_reversed` of
Work/FalknerSkan/Neg1988Rev.lean, blind restatement closed in run 2026-11-11T1228Z, with β and the ten-decimal window
replaced). Proofs: `RAssemble.core_rev` (tube ending at 3/2) or `RAssembleA.core_revA` (tube ending at 7/4, rows with
larger scaled coefficient). usage: make_table.py freeze|prove tag..."""
import json, sys, pathlib
from fractions import Fraction as Fr
R = pathlib.Path(__file__).resolve().parents[3]
rows = json.load(open(R / 'runs/2026-11-12T2228Z/scripts/rows_rev.json')); mode = sys.argv[1]; OUT = sys.argv[2]; tags = sys.argv[3:]
CELLS = R / 'runs/2026-11-13T0628Z/cells'
QC = 4
NAMES = {'01': 'One', '02': 'Two', '03': 'Three', '04': 'Four', '05': 'Five', '06': 'Six', '07': 'Seven', '08': 'Eight', '09': 'Nine',
         '11': 'Eleven', '12': 'Twelve', '13': 'Thirteen', '14': 'Fourteen', '16': 'Sixteen'}
def lit(x): x = Fr(x); return f"{x.numerator} / {x.denominator}"
body = []
for tag in tags:
    r = rows[tag]; nm = NAMES[tag]; K = Fr(r['K']); KN, KD = (r['K'].split('/') + ['1'])[:2]
    BN, BD = int(tag), 100
    assert K == Fr(BD, BN)
    lo = r['lo']; hi = lo + 1
    los = f"-0.{-lo:010d}"; his = f"-0.{-hi:010d}"
    assert Fr(los) == Fr(lo, 10**10) and Fr(his) == Fr(hi, 10**10)
    Ao = -Fr(r['Aover']); As = -Fr(r['Aslow'])
    ns = f"W{nm}"; ln = nm.lower()
    Lt = Fr(*json.load(open(CELLS / f'{tag}_tube.json'))['L']) if mode == 'prove' else None
    if mode == 'prove':
        core = f"Checked.FSRevW.WAssemble.core_revW (Cq := {QC}) (K := {{KN}} / {{KD}}) (by norm_num) (by norm_num) (L := {Lt.numerator} / {Lt.denominator}) (by norm_num) (by norm_num)"
        core = core.replace('{KN}', KN).replace('{KD}', KD)
        aux = f"""theorem {ln}_sqrtK_pos : 0 < Real.sqrt ({KN} / {KD} : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem {ln}_hK : (-1 / ({KN} / {KD} : ℝ)) = -{BN} / {BD} := by norm_num

theorem {ln}_lo_bound : ({los} : ℝ) < -({lit(Ao)}) / Real.sqrt ({KN} / {KD}) := by
  have hs := {ln}_sqrtK_pos
  have h : ({lit(Ao)}) / ({los[1:]} : ℝ) < Real.sqrt ({KN} / {KD} : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem {ln}_hi_bound : -({lit(As)}) / Real.sqrt ({KN} / {KD}) < ({his} : ℝ) := by
  have hs := {ln}_sqrtK_pos
  have h : Real.sqrt ({KN} / {KD} : ℝ) < ({lit(As)}) / ({his[1:]} : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

"""
        pr = f"""by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    {core}
      Checked.FSRevW.{ns}Over.chain Checked.FSRevW.{ns}Slow.chain Checked.FSRevW.{ns}Tube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← {ln}_hK]; exact a3 η hη
  · have e : (-{Ao.numerator} / {Ao.denominator} : ℝ) / Real.sqrt ({KN} / {KD}) = -({lit(Ao)}) / Real.sqrt ({KN} / {KD}) := by ring
    linarith [{ln}_lo_bound]
  · have e : (-{As.numerator} / {As.denominator} : ℝ) / Real.sqrt ({KN} / {KD}) = -({lit(As)}) / Real.sqrt ({KN} / {KD}) := by ring
    linarith [{ln}_hi_bound]"""
    else:
        aux = ''; pr = 'sorry'
    body.append(aux + f"""/-- Falkner–Skan with β = −{BN}/{BD}: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0
on [0, ∞) with f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, eventually
M (1 − p) ≤ q, whose wall value satisfies {los} < q(0) < {his} (reversed flow at the wall). -/
theorem fs_rev_{ln}_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-{BN} / {BD}) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      {los} < q 0 ∧ q 0 < {his} := {pr}
""")
imports = ['import Mathlib'] + (['import Checked.FSRevW.WAssemble'] +
    [f'import Checked.FSRevW.W{NAMES[t]}{s}' for t in tags for s in ('Over', 'Slow', 'Tube')] if mode == 'prove' else [])
vals = ', '.join(f"{rows[t]['q0']:.11f}" for t in tags)
hdr = f'''
/-!
# Falkner–Skan reversed-flow row β = −0.02 of Ganapol 2010 Table 7: wall-shear window of the second branch (FROZEN, run 2026-11-13T0628Z; statements unchanged, proofs added)

Parts 2/5. The statement `fs_neg1988_reversed` of `Work/FalknerSkan/Neg1988Rev.lean` (blind-restated and closed in
run 2026-11-11T1228Z) with β and the window replaced (ten decimals), as in `Work/FalknerSkan/ReversedRows.lean`,
emitted by `runs/2026-11-13T0628Z/scripts/make_row2.py` (copy of run 0228Z's `make_row3.py`; proof route: the stack with the shear clamp at 4, `Checked/FSRevW/`) from `runs/2026-11-12T2228Z/scripts/rows_rev.json` (float
shooting `runs/2026-11-12T1828Z/scripts/shoot_rev.py`: q(0) ≈ {vals}).
Do not change the statements; prove them.
-/

namespace Work.FalknerSkan.ReversedRowTwo

open Set Filter Topology

'''
(R / OUT).write_text('\n'.join(imports) + '\n' + hdr + '\n'.join(body) + '\nend Work.FalknerSkan.ReversedRowTwo\n')
print('ok', mode, tags)
