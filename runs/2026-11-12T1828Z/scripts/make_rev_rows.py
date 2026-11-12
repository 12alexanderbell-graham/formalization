#!/usr/bin/env python3
"""Run 2026-11-12T1828Z: the statement file Work/FalknerSkan/ReversedRows.lean for the reversed-flow Falkner–Skan rows
of rows_rev.json. Statements: `Work/FalknerSkan/Neg1988Rev.lean` (`fs_neg1988_reversed`, `fs_neg1988_two_decay`; blind
restatement closed in run 2026-11-11T1228Z) with β and the window replaced; window = the ten-decimal cell of the float
shooting value. usage: make_rev_rows.py freeze|prove"""
import json, sys, pathlib
from fractions import Fraction as Fr
R = pathlib.Path(__file__).resolve().parents[3]
rows = json.load(open(R / 'runs/2026-11-12T1828Z/scripts/rows_rev.json')); mode = sys.argv[1]
NAMES = {'15': 'Fifteen', '17': 'Seventeen', '18': 'Eighteen', '19': 'Nineteen'}
ATT = {'15': 'Work.FalknerSkan.AttachedRows.fs_att_fifteen_exists_decay',
       '17': 'Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_17_exists_decay',
       '18': 'Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_18_exists_decay',
       '19': 'Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_19_exists_decay'}
def lit(x): x = Fr(x); return f"{x.numerator} / {x.denominator}"
body = []
for tag in ('15', '17', '18', '19'):
    r = rows[tag]; nm = NAMES[tag]; K = Fr(r['K']); KN, KD = r['K'].split('/')
    BN, BD = int(tag), 100
    assert K == Fr(BD, BN)
    lo = r['lo']; hi = lo + 1  # q(0) window in units of 1e-10, negative
    los = f"-0.{-lo:010d}"; his = f"-0.{-hi:010d}"
    assert Fr(los) == Fr(lo, 10**10) and Fr(his) == Fr(hi, 10**10)
    Ao = -Fr(r['Aover']); As = -Fr(r['Aslow'])   # positive magnitudes
    ns = f"R{nm}"
    if mode == 'prove':
        aux = f"""theorem {nm.lower()}_sqrtK_pos : 0 < Real.sqrt ({KN} / {KD} : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem {nm.lower()}_hK : (-1 / ({KN} / {KD} : ℝ)) = -{BN} / {BD} := by norm_num

theorem {nm.lower()}_lo_bound : ({los} : ℝ) < -({lit(Ao)}) / Real.sqrt ({KN} / {KD}) := by
  have hs := {nm.lower()}_sqrtK_pos
  have h : ({lit(Ao)}) / ({los[1:]} : ℝ) < Real.sqrt ({KN} / {KD} : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
  rw [div_lt_iff₀ (by norm_num)] at h; linarith

theorem {nm.lower()}_hi_bound : -({lit(As)}) / Real.sqrt ({KN} / {KD}) < ({his} : ℝ) := by
  have hs := {nm.lower()}_sqrtK_pos
  have h : Real.sqrt ({KN} / {KD} : ℝ) < ({lit(As)}) / ({his[1:]} : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hs]
  rw [lt_div_iff₀ (by norm_num)] at h; linarith

"""
        pr = f"""by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Checked.FSRev.RAssemble.core_rev (K := {KN} / {KD}) (by norm_num) (by norm_num)
      Checked.FSRev.{ns}Over.chain Checked.FSRev.{ns}Slow.chain Checked.FSRev.{ns}Tube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, ?_, ?_⟩
  · rw [← {nm.lower()}_hK]; exact a3 η hη
  · have e : (-{Ao.numerator} / {Ao.denominator} : ℝ) / Real.sqrt ({KN} / {KD}) = -({lit(Ao)}) / Real.sqrt ({KN} / {KD}) := by ring
    linarith [{nm.lower()}_lo_bound]
  · have e : (-{As.numerator} / {As.denominator} : ℝ) / Real.sqrt ({KN} / {KD}) = -({lit(As)}) / Real.sqrt ({KN} / {KD}) := by ring
    linarith [{nm.lower()}_hi_bound]"""
        pr2 = f"""by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ := fs_rev_{nm.lower()}_exists
  obtain ⟨f₂, p₂, q₂, b1, b2, b3, b4, b5, b6, b7, b8⟩ := {ATT[tag]}
  have h00 : (0 : ℝ) ∈ Ici (0 : ℝ) := Set.mem_Ici.2 le_rfl
  have hmono : MonotoneOn p₂ (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := q₂) (convex_Ici 0)
      (HasDerivWithinAt.continuousOn (fun x hx => b2 x hx)) (fun x hx => ?_) (fun x hx => ?_)
    · exact (b2 x (interior_subset hx)).mono interior_subset
    · exact (b7 x (interior_subset hx)).le
  have hp₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1 := by
    intro η hη
    have h0 : p₂ 0 ≤ p₂ η := hmono h00 hη hη
    have h1 : p₂ η ≤ 1 := ge_of_tendsto b6
      (eventually_atTop.2 ⟨η, fun t ht => hmono hη (le_trans hη ht) ht⟩)
    constructor <;> linarith
  refine ⟨f, p, q, f₂, p₂, q₂, a1, a2, a3, b1, b2, b3, a4, a5, b4, b5, a6, b6, a7, hp₂, a8, b8, ?_⟩
  have := b7 0 h00
  intro h; rw [h] at w2; linarith"""
    else:
        aux = ''; pr = 'sorry'; pr2 = 'sorry'
    body.append(aux + f"""/-- Falkner–Skan with β = −{BN}/{BD}: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0
on [0, ∞) with f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, eventually
M (1 − p) ≤ q, whose wall value satisfies {los} < q(0) < {his} (reversed flow at the wall). -/
theorem fs_rev_{nm.lower()}_exists :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-{BN} / {BD}) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      {los} < q 0 ∧ q 0 < {his} := {pr}

/-- Falkner–Skan with β = −{BN}/{BD}: there are solutions (f, p, q) and (f₂, p₂, q₂) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, p → 1 and −1 ≤ p ≤ 1 on [0, ∞), with
q(0) ≠ q₂(0), such that, for every M, eventually M (1 − p) ≤ q, and, for every M, eventually M (1 − p₂) ≤ q₂. -/
theorem fs_rev_{nm.lower()}_two_decay :
    ∃ f p q f₂ p₂ q₂ : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-{BN} / {BD}) * (1 - p η ^ 2)) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - (-{BN} / {BD}) * (1 - p₂ η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ f₂ 0 = 0 ∧ p₂ 0 = 0 ∧
      Tendsto p atTop (𝓝 1) ∧ Tendsto p₂ atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧ (∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧ (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) ∧
      q 0 ≠ q₂ 0 := {pr2}
""")
imports = ['import Mathlib'] + (['import Checked.FSRev.RAssemble', 'import Checked.FalknerSkan.NegWallShearRows',
    'import Work.FalknerSkan.AttachedRows'] + [f'import Checked.FSRev.R{NAMES[t]}{s}' for t in ('15', '17', '18', '19')
    for s in ('Over', 'Slow', 'Tube')] if mode == 'prove' else [])
hdr = '''
/-!
# Falkner–Skan reversed-flow rows β = −0.15, −0.17, −0.18, −0.19: wall-shear windows of the second branch (FROZEN, run 2026-11-12T1828Z; statements unchanged, proofs added)

Parts 2/5. The statements `fs_neg1988_reversed` and `fs_neg1988_two_decay` of `Work/FalknerSkan/Neg1988Rev.lean`
(blind-restated and closed in run 2026-11-11T1228Z) with β and the window replaced (ten decimals), emitted by
`runs/2026-11-12T1828Z/scripts/make_rev_rows.py` from `runs/2026-11-12T1828Z/scripts/rows_rev.json` (float shooting
`shoot_rev.py`: q(0) ≈ −0.13342123790, −0.11422723910, −0.09769206013, −0.07133590600).
The rows −0.17, −0.18, −0.19 are the attached rows of `Checked/FalknerSkan/NegWallShearRows.lean`; there the class
also asks q > 0, and these solutions show that hypothesis is needed. Do not change the statements; prove them.
-/

namespace Work.FalknerSkan.ReversedRows

open Set Filter Topology

'''
(R / 'Work/FalknerSkan/ReversedRows.lean').write_text('\n'.join(imports) + '\n' + hdr + '\n'.join(body) + '\nend Work.FalknerSkan.ReversedRows\n')
print('ok', mode)
