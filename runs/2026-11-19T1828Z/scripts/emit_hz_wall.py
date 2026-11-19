#!/usr/bin/env python3
"""Run 2026-11-19T1828Z: emit a Checked cell module for the clamped Hiemenz field `vH` from a start
(S, P, A) (JSON of gen_hiemenz_wc_sp.py, mode 'under'), for the necessity witnesses of the wall conditions
f(0) = 0 and p(0) = 0 of `Checked.Hiemenz.hiemenz_over`. Copy of runs/2026-11-11T2228Z/scripts/emit_hiemenz_wc_s.py
with two conclusions instead of the event: `chainP` (every solution of the clamped field from the start has
p < 1 on the whole interval) and `boxC` (it stays inside the clamps there: `HCellWC.BoxΦ`, the pattern of
`Checked.Hiemenz.HIVP`).
Also the Homann field (seventh argument `homann`: cells of `Checked.Homann.HmCellWC`, statement `homann_over`).
usage: emit_hz_wall.py cells.json SEG out.lean ModName S_dec P_dec A_dec [homann]"""
import sys, json
from fractions import Fraction as Fr
d = json.load(open(sys.argv[1])); SEG = int(sys.argv[2]); out = sys.argv[3]; mod = sys.argv[4]
Sdec, Pdec, Adec = sys.argv[5], sys.argv[6], sys.argv[7]
fr = lambda v: Fr(v[0], v[1])
def q(x):
    x = Fr(x)
    return f"({x.numerator}/{x.denominator} : ℚ)" if x.denominator != 1 else f"({x.numerator} : ℚ)"
def ql(xs): return "[" + ", ".join(q(fr(v)) for v in xs) + "]"
cells = d['cells']; n = len(cells); L = fr(d['L']); MODE = d['mode']; assert MODE in ('under', 'over')
side = 'sideU' if MODE == 'under' else 'sideO'
endb = 'endU' if MODE == 'under' else 'endO'
endlemma = 'endS_q0' if MODE == 'under' else 'endSO_q0'
CH = 'chainP' if MODE == 'under' else 'chainQ'
assert fr(d['A']) == Fr(Adec) and fr(d['S']) == Fr(Sdec) and fr(d['P']) == Fr(Pdec)
HM = len(sys.argv) > 8 and sys.argv[8] == 'homann'
CELL = 'Checked.Homann.HmCellWC' if HM else 'Checked.Hiemenz.HCellWC'
BASE = 'Checked.Homann.HmExBase' if HM else 'Checked.Hiemenz.HExBase'
IVP = 'Checked.Homann.HmIVP' if HM else 'Checked.Hiemenz.HIVP'
NAME = 'Homann' if HM else 'Hiemenz'
Ls = q(L); Lr = f"({L.numerator} / {L.denominator} : ℝ)" if L.denominator != 1 else f"({L.numerator} : ℝ)"
start = f"({Sdec}, {Pdec}, {Adec})"
lines = [f"import {IVP}", "",
 f"/-! Necessity witnesses for the wall conditions of the {NAME} {'overshoot' if MODE == 'under' else 'undershoot'} statement, `{mod}`: generated cells",
 f"(`runs/2026-11-19T1828Z/scripts/{'gen_k_wc_sp.py' if HM else 'gen_hiemenz_wc_sp.py'}`, then `emit_hz_wall.py`) for the clamped {NAME} field",
 "from a start with a nonzero wall value of f or of its derivative, on the whole certified window; every side",
 f"condition is checked by kernel evaluation. The {'velocity stays below one' if MODE == 'under' else 'shear stays positive'} and the clamps stay inactive. -/", "",
 f"namespace Checked.Trust.{mod}", f"open Set Checked.Sim {CELL} {BASE}", ""]
keys = ['t0', 'h', 'δ', 'ε', 'B', 'μ', 'w1', 'w2', 'r1', 'r2']
for i, c in enumerate(cells):
    lines.append(f"def c{i} : Cell := ⟨" + ", ".join(q(fr(c[k])) for k in keys) + ", " +
                 ", ".join(ql(c[k]) for k in ('pg', 'pp', 'pq')) + "⟩")
lines.append("")
segs = []; s = 0
while s < n:
    e = min(s + SEG, n); segs.append((s, e)); s = e
for j, (s, e) in enumerate(segs):
    lst = "[" + ", ".join(f"c{i}" for i in range(s, e)) + "]"
    term = f"(fun e => linkOK e c{e})" if e < n else f"({endb} {Ls})"
    lines += [f"theorem seg{j}_ok : chainS {Ls} {side} {term} {lst} = true := by", "  decide +kernel", ""]
lines += ["theorem glue {P : ℝ → Prop} {a b : ℝ} (h1 : ∀ t ∈ Icc 0 a, P t) (h2 : ∀ t ∈ Icc a b, P t) :",
 "    ∀ t ∈ Icc 0 b, P t := by",
 "  intro t ht",
 "  rcases le_total t a with h | h",
 "  · exact h1 t ⟨ht.1, h⟩",
 "  · exact h2 t ⟨h, ht.2⟩", ""]

def body(Phi, spec, concl_name, doc):
    out = [f"/-- Every solution Y of Y' = vH t Y (the clamped {NAME} field) on [0, {L}] (derivatives within the",
     f"interval) with Y(0) = {start}: {doc}. -/",
     f"theorem {concl_name} {{Y : ℝ → ℝ × ℝ × ℝ}}",
     f"    (hY : ∀ t ∈ Icc (0 : ℝ) {Lr}, HasDerivWithinAt Y (vH t (Y t)) (Icc 0 {Lr}) t)",
     f"    (h0 : Y 0 = {start}) :",
     (f"    ∀ t ∈ Icc (0 : ℝ) {Lr}, (Y t).2.1 < 1 := by" if concl_name == 'chainP' else
      f"    ∀ t ∈ Icc (0 : ℝ) {Lr}, 0 < (Y t).2.2 := by" if concl_name == 'chainQ' else
      f"    ∀ t ∈ Icc (0 : ℝ) {Lr}, BoxΦ (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) t := by"),
     f"  have hX : (({Ls} : ℚ) : ℝ) = {Lr} := by norm_num",
     f"  have hs : SolC (({Ls} : ℚ) : ℝ) 0 (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) := by",
     "    rw [hX]",
     "    exact ⟨fun t ht => (hY t ht).fst, fun t ht => (hY t ht).snd.fst, fun t ht => (hY t ht).snd.snd⟩",
     "  have z0 : ((c0.t0 : ℚ) : ℝ) = 0 := by simp [c0]",
     "  have b0 : InBox c0 (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) := by",
     "    unfold InBox; simp only [z0, h0]",
     "    simp only [V, c0, List.headD_cons]; push_cast; norm_num", ""]
    prev = "b0"; acc = None
    for j, (s, e) in enumerate(segs):
        rest = "[" + ", ".join(f"c{i}" for i in range(s + 1, e)) + "]"
        if e < n:
            out.append(f"  obtain ⟨b{j+1}, P{j}⟩ := segS_q0 (Φ := {Phi}) {spec} c{e} {rest} c{s} seg{j}_ok hs {prev}")
            prev = f"b{j+1}"
        else:
            out.append(f"  obtain ⟨-, P{j}⟩ := {endlemma} (Φ := {Phi}) {spec} {rest} c{s} seg{j}_ok hs {prev}")
        if j == 0:
            out.append("  rw [z0] at P0"); acc = "P0"
        else:
            out.append(f"  have A{j} := glue {acc} P{j}"); acc = f"A{j}"
    out += [f"  rw [hX] at {acc}", f"  exact {acc}", ""]
    return out

if MODE == 'under':
    lines += body("(fun _ p _ t => p t < 1)", "(fun c hok hsd => sideU_spec c hok hsd)", "chainP",
                  "the velocity p stays below one on the whole interval")
else:
    lines += body("(fun _ _ q t => 0 < q t)", "(fun c hok hsd => sideO_spec c hok hsd)", "chainQ",
                  "the shear q stays positive on the whole interval")
lines += body("BoxΦ", "(fun c hok _ => box_spec c hok)", "boxC",
              "every component stays inside the clamps on the whole interval")
lines += [f"end Checked.Trust.{mod}", ""]
open(out, 'w').write("\n".join(lines))
print("wrote", out, n, "cells", len(segs), "segments")
