"""Emit the proof of `duffing_first_zero` (chaining the 24 cell steps and the sign argument)
from cert.json; prints Lean text that replaces the `sorry` in Work/Sim/Duffing.lean."""
import json, sys
from fractions import Fraction as F

cert = json.load(open(sys.argv[1]))
cells = cert['cells']
m = cert['m']           # cells 0..m-1: positivity by crude lower bound
NC = len(cells)
LO, HI = F(1192005, 10 ** 6), F(1192006, 10 ** 6)


def r(f):
    f = F(f)
    return f"({f.numerator} : ℝ)" if f.denominator == 1 else f"({f.numerator}/{f.denominator} : ℝ)"


def T(i):
    return r(F(i, 20)) if i else "(0 : ℝ)"


def ev(p, s):
    acc = F(0)
    for c in reversed(p):
        acc = F(c) + s * acc
    return acc


L = []
A = L.append
A("  have hbox := DuffingCell.in_box hx0 hv0 hd")
A("  have sub : ∀ a b : ℝ, 0 ≤ a → b ≤ 6 / 5 → ∀ t ∈ Icc a b, t ∈ Icc (0 : ℝ) (6 / 5) :=")
A("    fun a b ha hb t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩")
for i in range(NC):
    args = (f"(fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) "
            f"(fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) "
            f"(fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht))")
    if i == 0:
        A(f"  have s0 := DuffingCerts.step0 (x := x) (v := v) {args} (by rw [hx0]; norm_num) (by rw [hv0]; norm_num)")
    else:
        A(f"  have s{i} := DuffingCerts.step{i} (x := x) (v := v) {args} s{i-1}.2.1 s{i-1}.2.2")
last = NC - 1
lc = cells[last]
A(f"  have hdl : ∀ t ∈ Icc {T(last)} {T(last+1)}, HasDerivWithinAt x (v t) (Icc {T(last)} {T(last+1)}) t :=")
A(f"    fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))")
A(f"  have hneg := neg_cell DuffingCerts.pv{last} _ _ rfl (fun t ht => (s{last}.1 t ht).2) (by norm_num [evalQ])")
A(f"  have hanti := anti_of_neg hdl hneg")
xlo = ev(lc['px'], LO - F(last, 20))
xhi = ev(lc['px'], HI - F(last, 20))
A(f"  have hPlo : evalQ DuffingCerts.px{last} ((1192005 / 1000000 : ℝ) - {T(last)}) = {r(xlo)} := by")
A(f"    norm_num [DuffingCerts.px{last}, evalQ]")
A(f"  have hPhi : evalQ DuffingCerts.px{last} ((1192006 / 1000000 : ℝ) - {T(last)}) = {r(xhi)} := by")
A(f"    norm_num [DuffingCerts.px{last}, evalQ]")
A(f"  have elo := (s{last}.1 (1192005 / 1000000) ⟨by norm_num, by norm_num⟩).1")
A(f"  have ehi := (s{last}.1 (1192006 / 1000000) ⟨by norm_num, by norm_num⟩).1")
A(f"  rw [hPlo, abs_le] at elo")
A(f"  rw [hPhi, abs_le] at ehi")
A(f"  have xlo : 0 < x (1192005 / 1000000) := by linarith [elo.1]")
A(f"  refine ⟨?_, by linarith [ehi.2]⟩")
for i in range(m):
    A(f"  have P{i} := pos_cell DuffingCerts.px{i} _ _ rfl (fun t ht => (s{i}.1 t ht).1) (by norm_num [evalQ])")
A("  intro t ht")
for i in range(m):
    A(f"  rcases le_total t {T(i+1)} with h{i} | h{i}")
    lower = "ht.1" if i == 0 else f"h{i-1}"
    A(f"  · exact P{i} t ⟨{lower}, h{i}⟩")
# remaining: t in [m/20, LO], requires m == last
assert m == last, (m, last)
A(f"  exact xlo.trans_le (hanti ⟨h{m-1}, by linarith [ht.2]⟩ ⟨by norm_num, by norm_num⟩ ht.2)")
print("\n".join(L))
