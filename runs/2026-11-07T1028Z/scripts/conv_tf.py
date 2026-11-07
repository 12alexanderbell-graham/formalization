#!/usr/bin/env python3
"""Convert the Thomas–Fermi barrier certificates (Checked/Math/TFCerts{Sup,Sub}*.lean, run
2026-11-06T1828Z) to the kernel-evaluated form of Checked/Math/TFCellQ.lean.

Reads every cell's Taylor polynomials (qw_*, qp_*), start t0 and length h from the existing
modules, re-checks in exact Fractions what TFCellQ's Boolean checks will decide (cell side
conditions with the defect polynomials *recomputed* from qw, qp; links; start and end), and
emits Checked/Math/TFQData.lean: the cells as `BCell` values and one `decide +kernel` per
segment of SEG cells.

usage: conv_tf.py <repo root> <out file> [SEG]
"""
import re
import sys
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(sys.argv[1])
OUT = Path(sys.argv[2])
SEG = int(sys.argv[3]) if len(sys.argv) > 3 else 10

RAT = re.compile(r"\((-?\d+)(?:/(\d+))? : [ℚℝ]\)")


def rat(tok):
    m = RAT.fullmatch(tok.strip())
    assert m, tok
    return F(int(m.group(1)), int(m.group(2) or 1))


def parse_list(s):
    return [F(int(a), int(b or 1)) for a, b in re.findall(r"\((-?\d+)(?:/(\d+))? : ℚ\)", s)]


def lean_q(x):
    return f"({x.numerator}/{x.denominator} : ℚ)" if x.denominator != 1 else f"({x.numerator} : ℚ)"


# exact polynomial arithmetic, constant first (mirrors Checked.Sim.QPoly)
def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def psmul(c, p):
    return [c * a for a in p]


def pmul(p, q):
    r = [F(0)] * (len(p) + len(q) - 1) if p and q else []
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def pderiv(p):
    return [i * p[i] for i in range(1, len(p))]


def peval(p, x):
    r = F(0)
    for c in reversed(p):
        r = c + x * r
    return r


def qabs(p, h):
    return peval([abs(c) for c in p], h)


def lo(p, h):
    return (p[0] if p else F(0)) - h * qabs(p[1:], h)


def hi(p, h):
    return (p[0] if p else F(0)) + h * qabs(p[1:], h)


def d1(c):
    return padd(pmul(c["qw"], pderiv(c["qw"])), psmul(-1, pmul([c["t0"], F(1)], c["qp"])))


def d2(c):
    return padd(pderiv(c["qp"]), psmul(-1, psmul(2, pmul(c["qw"], pmul(c["qw"], c["qw"])))))


def read_cells(kind):
    files = sorted(ROOT.glob(f"Checked/Math/TFCerts{kind.capitalize()}*.lean"))
    defs, cells = {}, {}
    out_bounds = {}
    for f in files:
        txt = f.read_text()
        for name, body in re.findall(r"^def (q[wp]_" + kind + r"\d+) : List ℚ := \[(.*)\]$", txt, re.M):
            defs[name] = parse_list(body)
        for idx, t0, h in re.findall(
                r"(?:super|sub)_cell qw_" + kind + r"(\d+) qp_" + kind + r"\d+ \(w := W\) \(P := P\) \(t0 := (\([^)]*\))\) \(h := (\([^)]*\))\)", txt):
            cells[int(idx)] = dict(t0=rat(t0), h=rat(h))
        for idx, concl in re.findall(r"^theorem " + kind + r"(\d+) \{W P[\s\S]*?\) :\n    (.*) := by$", txt, re.M):
            pat = r"< (\(-?\d+(?:/\d+)? : ℝ\))" if kind == "sup" else r"(\(-?\d+(?:/\d+)? : ℝ\)) < [WP]"
            out_bounds[int(idx)] = [rat(x) for x in re.findall(pat, concl)]
            assert len(out_bounds[int(idx)]) == 2, concl
    n = len(cells)
    assert sorted(cells) == list(range(n)), (kind, sorted(cells)[:5])
    for i in range(n):
        cells[i]["qw"] = defs[f"qw_{kind}{i}"]
        cells[i]["qp"] = defs[f"qp_{kind}{i}"]
    return [cells[i] for i in range(n)], out_bounds


def check(kind, cells, T, end_a, end_b):
    up = kind == "sup"
    for i, c in enumerate(cells):
        assert 0 <= c["t0"] and 0 < c["h"] and c["t0"] + c["h"] <= T, i
        a, b = d1(c), d2(c)
        if up:
            assert lo(a, c["h"]) > 0 and lo(b, c["h"]) > 0, (kind, i)
        else:
            assert hi(a, c["h"]) < 0 and hi(b, c["h"]) < 0, (kind, i)
        ew, ep = peval(c["qw"], c["h"]), peval(c["qp"], c["h"])
        if i + 1 < len(cells):
            d = cells[i + 1]
            assert c["t0"] + c["h"] == d["t0"], i
            if up:
                assert ew <= d["qw"][0] and ep <= d["qp"][0], (kind, i)
            else:
                assert d["qw"][0] <= ew and d["qp"][0] <= ep, (kind, i)
        else:
            assert c["t0"] + c["h"] == T
            if up:
                assert ew <= end_a and ep <= end_b
            else:
                assert end_a <= ew and end_b <= ep


def emit_cell(name, c):
    qw = ", ".join(lean_q(x) for x in c["qw"])
    qp = ", ".join(lean_q(x) for x in c["qp"])
    return f"def {name} : BCell := ⟨{lean_q(c['t0'])}, {lean_q(c['h'])},\n  [{qw}],\n  [{qp}]⟩\n"


def emit_kind(kind, cells, T, end_a, end_b, lines):
    pre = "u" if kind == "sup" else "l"
    chain = "supChain" if kind == "sup" else "subChain"
    link = "supLink" if kind == "sup" else "subLink"
    endf = "supEnd" if kind == "sup" else "subEnd"
    for i, c in enumerate(cells):
        lines.append(emit_cell(f"{pre}{i}", c))
    n = len(cells)
    starts = list(range(0, n, SEG))
    for k, s in enumerate(starts):
        e = min(s + SEG, n)
        names = ", ".join(f"{pre}{i}" for i in range(s, e))
        if e < n:
            lines.append(f"theorem {pre}seg{k}_ok : {chain} {lean_q(T)} (fun e => {link} e {pre}{e}) [{names}] = true := by\n  decide +kernel\n")
        else:
            lines.append(f"theorem {pre}seg{k}_ok : {chain} {lean_q(T)} ({endf} {lean_q(T)} {lean_q(end_a)} {lean_q(end_b)}) [{names}] = true := by\n  decide +kernel\n")
    return starts


def main():
    sup, sup_b = read_cells("sup")
    sub, sub_b = read_cells("sub")
    # end values: the last generated cell's stated bounds (sup_chain then weakens them by norm_num)
    sa, sb = sup_b[len(sup) - 1]
    la, lb = sub_b[len(sub) - 1]
    check("sup", sup, F(27, 4), sa, sb)
    check("sub", sub, F(15, 2), la, lb)
    assert sup[0]["qw"][0] > 1 and sup[0]["qp"][0] == F(-158807103, 10**8)
    assert sub[0]["qw"][0] < 1 and sub[0]["qp"][0] == F(-158807102, 10**8)
    assert sa <= F(13, 625) and sb <= F(-771, 10**7) and lb >= 0
    lines = [
        "import Checked.Math.TFCellQ\n",
        "/-! Thomas–Fermi, `TFQData`: the barrier cells of both shooting directions as data, generated by `runs/2026-11-07T1028Z/scripts/conv_tf.py` from the cells of the earlier certificate modules (same Taylor polynomials, starts and lengths). Every side condition and every defect bound is decided by kernel evaluation over the rationals, one declaration per segment of cells. -/\n",
        "namespace Checked.Math.TFQData",
        "open Checked.Math.TFCellQ\n",
    ]
    us = emit_kind("sup", sup, F(27, 4), sa, sb, lines)
    ls = emit_kind("sub", sub, F(15, 2), la, lb, lines)
    lines.append("end Checked.Math.TFQData\n")
    OUT.write_text("\n".join(lines))
    print(f"sup {len(sup)} cells, segments at {us}; end ({sa}, {sb})")
    print(f"sub {len(sub)} cells, segments at {ls}; end ({la}, {lb})")


if __name__ == "__main__":
    main()
