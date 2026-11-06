#!/usr/bin/env python3
import sys, pathlib
ROOT = pathlib.Path(sys.argv[1])

def rep(rel, old, new):
    p = ROOT / rel
    t = p.read_text(encoding="utf-8")
    assert t.count(old) == 1, (rel, old[:60], t.count(old))
    p.write_text(t.replace(old, new), encoding="utf-8")

def append(rel, text):
    p = ROOT / rel
    t = p.read_text(encoding="utf-8")
    if t and not t.endswith("\n"):
        t += "\n"
    p.write_text(t + text, encoding="utf-8")

def create(rel, text):
    p = ROOT / rel
    assert not p.exists(), rel
    p.write_text(text, encoding="utf-8")

rep("STATE.md",
    "- **PROVED in Work + AUDITED** (parts 2/1, run 2026-11-06T1828Z; local build, axioms standard; CI of 7c25ba6/8081e34: next run) `Work.Math.ThomasFermi.tf_initial_slope` (see the Thomas–Fermi section).",
    "- **PROVED** (parts 2/1, run 2026-11-06T1828Z; promoted to Checked, **CI green on every job**, non-vacuity witnessed, a rigorous enclosure for every neutral atom, so the Thomas–Fermi energy constant of neutral atoms is now certified) `Work.Math.ThomasFermi.tf_initial_slope` (see the Thomas–Fermi section).")
