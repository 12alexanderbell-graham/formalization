#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])

def rep(path, old, new):
    p = root / path
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (path, old)
    p.write_text(s.replace(old, new), encoding="utf-8")

def append(path, text):
    p = root / path
    s = p.read_text(encoding="utf-8")
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text, encoding="utf-8")

rep('README.md', '- Results that passed the checker: `Checked/`', '- Results that passed the checker: `Checked/`\n- Rigorous simulation (`Checked/Sim/`): a general validated ODE solver (rational Taylor cells, exact defect bounds, Grönwall; no floating point trusted). It certifies the full oscillation period of the Duffing oscillator for every amplitude and hardening, and the Michaelis–Menten half-conversion time for any rate constants and enzyme loading, over arbitrary time horizons; the output was also cross-checked by outside experts (blind comparison complete, nothing missed).')
