#!/usr/bin/env python3
"""Measurement only (run 2026-11-20T1228Z): sum the `ndprof <us> <name>` lines of a profiled nanoda run per
module (module of each constant from ModuleOf.lean's output). Prints `<seconds> <declarations> <module>` sorted,
and the total. A constant not found (names nanoda prints differently) is reported under `?`.
Usage: aggregate.py <ndprof log> <modof.txt> > per_module.txt
"""
import collections, sys

modof = {}
with open(sys.argv[2], encoding="utf-8") as f:
    for line in f:
        m, _, n = line.rstrip("\n").partition(" ")
        modof[n] = m
tot = collections.Counter(); cnt = collections.Counter(); grand = 0
with open(sys.argv[1], encoding="utf-8", errors="replace") as f:
    for line in f:
        if not line.startswith("ndprof "):
            continue
        _, us, name = line.rstrip("\n").split(" ", 2)
        us = int(us); grand += us
        m = modof.get(name)
        if m is None and name.startswith("_private."):
            parts = name.split(".")
            if "0" in parts[1:]:
                m = ".".join(parts[1:parts.index("0", 1)])
        m = m or "?"
        tot[m] += us; cnt[m] += 1
for m, us in tot.most_common():
    print(f"{us/1e6:.1f} {cnt[m]} {m}")
print(f"# total {grand/1e6:.1f} s of worker time in declarations of at least the threshold", file=sys.stderr)
