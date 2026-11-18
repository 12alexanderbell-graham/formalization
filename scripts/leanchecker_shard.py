#!/usr/bin/env python3
"""Kernel replay of the Checked library with the toolchain's leanchecker, shard I of K (part of the judge,
annex 39.5; run 2026-11-18T1828Z, see LEDGER).

Why: lean-action's leanchecker step ran `lake env leanchecker Checked` inside the checked job on one thread
(LEAN_NUM_THREADS=1); it replays every module of Checked from its imports and took 47 min on 2026-11-12 and
140 min on 2026-11-18 (job 134891775171), putting the checked job at 180-211 min of its 240-min limit and
holding every later checked job pending for 3 h. The same check is now split into K jobs that run in parallel.

What it checks (unchanged): `leanchecker M1 … Mn` replays, for each listed module, every declaration the module
adds into the environment of its imports, with the Lean kernel (LeanChecker.lean, `replayFromImports`), and
fails if any module's olean is missing or any declaration is rejected. The module list of Checked is every
tracked `Checked/**/*.lean` plus `Checked.lean` (the files `lake build Checked` builds; an untracked or
unimported file would have no olean and fail the shard, never pass silently). Shard i takes the modules whose
FNV-1a hash (as in scripts/nanoda/ShardMain.lean) is i mod K, so the K shards partition the module list:
K green shards replay every module the single `leanchecker Checked` call replayed.

Timing (run 2026-11-18T2228Z, annex LIV): the shard's modules are replayed in consecutive groups of GROUP modules
(one leanchecker call per group, same modules, same order), and each group's wall time is printed
(`leanchecker-time <seconds> <modules>`). Why: in branch trial 44373171551 shard 2 replayed for 182 min and shards
0, 1, 3 for 44-48 min (job limit 240 min); olean sizes do not predict the difference, so the partition can only be
balanced on measured times, which one call per shard does not report. Every module of the shard is still replayed and
any failing group fails the shard.

Usage:
  python3 scripts/leanchecker_shard.py I K           # run leanchecker on shard I of K (needs `lake build Checked`)
  python3 scripts/leanchecker_shard.py --list I K    # print the modules of shard I
  python3 scripts/leanchecker_shard.py --selftest    # the K lists partition the module list, none empty
"""
import subprocess
import sys
import time

GROUP = 8


def modules() -> list[str]:
    out = subprocess.run(["git", "ls-files", "Checked.lean", "Checked/*.lean"], capture_output=True,
                         text=True, check=True).stdout.split()
    mods = []
    for p in out:
        assert p.endswith(".lean"), p
        mods.append(p[: -len(".lean")].replace("/", "."))
    if "Checked" not in mods:
        raise SystemExit("Checked.lean is not tracked")
    return sorted(set(mods))


def shard_of(name: str, k: int) -> int:
    h = 14695981039346656037
    for c in name:
        h = ((h ^ ord(c)) * 1099511628211) & 0xFFFFFFFFFFFFFFFF
    return h % k


def shard(i: int, k: int) -> list[str]:
    return [m for m in modules() if shard_of(m, k) == i]


def selftest() -> int:
    mods = modules()
    for k in (1, 2, 4):
        lists = [shard(i, k) for i in range(k)]
        flat = [m for l in lists for m in l]
        if sorted(flat) != mods or len(set(flat)) != len(flat):
            print(f"selftest FAILED: the {k} shards do not partition the {len(mods)} modules")
            return 1
        if any(not l for l in lists):
            print(f"selftest FAILED: an empty shard at k = {k}")
            return 1
    print(f"selftest: {len(mods)} modules; shards of 4: {[len(shard(i, 4)) for i in range(4)]}")
    return 0


def main(argv: list[str]) -> int:
    if argv[1:] == ["--selftest"]:
        return selftest()
    if len(argv) == 4 and argv[1] == "--list":
        print("\n".join(shard(int(argv[2]), int(argv[3]))))
        return 0
    if len(argv) != 3:
        print(__doc__)
        return 2
    i, k = int(argv[1]), int(argv[2])
    if not (0 <= i < k):
        print("need 0 <= I < K")
        return 2
    mods = shard(i, k)
    if not mods:
        print(f"shard {i} of {k} is empty")
        return 1
    print(f"leanchecker shard {i} of {k}: {len(mods)} of {len(modules())} modules", flush=True)
    for g in range(0, len(mods), GROUP):
        group = mods[g:g + GROUP]
        t0 = time.monotonic()
        r = subprocess.run(["lake", "env", "leanchecker", *group])
        print(f"leanchecker-time {time.monotonic() - t0:.0f} {' '.join(group)}", flush=True)
        if r.returncode != 0:
            print(f"leanchecker shard {i} of {k} FAILED (exit {r.returncode}) in the group {' '.join(group)}")
            return 1
    print(f"leanchecker: Checked shard {i} of {k} passed ({len(mods)} modules)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
