#!/usr/bin/env python3
"""Reader pages for test WP (run 2026-11-20T1428Z, part 3): the records as they stand, no inserted line.

Arm S: STATE.md and CLAIMS.md (= CLAIMS_READER.md), both at <commit>, unchanged. Arm G: CLAIMS.md only.
Headlines: five drawn from the listed headlines (CLAIMS_READER.md `## `name`` sections) whose name occurs in STATE.md
at <commit>, by random.Random(<seed>).sample over the sorted list; <seed> = the full hash of <commit>'s parent, so
the draw is fixed by the commit that adds the brief and cannot be chosen after seeing answers.

Usage: make_pages_WP.py <commit> <outdir>          (prints the draw, writes <outdir>/<reader>/...)
       make_pages_WP.py <commit> --draw           (prints the draw only)
"""
import pathlib, random, re, subprocess, sys

READERS = {"r75": "S", "r76": "G", "r77": "S", "r78": "S", "r79": "G", "r80": "S", "r81": "S", "r82": "G", "r83": "S"}


def git(*a):
    return subprocess.run(["git", *a], check=True, capture_output=True, text=True).stdout


def draw(commit):
    state, claims = git("show", f"{commit}:STATE.md"), git("show", f"{commit}:CLAIMS_READER.md")
    names = re.findall(r"^## `([^`]+)`", claims, re.M)
    pool = sorted(n for n in set(names) if n in state)
    seed = git("rev-parse", f"{commit}^").strip()
    return state, claims, pool, seed, random.Random(seed).sample(pool, 5)


def main():
    commit = sys.argv[1]
    state, claims, pool, seed, pick = draw(commit)
    print(f"pool {len(pool)} headlines named in STATE.md; seed {seed}; draw: {', '.join(pick)}")
    if sys.argv[2] == "--draw":
        return
    out = pathlib.Path(sys.argv[2])
    for r, arm in READERS.items():
        d = out / r
        d.mkdir(parents=True, exist_ok=True)
        (d / "CLAIMS.md").write_text(claims)
        if arm == "S":
            (d / "STATE.md").write_text(state)
    print("built", len(READERS), "reader directories from", commit)


if __name__ == "__main__":
    main()
