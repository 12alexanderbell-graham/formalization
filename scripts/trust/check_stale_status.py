#!/usr/bin/env python3
"""A forward-looking status left standing after the judge has spoken (run 2026-11-18T2028Z, part 3; see LEDGER).

Why: reader test L of run 2026-11-18T2028Z (`runs/2026-11-18T2028Z/t5/READERS.md`): two of three blind readers named
STATE.md's heading "… PROVED once a main run is green on every job (read next run)" for
`gelfand_pde_radial_many_centre` as the reason not to trust STATE.md's status words — the heading had been stale for
three days: main runs green on every job had judged that promotion since 2026-11-18 (44217681379 of fa47717, 44275141268
of 7d5b41c), and five such headings (promotions of 2026-11-11 and 2026-11-15) were still standing. Nobody's job was to
come back to them.

Rule: a level-2 heading of STATE.md carrying the pending template ("PROVED once a main run is green on every job" or
"PROVED once CI is green on every job") is STALE when every registered headline named in backticks in its section
(heading to the next level-2 heading) entered `scripts/trust/headlines.txt` in a commit that is an ancestor of, or
equal to, BASE — the newest ancestor of HEAD whose whole workflow run concluded success (`scripts/ci_changes.py`),
i.e. a main run green on every job has judged the promotion. Then the heading must carry the judged template
("PROVED (CI <run> of <sha>, a descendant, green on every job …)"). A section that names no registered headline is
not judged by this rule.

Usage: check_stale_status.py --base SHA [--run ID]   (CI: base of the push; the message names the run if given)
       check_stale_status.py --selftest
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HEADS = "scripts/trust/headlines.txt"
PENDING = re.compile(r"PROVED once (?:a main run|CI) is green on every job")


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)


def registered():
    return [l.strip() for l in (ROOT / HEADS).read_text(encoding="utf-8").splitlines()
            if l.strip() and not l.startswith("#")]


def sections(text):
    """(heading line number, heading, section text) for every level-2 heading"""
    lines = text.splitlines()
    idx = [i for i, l in enumerate(lines) if l.startswith("## ")] + [len(lines)]
    return [(idx[k] + 1, lines[idx[k]], "\n".join(lines[idx[k]:idx[k + 1]])) for k in range(len(idx) - 1)]


def named(section, heads):
    code = set(re.findall(r"`([^`]+)`", section))
    out = []
    for h in heads:
        last = h.split(".")[-1]
        if any(c == h or c == last or c.endswith("." + last) for c in code):
            out.append(h)
    return out


def intro_commit(h):
    r = git("log", "--format=%H", "-S", h, "--", HEADS)
    shas = [s for s in r.stdout.split() if s]
    return shas[-1] if shas else None


def is_ancestor(a, b):
    return git("merge-base", "--is-ancestor", a, b).returncode == 0


def findings(text, heads, intro, judged):
    out = []
    for n, head, sec in sections(text):
        if not PENDING.search(head):
            continue
        hs = named(sec, heads)
        if not hs:
            continue
        commits = [intro(h) for h in hs]
        if all(c is not None and judged(c) for c in commits):
            out.append((n, head, hs))
    return out


def selftest():
    heads = ["Checked.A.old_one", "Checked.B.new_one", "Records.F1_x"]
    text = "\n".join([
        "# STATE", "",
        "## Old (run X): promoted to Checked; PROVED once a main run is green on every job (read next run)",
        "- headline `Checked.A.old_one`; see also `F1_x`.", "",
        "## New (run Y): promoted to Checked; PROVED once a main run is green on every job",
        "- headline `Checked.B.new_one`, extends `old_one`.", "",
        "## Judged (run Z): PROVED (CI 1 of abcdef1 green on every job)", "- `old_one`", "",
        "## Nameless (run W): PROVED once CI is green on every job", "- no backticked headline here", "",
    ])
    intro = {"Checked.A.old_one": "a", "Checked.B.new_one": "b", "Records.F1_x": "a"}.get
    fails = 0
    got = findings(text, heads, intro, lambda c: c == "a")
    if [g[0] for g in got] != [3]:
        print(f"selftest FAIL: expected only the old heading (line 3) stale, got {got}")
        fails += 1
    got = findings(text, heads, intro, lambda c: c in ("a", "b"))
    if [g[0] for g in got] != [3, 6]:
        print(f"selftest FAIL: expected lines 3 and 6 stale once both are judged, got {got}")
        fails += 1
    if findings(text, heads, intro, lambda c: False):
        print("selftest FAIL: nothing judged, nothing stale")
        fails += 1
    print(f"check_stale_status selftest: 3 controls; {'FAIL' if fails else 'ok'}")
    return 1 if fails else 0


def main(argv):
    if "--selftest" in argv:
        return selftest()
    if "--base" not in argv:
        print(__doc__)
        return 2
    if selftest():
        return 1
    base = argv[argv.index("--base") + 1]
    run = argv[argv.index("--run") + 1] if "--run" in argv else None
    if git("cat-file", "-e", base + "^{commit}").returncode != 0:
        print(f"check_stale_status: base {base} is not a commit here (fetch-depth 0 needed); FAIL")
        return 1
    heads = registered()
    cache = {}

    def intro(h):
        if h not in cache:
            cache[h] = intro_commit(h)
        return cache[h]
    text = (ROOT / "STATE.md").read_text(encoding="utf-8")
    got = findings(text, heads, intro, lambda c: is_ancestor(c, base))
    for n, head, hs in got:
        print(f"STATE.md:{n}: STALE pending status: {', '.join(h.split('.')[-1] for h in hs)} entered the registry in "
              f"an ancestor of {base[:12]}{f' (run {run})' if run else ''}, whose run is green on every job: write "
              f"'PROVED (CI <run> of <sha>, a descendant, green on every job …)' in the heading. {head[:80]}")
    print(f"check_stale_status (base {base[:12]}): {len(got)} finding(s); {'FAIL' if got else 'ok'}")
    return 1 if got else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
