#!/usr/bin/env python3
"""Check a commit message before committing (run 2026-11-18T1828Z, annex LIV; see LEDGER).

Why: GitHub skips every workflow of a push whose head commit message contains a skip token
ANYWHERE in it, even inside a quotation. Run 2026-11-18T1628Z's final commit 1473ec0 described the
new PROMPT note "intermediate pushes [skip ci]" in its message, so the promotion of
`bonnor_ebert_count` was pushed with no CI run at all and nobody noticed until the next run.

Usage:
  python3 scripts/check_commit_msg.py --final <message file>   # a push that must run CI: no skip token
  python3 scripts/check_commit_msg.py --skip  <message file>   # an intermediate push: exactly the token
  python3 scripts/check_commit_msg.py --selftest
Exit 0 when the message is right for its kind, 1 otherwise.

--final also checks the index (run 2026-11-19T1828Z, annex LIV): run it AFTER `git add`. It fails when a
tracked file has unstaged changes or nothing is staged. Why: that run's final commit 88d46d6 carried only
the LOCK removal, because one `git add` naming the already removed LOCK aborted the whole add and the
commit ran anyway; the relock, TRUST_MAP and every record went out one commit later and the CI run of
88d46d6 had to be cancelled. CHECK_COMMIT_MSG_NO_INDEX=1 skips this part (message-only check).
"""
import os
import re
import subprocess
import sys

# GitHub's documented skip tokens (case-insensitive), plus the trailer form.
TOKENS = re.compile(
    r"\[\s*(skip ci|ci skip|no ci|skip actions|actions skip)\s*\]|^skip-checks:\s*true\s*$",
    re.IGNORECASE | re.MULTILINE,
)


def check(kind: str, text: str) -> list[str]:
    hits = [m.group(0) for m in TOKENS.finditer(text)]
    if kind == "final" and hits:
        return [f"skip token {h!r} in a message that must run CI: GitHub would skip the whole run "
                f"(write 'skip-ci marker' or similar instead)" for h in hits]
    if kind == "skip" and not hits:
        return ["no skip token in an intermediate commit: this push would cancel pending CI jobs"]
    return []


def selftest() -> int:
    cases = [
        ("final", "Run X final: records\n\nCo-Authored-By: a", True),
        ("final", "Run X final: PROMPT notes (intermediate pushes [skip ci]; …)", False),
        ("final", "Run X final: notes [CI Skip] here", False),
        ("final", "Run X final\n\nskip-checks: true\n", False),
        ("final", "Run X final: intermediate pushes carry the skip-ci marker", True),
        ("skip", "Run X: take LOCK [skip ci]", True),
        ("skip", "Run X: take LOCK", False),
    ]
    bad = 0
    for kind, text, ok in cases:
        got = not check(kind, text)
        if got != ok:
            print(f"selftest FAILED: {kind} {text!r}: expected {'pass' if ok else 'fail'}")
            bad += 1
    print(f"selftest: {len(cases) - bad}/{len(cases)} controls behave")
    return 1 if bad else 0


def index_errors() -> list[str]:
    """A final commit carries the whole work: nothing unstaged in tracked files, something staged."""
    errs = []
    unstaged = subprocess.run(["git", "diff", "--name-only"], capture_output=True, text=True)
    if unstaged.returncode != 0:
        return [f"git diff failed: {unstaged.stderr.strip()}"]
    if unstaged.stdout.strip():
        errs.append("final commit: tracked files with unstaged changes (git add them first): "
                    + ", ".join(unstaged.stdout.split()[:10]))
    staged = subprocess.run(["git", "diff", "--cached", "--quiet"])
    if staged.returncode == 0:
        errs.append("final commit: nothing staged")
    return errs


SCANNED = re.compile(r"^(STATE\.md|README\.md|BLUEPRINT\.md|runs/[^/]+/README\.md)$")


def mention_errors() -> list[str]:
    """Run 2026-11-25T0228Z (annex LIV): run 2026-11-25T0028Z ran records_check, then rewrote its run README's front
    page, which named two headlines in words outside the mention vocabulary; the checked job of its final push failed
    on check_headline_mentions.py alone, and the PROVED reading of a promotion waited another run. So a final commit
    that stages STATE.md, README.md, BLUEPRINT.md or a run README reruns that check (about a minute) against
    origin/main (every line new since the last push), with the stale-status part off (it needs the green base;
    records_check.py runs it). CHECK_COMMIT_MSG_NO_MENTIONS=1 skips it."""
    if os.environ.get("CHECK_COMMIT_MSG_NO_MENTIONS") == "1":
        return []
    staged = subprocess.run(["git", "diff", "--cached", "--name-only"], capture_output=True, text=True).stdout.split()
    if not any(SCANNED.match(p) for p in staged):
        return []
    r = subprocess.run([sys.executable, "scripts/trust/check_headline_mentions.py", "--base", "origin/main",
                        "--no-stale"], capture_output=True, text=True,
                       cwd=os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    if r.returncode == 0:
        return []
    return ["final commit: check_headline_mentions.py fails on lines new since origin/main (CI's frozen step would "
            "fail):"] + ["  " + l for l in r.stdout.splitlines() if ": M" in l][:12]


def main(argv: list[str]) -> int:
    if argv[1:] == ["--selftest"]:
        return selftest()
    if len(argv) != 3 or argv[1] not in ("--final", "--skip"):
        print(__doc__)
        return 2
    with open(argv[2], encoding="utf-8") as f:
        text = f.read()
    errs = check(argv[1][2:], text)
    if argv[1] == "--final" and os.environ.get("CHECK_COMMIT_MSG_NO_INDEX") != "1":
        errs += index_errors()
        errs += mention_errors()
    for e in errs:
        print(e)
    return 1 if errs else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
