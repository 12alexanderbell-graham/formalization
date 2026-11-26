#!/usr/bin/env python3
"""Reader-test pages for run 2026-11-26T2028Z (brief: runs/2026-11-26T2028Z/t5/reader_brief.md).

Each page: CLAIMS_READER.md's header up to the notation paragraph, then the section of one headline.
Usage: make_pages.py <old commit> <out dir> [headline]
"""
import re
import subprocess
import sys


def page(text, head):
    hdr = text.split("\nNotation (Lean/Mathlib", 1)[0].rstrip() + "\n"
    secs = re.split(r"\n(?=## `)", text)
    sec = [s for s in secs if s.startswith(f"## `{head}`")]
    assert len(sec) == 1, head
    return hdr + "\n" + sec[0].rstrip() + "\n"


def main():
    old, out = sys.argv[1], sys.argv[2]
    head = sys.argv[3] if len(sys.argv) > 3 else "rob_state40"
    old_txt = subprocess.run(["git", "show", f"{old}:CLAIMS_READER.md"], capture_output=True, text=True,
                             check=True).stdout
    new_txt = open("CLAIMS_READER.md").read()
    for name, t in (("page_old.md", old_txt), ("page_new.md", new_txt)):
        with open(f"{out}/{name}", "w") as f:
            f.write(page(t, head))


if __name__ == "__main__":
    main()
