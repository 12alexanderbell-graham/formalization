#!/usr/bin/env python3
"""Reader pages for test L2R (run 2026-11-19T0828Z): arm L2 of make_pages.py for readers r48-r50.
Usage: make_pages_r.py <commit> <outdir>"""
import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).parent))
import make_pages as M

M.READERS = {"r48": "L2", "r49": "L2", "r50": "L2"}
if __name__ == "__main__":
    M.main()
