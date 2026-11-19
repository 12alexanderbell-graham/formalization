#!/usr/bin/env python3
"""Reader pages for test L2S (run 2026-11-19T0828Z): arm L2 of make_pages.py for readers r51-r53.
Usage: make_pages_r.py <commit> <outdir>"""
import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).parent))
import make_pages as M

M.READERS = {"r51": "L2", "r52": "L2", "r53": "L2"}
if __name__ == "__main__":
    M.main()
