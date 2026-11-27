#!/usr/bin/env python3
"""Verbatim source transcriptions for blind readers (run 2026-11-27T0428Z, annex LIV; copied here from
runs/2026-11-27T0428Z/scripts/ by run 2026-11-27T0828Z, the run folder's copy kept as the record).

Why: blind readers in unattended sessions cannot fetch the web (WebFetch refused, PROVENANCE_REQUIRED), so on
links that depend on a named source's convention their readings were memory (run 2026-11-27T0228Z: two of
two readers had the opposite Ricci sign of Bamba et al. 2012 §XI). The orchestrator can fetch arXiv's LaTeX
source; this script writes verbatim line ranges of it, with the e-print's sha256 and the file's line numbers,
into a Markdown file for `runs/<run>/sources/` (outside the reader's folder, check_blind_route B5).

  python3 source_excerpt.py <arxiv id, e.g. 1205.3421v3> <tex file inside the e-print> <out.md> \
      "<heading>:<first>-<last>" ["<heading>:<first>-<last>" ...]

The e-print is untrusted: it is downloaded to a fresh temporary directory, extracted with tarfile's 'data'
filter (no links, no paths outside), and only read as text. Nothing is executed. CR line endings are dropped
(the lines are otherwise byte-identical; checked on 1205.3421v3 lines 10030-10036).
"""
import gzip, hashlib, io, subprocess, sys, tarfile, tempfile
from pathlib import Path


def main():
    if len(sys.argv) < 5:
        sys.exit(__doc__)
    aid, texname, out, ranges = sys.argv[1], sys.argv[2], Path(sys.argv[3]), sys.argv[4:]
    url = f"https://arxiv.org/e-print/{aid}"
    with tempfile.TemporaryDirectory() as d:
        blob = Path(d) / "eprint"
        subprocess.run(["curl", "-sSfL", "--retry", "3", "-o", str(blob), url], check=True)
        raw = blob.read_bytes()
        sha = hashlib.sha256(raw).hexdigest()
        data = gzip.decompress(raw) if raw[:2] == b"\x1f\x8b" else raw
        try:
            with tarfile.open(fileobj=io.BytesIO(data)) as tf:
                tf.extractall(Path(d) / "x", filter="data")
            tex = (Path(d) / "x" / texname).read_text(encoding="utf-8", errors="replace")
        except tarfile.ReadError:  # single-file e-print
            tex = data.decode("utf-8", errors="replace")
    lines = tex.splitlines()
    parts = [f"# Source transcription: arXiv:{aid}, `{texname}`", "",
             f"Verbatim excerpts of the LaTeX source fetched from {url} (sha256 {sha[:16]}…). Line numbers are of "
             f"`{texname}`. Nothing is added; `%` lines are LaTeX comments in the source."]
    for r in ranges:
        head, span = r.rsplit(":", 1)
        a, b = (int(x) for x in span.split("-"))
        parts += ["", f"## {head}, lines {a}–{b}", "```latex", *lines[a - 1:b], "```"]
    out.write_text("\n".join(parts) + "\n", encoding="utf-8")
    print(f"wrote {out} ({sum(1 for _ in ranges)} excerpts, e-print sha256 {sha[:16]})")


if __name__ == "__main__":
    main()
