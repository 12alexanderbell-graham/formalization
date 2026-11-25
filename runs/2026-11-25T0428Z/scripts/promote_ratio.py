#!/usr/bin/env python3
"""Promotion of `gelfand_turning_ratio` (run 2026-11-25T0428Z).

Copies the files prepared in `runs/2026-11-25T0428Z/promote/` into the tree and registers the headline,
its non-vacuity witness and its literal readings. Run from the repository root; idempotent.

  python3 runs/2026-11-25T0428Z/scripts/promote_ratio.py

What it does (each step a no-op if already done):
 1. copies `promote/Checked/Math/GelfandRatioCore.lean`, `promote/Checked/Math/GelfandTurningRatio.lean`,
    `promote/Checked/Trust/SecondReadingGelfandTurnRatio.lean`, `promote/Checked/Trust/NecessityBS.lean`,
    `promote/Work/Math/GelfandTurningRatio.lean`, `promote/Work/Math/GelfandTurningRatioBlindClosed.lean`;
 2. adds the four `Checked.*` imports to `Checked.lean` and the two `Work.*` imports to `Work.lean`
    (each after the import of the module it extends, so the files stay grouped);
 3. appends the headline to `scripts/trust/headlines.txt`;
 4. appends the non-vacuity witness of `promote/witness_snippet.lean` to `Checked/Trust/Witnesses.lean`
    before its final `end`, with the import of the headline's module;
 5. appends the literal readings line: the readings registered for the parent headline
    `Checked.Math.GelfandExtrema.gelfand_extrema` (same statement up to the new conjunct) plus the new
    `Checked.Trust.SecondReading.gelfandTurnRatio`.
"""
import pathlib
import shutil

ROOT = pathlib.Path(__file__).resolve().parents[3]
P = ROOT / "runs/2026-11-25T0428Z/promote"
HEADLINE = "Checked.Math.GelfandTurningRatio.gelfand_turning_ratio"
PARENT = "Checked.Math.GelfandExtrema.gelfand_extrema"

COPIES = [
    ("Checked/Math/GelfandRatioCore.lean", None),
    ("Checked/Math/GelfandTurningRatio.lean", None),
    ("Checked/Trust/SecondReadingGelfandTurnRatio.lean", None),
    ("Checked/Trust/NecessityBS.lean", None),
    ("Work/Math/GelfandTurningRatio.lean", None),
    ("Work/Math/GelfandTurningRatioBlindClosed.lean", None),
]

IMPORTS = [
    ("Checked.lean", "import Checked.Math.GelfandRatioCore", "import Checked.Math.GelfandExtremaMain"),
    ("Checked.lean", "import Checked.Math.GelfandTurningRatio", "import Checked.Math.GelfandRatioCore"),
    ("Checked.lean", "import Checked.Trust.SecondReadingGelfandTurnRatio",
     "import Checked.Trust.SecondReadingGelfandSeventhTurn"),
    ("Checked.lean", "import Checked.Trust.NecessityBS", "import Checked.Trust.NecessityBR"),
    ("Work.lean", "import Work.Math.GelfandTurningRatio", "import Work.Math.GelfandTurningValuesSeven"),
    ("Work.lean", "import Work.Math.GelfandTurningRatioBlindClosed", "import Work.Math.GelfandTurningRatio"),
]


def copy_files() -> None:
    for rel, _ in COPIES:
        src = P / rel
        dst = ROOT / rel
        if dst.exists() and dst.read_text() == src.read_text():
            print("same", rel)
            continue
        shutil.copyfile(src, dst)
        print("copied", rel)


def add_import(index: str, line: str, after: str) -> None:
    path = ROOT / index
    text = path.read_text()
    if line + "\n" in text:
        print("import present", line)
        return
    assert after + "\n" in text, (index, after)
    text = text.replace(after + "\n", after + "\n" + line + "\n", 1)
    path.write_text(text)
    print("import added", line)


def add_headline() -> None:
    path = ROOT / "scripts/trust/headlines.txt"
    lines = path.read_text().splitlines()
    if HEADLINE in lines:
        print("headline present")
        return
    lines.append(HEADLINE)
    path.write_text("\n".join(lines) + "\n")
    print("headline added")


def add_witness() -> None:
    path = ROOT / "Checked/Trust/Witnesses.lean"
    text = path.read_text()
    snippet = (P / "witness_snippet.lean").read_text()
    if "theorem gelfand_turning_ratio :" in text:
        print("witness present")
    else:
        tail = "\nend Checked.Trust.NV\n"
        assert text.endswith(tail)
        text = text[: -len(tail)] + snippet + tail
        print("witness added")
    imp = "import Checked.Math.GelfandTurningRatio\n"
    if imp not in text:
        anchor = "import Checked.Math.GelfandTurningValuesSeven\n"
        assert anchor in text
        text = text.replace(anchor, anchor + imp, 1)
        print("witness import added")
    path.write_text(text)


def add_readings() -> None:
    path = ROOT / "scripts/trust/literal_readings.txt"
    lines = path.read_text().splitlines()
    if any(l.split(" ")[0] == HEADLINE for l in lines):
        print("readings present")
        return
    parent = [l for l in lines if l.split(" ")[0] == PARENT]
    assert len(parent) == 1, parent
    consts = parent[0].split(" ")[1:]
    consts.append("Checked.Trust.SecondReading.gelfandTurnRatio")
    lines.append(" ".join([HEADLINE] + consts))
    path.write_text("\n".join(lines) + "\n")
    print("readings added")


if __name__ == "__main__":
    copy_files()
    for index, line, after in IMPORTS:
        add_import(index, line, after)
    add_headline()
    add_witness()
    add_readings()
