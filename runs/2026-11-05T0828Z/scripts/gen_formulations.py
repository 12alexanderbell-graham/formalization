#!/usr/bin/env python3
"""Generate Checked/Trust/Formulations.lean (run 2026-11-05T0828Z).

For each FORMULA definition of scripts/trust/def_kinds.txt: a theorem
`agree_<short> : @<program> = @<second formulation>` proved by unfolding both sides and `ring`
(fallbacks: `field_simp; ring`, `ring_nf`), the shape StatementDeps.lean accepts as a machine-checked
blind second formulation. The blind files are copied verbatim to Checked/Trust/SecondFormulation.lean
(chemistry, data) and Checked/Trust/SecondFormulationCosmo.lean (cosmography); a pair whose
second-formulation constant is missing from them is skipped (and reported), so the generated file
always elaborates up to genuine disagreements. A failing proof is a DISAGREEMENT: investigate it,
never edit either side to agree.

Run from the repository root:  python3 runs/2026-11-05T0828Z/scripts/gen_formulations.py
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SF_FILES = ["Checked/Trust/SecondFormulation.lean", "Checked/Trust/SecondFormulationCosmo.lean"]
SF_NS = "Checked.Trust.SecondFormulation"
OUT = ROOT / "Checked/Trust/Formulations.lean"
C = "Checked.Cosmography."

# (program constant, explicit argument names (in order), implicit argument names,
#  extra program constants to unfold, extra second-formulation-side constants to unfold,
#  optional proof override (Lean tactic block after `:= by`, without the leading newline))
PAIRS = [
    (C + "CCS.correctD4", "q j s l", "", [], [], None),
    (C + "CCS.series", "d4 q j s z", "", [C + "CCS.D1", C + "CCS.D2", C + "CCS.D3"],
     ["Checked.Trust.SecondReading.D1", "Checked.Trust.SecondReading.D2", "Checked.Trust.SecondReading.D3"], None),
    (C + "BambaY.correctD2y", "q j Ω", "", [], [], None),
    (C + "BambaY.seriesY", "d2 q y", "", [C + "BambaY.D1y"], ["Checked.Trust.SecondReading.D1y"], None),
    (C + "BambaK.correctD3y", "q j s Ω", "", [C + "BambaK.printedD3y"], [], None),
    (C + "BambaK.correctD4y", "q j s l Ω", "", [C + "BambaK.printedD4y"], [], None),
    (C + "BambaK.seriesY4", "q d2 d3 d4 y", "", [C + "BambaY.D1y"], ["Checked.Trust.SecondReading.D1y"], None),
    (C + "BambaA.correctDA3", "q j s Ω", "", [C + "BambaA.printedDA3"], [], None),
    (C + "BambaA.correctDA4", "q j s l Ω", "", [C + "BambaA.printedDA4"], [], None),
    (C + "BambaZ.correctDL4z", "q j s l k", "", [C + "BambaZ.printedDL4z"], [], None),
    (C + "BambaZ.correctDA4z", "q j s l k", "", [C + "BambaZ.printedDA4z"], [], None),
    (C + "BambaZ.seriesZ", "d1 d2 d3 d4 z", "", [], [], None),
    (C + "CVdQ.correctQ2", "q j Ω", "", [], [], None),
    (C + "CVdQ.seriesQ", "d2 q y", "", [], [], None),
    (C + "FREta.correct20", "Ω", "", [], [], None),
    (C + "FREta.correct30", "Ω", "", [], [], None),
    # (C + "FRCosmo.correctR", "q j s l", "", [], [], None),  # baselined (scripts/trust/formula_baseline.txt)
    ("Checked.Chemistry.CubicEOS.cubicP", "R a b u w T v", "", [], [], None),
    ("Checked.Chemistry.CubicEOS.critCubic", "u w x", "", [], [], None),
    ("Checked.Chemistry.Coexistence.acentric", "ps pc", "", [], [], None),
    ("Checked.Data.FR13.chiSqHz", "tbl H₀ Ω", "n", [], [],
     "  funext n tbl H₀ Ω\n  simp only [Checked.Data.FR13.chiSqHz, Checked.Trust.SecondFormulation.chiSqHz]\n  refine Finset.sum_congr rfl fun i _ => ?_\n  rw [add_sub_assoc]\n  ring"),
    # margChiSq: DISAGREES for σ < 0 (program prior normaliser √(2πσ²) = |σ|√(2π), blind σ√(2π));
    # equal for σ > 0 (Checked.Trust.FormulationsCond.agree_margChiSq_pos); baselined.
    # ("Checked.Data.FR13.margChiSq", "tbl Hbar σ Ω", "n", ["Checked.Data.FR13.chiSqHz"], [SF_NS + ".chiSqHz"], None),
]

IMPORTS = ["Checked.Chemistry.CubicEOS", "Checked.Chemistry.Coexistence", "Checked.Data.FR13",
           C + "CCSLookback", C + "BambaDLy", C + "BambaCurved", C + "BambaAngular", C + "BambaZ",
           C + "CVdQ", C + "FREta", C + "FRCosmo"]

DEF = re.compile(r"^(?:noncomputable\s+)?def\s+([^\s({:]+)", re.M)


def sf_defs():
    """name -> (module, body text) for every def of the blind files present."""
    out = {}
    for rel in SF_FILES:
        p = ROOT / rel
        if not p.exists():
            continue
        text = p.read_text()
        ns = re.search(r"^namespace\s+(\S+)", text, re.M)
        if not ns or ns.group(1) != SF_NS:
            sys.exit(f"{rel}: namespace must be {SF_NS}")
        ms = list(DEF.finditer(text))
        for i, m in enumerate(ms):
            end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
            out[m.group(1)] = (rel[:-5].replace("/", "."), text[m.end():end])
    return out


def main():
    defs = sf_defs()
    mods = sorted({m for m, _ in defs.values()})
    thms, skipped = [], []
    for prog, args, impl, pextra, sextra, proof in PAIRS:
        short = prog.split(".")[-1]
        if short not in defs:
            skipped.append(prog)
            continue
        sf = f"{SF_NS}.{short}"
        body = re.sub(r"/-.*?-/", "", defs[short][1], flags=re.S)  # names in docstrings are not uses
        # helpers of the blind file and SecondReading constants the blind body names (textually)
        auto = [f"{SF_NS}.{h}" for h in defs if h != short and re.search(rf"(?<![\w.]){re.escape(h)}(?![\w'])", body)]
        auto += [f"Checked.Trust.SecondReading.{h}" for h in re.findall(r"SecondReading\.(\w+)", body)]
        unfold = [prog] + pextra + [sf] + sextra
        for a in auto:
            if a not in unfold:
                unfold.append(a)
        binders = " ".join(([impl] if impl else []) + args.split())
        tac = proof or f"  funext {binders}\n  simp only [{', '.join(unfold)}] <;> ring"
        thms.append(f"/-- `{prog}` agrees with its blind second formulation. -/\n"
                    f"theorem agree_{short} : @{prog} = @{sf} := by\n{tac}\n")
    head = "\n".join(f"import {m}" for m in mods + IMPORTS)
    doc = f"""
/-!
# Blind second formulations agree with the program's FORMULA definitions (run 2026-11-05T0828Z)

Red team J (run 2026-11-04T2228Z) showed that the name, docstring and constants of a FORMULA
definition were checked by nothing (d03: a transposed gas constant; d06: the JT inversion
temperature named `boyleT`). Each FORMULA definition a headline rests on now needs an agreement
`@program = @second formulation` here, where the right-hand side was written by a subagent that saw
only the definition's name, argument roles and conventions (never its body), and lives in a
`Checked.Trust.SecondFormulation*` module that does not reach the left-hand side
(`scripts/trust/StatementDeps.lean`; exceptions only in the shrink-only
`scripts/trust/formula_baseline.txt`). Proved by unfolding and `ring`; generated by
`runs/2026-11-05T0828Z/scripts/gen_formulations.py`.
-/

namespace Checked.Trust.Formulations

"""
    OUT.write_text(head + "\n" + doc + "\n".join(thms) + "\nend Checked.Trust.Formulations\n")
    print(f"wrote {OUT.relative_to(ROOT)}: {len(thms)} agreements; skipped (no second formulation): {skipped}")


if __name__ == "__main__":
    main()
