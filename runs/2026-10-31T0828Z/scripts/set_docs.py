"""Run 0828Z: give every headline (and the claim definitions they negate) a self-contained
plain-words docstring (pilot validation, minor defects on items 11, 15, 20, 41, 47)."""
import re, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
C = ROOT / "Checked/Cosmography"
DOCS = [
 # (file, kind, name, doc)
 ("BambaDLy.lean", "theorem", "printedD2y_fails",
  "The printed `D²_{L,y}` (Bamba et al. 2012, Eq. (10.54)) fails in every flat model, scale factor `C³`\nat `t₀` with `a(t₀) ≠ 0`, `H₀ ≠ 0` and `11 − 5q₀ + 3q₀² − j₀ ≠ 0`: the flat `d_L(y)` series with it is\nnot `d_L + o(y³)` as `t → t₀` (two-sided limit; past-only version: `printedD2y_fails_past`)."),
 ("BambaCurved.lean", "theorem", "printedD3y_fails",
  "The printed `D³_{L,y}` (Eq. (10.55)), used with the corrected `D²_{L,y}`, fails in every FLRW model of\ncurvature `K` whose scale factor is `C⁵` at `t₀` with `a(t₀) ≠ 0`, `H₀ ≠ 0` and `(Ω₀ − 1)(3q₀ − 2) ≠ 0`:\nthe `d_L(y)` series is not `d_L + o(y⁴)` as `t → t₀` (two-sided; past-only: `printedD3y_fails_past`)."),
 ("BambaCurved.lean", "theorem", "printedD4y_fails",
  "The printed `D⁴_{L,y}` (Eqs. (10.56)–(10.57)), used with the corrected `D²`, `D³`, fails in every FLRW\nmodel of curvature `K` whose scale factor is `C⁵` at `t₀` with `a(t₀) ≠ 0`, `H₀ ≠ 0` and\n`(Ω₀ − 1)²/120 + 5q₀(Ω₀ − 1)/12 ≠ 0`: the `d_L(y)` series is not `d_L + o(y⁵)` as `t → t₀`\n(two-sided; past-only: `printedD4y_fails_past`)."),
 ("BambaCurved.lean", "theorem", "bambaD3yClaim_false",
  "The review's claim (10.55) is false: it is not true that for every curvature `K` and every analytic,\neverywhere positive scale factor with `H₀ > 0` the `d_L(y)` series with the corrected `D²_{L,y}` and\nthe printed `D³_{L,y}` equals `d_L + o(y⁴)` as `t → t₀`."),
 ("BambaCurved.lean", "theorem", "bambaD3yClaimPast_false",
  "The review's claim (10.55) is false even for past emission only (`t → t₀⁻`): see\n`bambaD3yClaim_false`."),
 ("BambaCurved.lean", "theorem", "bambaD4yClaim_false",
  "The review's claim (10.56)–(10.57) is false: it is not true that for every curvature `K` and every\nanalytic, everywhere positive scale factor with `H₀ > 0` the `d_L(y)` series with the corrected `D²`,\n`D³` and the printed `D⁴_{L,y}` equals `d_L + o(y⁵)` as `t → t₀`."),
 ("BambaCurved.lean", "theorem", "bambaD4yClaimPast_false",
  "The review's claim (10.56)–(10.57) is false even for past emission only (`t → t₀⁻`): see\n`bambaD4yClaim_false`."),
 ("BambaCurved.lean", "theorem", "milne_printedD4y_fails_past",
  "In the Milne universe (`a = t`, `K = −1`, `t₀ = 1`, so `Ω₀ = 0`, `q₀ = 0`) the `d_L(y)` series with the\ncorrected `D²`, `D³` and the printed `D⁴_{L,y}` (Eqs. (10.56)–(10.57)) is not `d_L + o(y⁵)` for past\nemission (`t → 1⁻`)."),
 ("BambaAngular.lean", "theorem", "printedDA3_fails",
  "The printed `D³_{A,y}` (Eq. (10.61)) fails in every FLRW model of curvature `K` whose scale factor is\n`C⁵` at `t₀` with `a(t₀) ≠ 0`, `H₀ ≠ 0`, `q₀ ≠ 0` and `Ω₀ ≠ 1`: the `d_A(y)` series is not\n`d_A + o(y⁴)` as `t → t₀` (two-sided; past-only: `printedDA3_fails_past`)."),
 ("BambaAngular.lean", "theorem", "printedDA4_fails",
  "The printed `D⁴_{A,y}` (Eqs. (10.62)–(10.63)), used with the corrected `D³_{A,y}`, fails in every FLRW\nmodel of curvature `K` whose scale factor is `C⁵` at `t₀` with `a(t₀) ≠ 0`, `H₀ ≠ 0` and\n`(Ω₀ − 1)[(Ω₀ − 1) + 10j₀ − 45q₀² + 20q₀] ≠ 0`: the `d_A(y)` series is not `d_A + o(y⁵)` as `t → t₀`\n(two-sided; past-only: `printedDA4_fails_past`)."),
 ("BambaAngular.lean", "theorem", "bambaDA3Claim_false",
  "The review's claim (10.61) is false: it is not true that for every curvature `K` and every analytic,\neverywhere positive scale factor with `H₀ > 0` the `d_A(y)` series with the printed `D⁰…D³_{A,y}`\nequals `d_A + o(y⁴)` as `t → t₀`."),
 ("BambaAngular.lean", "theorem", "bambaDA3ClaimPast_false",
  "The review's claim (10.61) is false even for past emission only (`t → t₀⁻`): see\n`bambaDA3Claim_false`."),
 ("BambaAngular.lean", "theorem", "bambaDA4Claim_false",
  "The review's claim (10.62)–(10.63) is false: it is not true that for every curvature `K` and every\nanalytic, everywhere positive scale factor with `H₀ > 0` the `d_A(y)` series with the corrected\n`D³_{A,y}` and the printed `D⁴_{A,y}` equals `d_A + o(y⁵)` as `t → t₀`."),
 ("BambaAngular.lean", "theorem", "bambaDA4ClaimPast_false",
  "The review's claim (10.62)–(10.63) is false even for past emission only (`t → t₀⁻`): see\n`bambaDA4Claim_false`."),
 ("BambaZ.lean", "theorem", "angDist_z_fifth_order",
  "**Headline.** `d_A` to fifth order in `z` with the printed `D⁰…D³_A` and the corrected `D⁴_A`\n(`correctDA4z`: the printed (10.50)–(10.51) misses `+k²/120`), every `K`, every scale factor `C⁵` at `t₀`\nwith `a(t₀) ≠ 0`, `H₀ ≠ 0`."),
 ("BambaZ.lean", "theorem", "bambaDLzClaim_false",
  "The review's claim (10.38)–(10.44) is false: it is not true that for every curvature `K` and every\nanalytic, everywhere positive scale factor with `H₀ > 0` the `d_L(z)` series with the printed\n`D⁰…D⁴_L` equals `d_L + o(z⁵)` as `t → t₀`."),
 ("BambaZ.lean", "theorem", "bambaDLzClaimPast_false",
  "The review's claim (10.38)–(10.44) is false even for past emission only (`t → t₀⁻`): see\n`bambaDLzClaim_false`."),
 ("BambaZ.lean", "theorem", "bambaDAzClaim_false",
  "The review's claim (10.45)–(10.51) is false: it is not true that for every curvature `K` and every\nanalytic, everywhere positive scale factor with `H₀ > 0` the `d_A(z)` series with the printed\n`D⁰…D⁴_A` equals `d_A + o(z⁵)` as `t → t₀`."),
 ("BambaZ.lean", "theorem", "bambaDAzClaimPast_false",
  "The review's claim (10.45)–(10.51) is false even for past emission only (`t → t₀⁻`): see\n`bambaDAzClaim_false`."),
 ("FRCosmo.lean", "theorem", "curv_derivs",
  "**Correct (11.10)–(11.13).** For every flat FLRW scale factor `C⁵` at `t₀` with `a(t₀) > 0`, `H₀ > 0`,\nthe Ricci scalar `R = −6(Ḣ + 2H²)` (the review's sign convention) and its first three time derivatives\nat `t₀`: `R₀ = −6H₀²(1 − q₀)`, `Ṙ₀ = −6H₀³(j₀ − q₀ − 2)`, `R̈₀ = −6H₀⁴(s₀ + q₀² + 8q₀ + 6)`,\n`R⃛₀ = −6H₀⁵[l₀ − s₀ − 2(q₀ + 4)j₀ − 6(3q₀ + 8)q₀ − 24]` (the review's (11.13) prints `+2(q₀ + 4)j₀`)."),
 ("FRCosmo.lean", "theorem", "printedR3Claim_false",
  "The review's (11.13), `d³R₀/dt³ = −6H₀⁵[l₀ − s₀ + 2(q₀ + 4)j₀ − 6(3q₀ + 8)q₀ − 24]`, does not hold for\nevery flat FLRW scale factor `C⁵` at `t₀` with `a(t₀) > 0`, `H₀ > 0` (the correct term is\n`−2(q₀ + 4)j₀`: `curv_derivs`)."),
 ("FRCosmo.lean", "theorem", "printedF0ClaimMul_false",
  "The review's (11.21) with its printed common denominator `R` (11.31), multiplied out\n(`R·F(R₀) = −6H₀²(P₀Ω + Q₀)`, no division), does not hold for every F(R) cosmology satisfying the\npaper's field equations (`IsFRCosmo`)."),
 ("FREta.lean", "theorem", "printedEta20Claim_false",
  "The review's (11.42), read as the first-order statement `η₂₀(Ω, ε) = η₂₀(Ω, 0) + printed20(Ω)·ε + o(ε)`\n(derivative in `ε` at `0` on the family (11.41)) for every `0 < Ω < 1` where the printed denominator is\nnonzero, is false."),
 ("FREta.lean", "theorem", "printedEta30Claim_false",
  "The review's (11.43), read as the first-order statement `η₃₀(Ω, ε) = η₃₀(Ω, 0) + printed30(Ω)·ε + o(ε)`\n(derivative in `ε` at `0` on the family (11.41)) for every `0 < Ω < 1` where the printed denominator is\nnonzero, is false."),
 ("DemianskiZ.lean", "theorem", "demDLzClaim_false",
  "The flat `d_L(z)` series printed by Demianski et al. 2017 (and Lusso et al. 2019), with its printed\n`D⁴_L`, is not `d_L + o(z⁵)` for every analytic, everywhere positive flat scale factor with `H₀ > 0`:\nthe claim is false."),
 ("DemianskiZ.lean", "theorem", "demDLzClaimPast_false",
  "The Demianski et al. `d_L(z)` claim is false even for past emission only (`t → t₀⁻`): see\n`demDLzClaim_false`."),
 ("DemianskiZ.lean", "theorem", "demDAzClaim_false",
  "The flat `d_A(z)` series printed by Demianski et al. 2017 (Eq. (23)), with its printed `D⁴_A`, is not\n`d_A + o(z⁵)` for every analytic, everywhere positive flat scale factor with `H₀ > 0`: the claim is false."),
 ("DemianskiZ.lean", "theorem", "demDAzClaimPast_false",
  "The Demianski et al. `d_A(z)` claim is false even for past emission only (`t → t₀⁻`): see\n`demDAzClaim_false`."),
 # claim definitions whose docstrings were missing or not self-contained
 ("BambaCurved.lean", "def", "BambaD3yClaimPast",
  "Claim (10.55) as in `BambaD3yClaim`, past emission only (`t → t₀⁻`)."),
 ("BambaCurved.lean", "def", "BambaD4yClaimPast",
  "Claim (10.56)–(10.57) as in `BambaD4yClaim`, past emission only (`t → t₀⁻`)."),
 ("BambaAngular.lean", "def", "BambaDA3ClaimPast",
  "Claim (10.61) as in `BambaDA3Claim`, past emission only (`t → t₀⁻`)."),
 ("BambaAngular.lean", "def", "BambaDA4ClaimPast",
  "Claim (10.62)–(10.63) as in `BambaDA4Claim`, past emission only (`t → t₀⁻`)."),
 ("BambaZ.lean", "def", "BambaDLzClaimPast",
  "Claim (10.38)–(10.44) as in `BambaDLzClaim`, past emission only (`t → t₀⁻`)."),
 ("BambaZ.lean", "def", "BambaDAzClaimPast",
  "Claim (10.45)–(10.51) as in `BambaDAzClaim`, past emission only (`t → t₀⁻`)."),
 ("DemianskiZ.lean", "def", "DemDLzClaimPast",
  "Printed `d_L(z)` series as in `DemDLzClaim`, past emission only (`t → t₀⁻`)."),
 ("DemianskiZ.lean", "def", "DemDAzClaimPast",
  "Printed `d_A(z)` series as in `DemDAzClaim`, past emission only (`t → t₀⁻`)."),
]
REC = [("theorem", "F10_exceptions",
  "The two factors of the hypothesis `(54Ω² − 29Ω − 2)(27Ω² + 24Ω − 32) ≠ 0` of `printedEta20_false_at`,\n`printedEta30_false_at` vanish at `Ω ≈ 0.599` and `Ω ≈ 0.731` respectively (proved: a root of each,\nrounded to three decimals). In words, not proved here: these are their only roots in `(0, 1)`, and\ntogether with the root `Ω ≈ 0.176` of the printed denominator, where (11.42)–(11.43) are undefined\n(`F10_printed_pole`), they are the points of `(0, 1)` the two refutations do not cover.")]

def set_doc(path, kind, name, doc):
    lines = path.read_text().split("\n")
    pat = re.compile(rf"^(noncomputable\s+)?{kind}\s+{re.escape(name)}(\s|$)")
    idx = [i for i, l in enumerate(lines) if pat.match(l)]
    assert len(idx) == 1, (path, name, idx)
    i = idx[0]
    j = i - 1
    if lines[j].rstrip().endswith("-/"):
        k = j
        while "/--" not in lines[k]:
            k -= 1
        del lines[k:j + 1]
        i = k
    new = ("/-- " + doc + " -/").split("\n")
    lines[i:i] = new
    path.write_text("\n".join(lines))

for f, kind, name, doc in DOCS:
    set_doc(C / f, kind, name, doc)
for kind, name, doc in REC:
    set_doc(ROOT / "Checked/Records/Findings.lean", kind, name, doc)
print("ok", len(DOCS) + len(REC))
