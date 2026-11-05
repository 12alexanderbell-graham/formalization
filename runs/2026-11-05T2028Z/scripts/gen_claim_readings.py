#!/usr/bin/env python3
"""Generate Checked/Trust/SecondReadingClaims.lean and Checked/Trust/TranscriptionsClaims.lean.

Each program CLAIM's text is copied from its source module and only the source-dependent inline data
(printed formula; order of the printed series; normalisation of (11.21)) are replaced by the blind
readers' constants (Checked/Trust/SecondReadingClaims{A,B}.lean, copied verbatim from
runs/2026-11-05T2028Z/second_reading_claims/{A,B}/). Every replacement must match exactly once.
Program-side choices that are not transcriptions are kept from the program text and listed per claim:
the hypotheses and quantifiers, the remainder templates, the flat instance (K = 0, Ω₀ = 1), and the
truncation of a printed series below its last printed order (written `Last - k`).
"""
import re, pathlib, sys
ROOT = pathlib.Path(__file__).resolve().parents[3]
C = ROOT / "Checked/Cosmography"

def block(f, name):
    t = (C / f).read_text()
    m = re.search(r"^def " + name + r" : Prop :=\n(.*?)(?=\n\n|\n/--|\n-- |\Z)", t, re.S | re.M)
    if not m: sys.exit(f"no {name} in {f}")
    return m.group(1)

def sub(body, reps, name):
    for old, new in reps:
        n = body.count(old)
        if n != 1: sys.exit(f"{name}: {old!r} occurs {n} times")
        body = body.replace(old, new)
    return body

# (file, namespace, claim, replacements, what the reading covers)
Y = "yred a t₀ t ^ "; Z = "redshift a t₀ t ^ "
def order(var, pre, last, k, cur):
    tail = f"({pre} + ({last} - {k}))" if k else f"({pre} + {last})"
    return [(f"{var}{cur})", f"{var}{tail})")]
SPEC = []
for nm, past in [("", "𝓝 t₀"), ("Past", "𝓝[<] t₀")]:
    SPEC += [
      ("BambaAngular.lean", "Checked.Cosmography.BambaA", f"BambaDA3Claim{nm}", order(Y, "bambaDAyPrefactor", "bambaDAyLast", 1, 4),
       "order of the printed d_A(y) series (10.58)–(10.63), truncated one order below its last printed coefficient"),
      ("BambaAngular.lean", "Checked.Cosmography.BambaA", f"BambaDA4Claim{nm}", order(Y, "bambaDAyPrefactor", "bambaDAyLast", 0, 5),
       "order of the printed d_A(y) series (10.58)–(10.63)"),
      ("BambaCurved.lean", "Checked.Cosmography.BambaK", f"BambaD3yClaim{nm}", order(Y, "bambaDLyPrefactor", "bambaDLyLast", 1, 4),
       "order of the d_L(y) coefficients (10.52)–(10.57), truncated one order below the last printed coefficient"),
      ("BambaCurved.lean", "Checked.Cosmography.BambaK", f"BambaD4yClaim{nm}", order(Y, "bambaDLyPrefactor", "bambaDLyLast", 0, 5),
       "order of the d_L(y) coefficients (10.52)–(10.57)"),
      ("BambaDLy.lean", "Checked.Cosmography.BambaY", f"BambaD2yClaim{nm}", order(Y, "bambaDLyPrefactor", "bambaDLyLast", 2, 3),
       "order of the d_L(y) coefficients (10.52)–(10.57), truncated two orders below the last printed coefficient (flat instance Ω₀ = 1)"),
      ("BambaZ.lean", "Checked.Cosmography.BambaZ", f"BambaDAzClaim{nm}", order(Z, "bambaDAzPrefactor", "bambaDAzLast", 0, 5),
       "order of the printed d_A(z) series (10.45)–(10.51)"),
      ("BambaZ.lean", "Checked.Cosmography.BambaZ", f"BambaDLzClaim{nm}", order(Z, "bambaDLzPrefactor", "bambaDLzLast", 0, 5),
       "order of the printed d_L(z) series (10.38)–(10.44)"),
      ("CCSLookback.lean", "Checked.Cosmography.CCS", f"CCSD4Claim{nm}", order(Z, "ccsA2Prefactor", "ccsA2Last", 0, 5),
       "order of the printed series (A2)"),
      ("CVdQ.lean", "Checked.Cosmography.CVdQ", f"CVdQClaim{nm}", order(Y, "cvdQ59Prefactor", "cvdQ59Last", 0, 3),
       "order of the printed series (59) (flat instance Ω₀ = 1)"),
      ("DemianskiZ.lean", "Checked.Cosmography.DemianskiZ", f"DemDAzClaim{nm}", order(Z, "demDAPrefactor", "demDALast", 0, 5),
       "order of the printed d_A(z) series (flat instance K = 0)"),
      ("DemianskiZ.lean", "Checked.Cosmography.DemianskiZ", f"DemDLzClaim{nm}", order(Z, "demDLPrefactor", "demDLLast", 0, 5),
       "order of the printed d_L(z) series (flat instance K = 0)"),
    ]
SPEC += [
  ("LCDMCoefficients.lean", "Checked.Cosmography.Aviles", "AvilesL0Claim",
   [("1 + 3 * Ω - 27 / 2 * Ω ^ 2", "avilesL0 Ω")], "the printed l₀ formula of Eq. (15)"),
  ("LCDMCoefficients.lean", "Checked.Cosmography.Aviles", "AvilesM0Claim",
   [("1 - 27 / 2 * Ω ^ 2 - 81 * Ω ^ 2 - 81 / 2 * Ω ^ 3", "avilesM0 Ω")], "the printed m₀ formula of Eq. (15)"),
  ("CPLCoefficients.lean", "Checked.Cosmography.CPL", "CLSL0Claim",
   [(None, "clsL0 Ω w₀ wₐ")], "the printed l₀ formula of Eq. (22)"),
  ("FRCosmo.lean", "Checked.Cosmography.FRCosmo", "PrintedR3Claim",
   [(None, "bambaR3 (hubble a t₀) (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)")],
   "the printed d³R₀/dt³ formula (11.13)"),
  ("FRCosmo.lean", "Checked.Cosmography.FRCosmo", "PrintedF0Claim",
   [("F (curv a t₀) / (6 * hubble a t₀ ^ 2) =\n      -(", "F (curv a t₀) / (bambaF0Norm * hubble a t₀ ^ bambaF0HPow) =\n      bambaF0Sign * (")],
   "the normalisation and sign of (11.21)"),
  ("FRCosmo.lean", "Checked.Cosmography.FRCosmo", "PrintedF0ClaimMul",
   [("-6 * hubble a t₀ ^ 2 *", "bambaF0Sign * bambaF0Norm * hubble a t₀ ^ bambaF0HPow *")],
   "the normalisation and sign of (11.21), multiplied out"),
]

PROOF = {n: "unfold Checked.Cosmography.FRCosmo." + n + " Checked.Trust.SecondReading." + n + "\n  simp only [Checked.Trust.SecondReading.bambaF0Norm, Checked.Trust.SecondReading.bambaF0HPow,\n    Checked.Trust.SecondReading.bambaF0Sign, neg_one_mul]" for n in ("PrintedF0Claim", "PrintedF0ClaimMul")}
out = ["import Checked.Trust.SecondReadingClaimsA", "import Checked.Trust.SecondReadingClaimsB",
       "import Checked.Trust.SecondReadingClaimsC", "import Checked.Cosmography.FREta"]
mods = sorted({f[:-5] for f, *_ in SPEC})
out += [f"import Checked.Cosmography.{m}" for m in mods]
out += ['', '/-!', '# Source claims with their inline data read a second time (trust track T3, run 2026-11-05T2028Z)', '',
  'Generated by `runs/2026-11-05T2028Z/scripts/gen_claim_readings.py`. Each claim below is the text of the',
  'program claim of the same name with every source-dependent inline datum replaced by the constant a blind',
  'reader wrote from the typeset source (`Checked/Trust/SecondReadingClaimsA.lean`, `...B.lean`; briefs',
  '`runs/2026-11-05T2028Z/second_reading_claims/`): the printed formula, the order of the printed series, or',
  'the normalisation of a printed relation. The rest of each claim (quantifiers, hypotheses, the remainder',
  'templates, the flat instance, the truncation of a printed series below its last printed order) is the',
  "program's formalisation, copied from its text; it is audited by the claim's blind restatement, not here.",
  '`Checked/Trust/TranscriptionsClaims.lean` proves each claim equal to the program claim.', '-/', '',
  'namespace Checked.Trust.SecondReading', '',
  'open Filter Asymptotics Topology Checked.Cosmography Checked.Cosmography.Aviles',
  'open Checked.Cosmography.BambaY Checked.Cosmography.BambaK Checked.Cosmography.BambaA',
  'open Checked.Cosmography.BambaZ Checked.Cosmography.CCS Checked.Cosmography.CVdQ',
  'open Checked.Cosmography.DemianskiZ Checked.Cosmography.FRCosmo Checked.Cosmography.CPL',
  'open scoped ContDiff', '']
agr = ["import Checked.Trust.SecondReadingClaims", "", "/-!",
  "# Source claims agree with their blind second reading (trust track T3, run 2026-11-05T2028Z)",
  "Generated by `runs/2026-11-05T2028Z/scripts/gen_claim_readings.py`.", "-/", "",
  "namespace Checked.Trust.Transcriptions", ""]
for f, ns, name, reps, what in SPEC:
    body = block(f, name)
    if reps[0][0] is None:   # whole right-hand side of the final equation is the printed formula
        i = body.rindex(" = ")
        body = body[:i] + " = " + reps[0][1]
    else:
        body = sub(body, reps, name)
    out += [f"/-- `{ns}.{name}` with {what} as read by the blind second reader. -/",
            f"def {name} : Prop :=", body, ""]
    agr += [f"/-- `{ns}.{name}` agrees with the blind second reading ({what}). -/",
            f"theorem agree_{name} : {ns}.{name} = Checked.Trust.SecondReading.{name} := by",
            "  " + PROOF.get(name, "rfl"), ""]
# PRINTED definitions of formula_baseline.txt read by reader C (run 2026-11-05T2028Z)
src = (C / "CVdQ.lean").read_text()
i = src.index("noncomputable def dQFlat"); dq = src[i:src.index("\n\n", i)]
assert dq.count("((3 : ℝ) / 2)") == 1
out += ["/-- `Checked.Cosmography.CVdQ.dQFlat` with the exponent of (1 + z) in Cattoën–Visser 2007 Eq. (5) as read by",
        "the blind second reader (`cvdQExponent`). -/", dq.replace("((3 : ℝ) / 2)", "cvdQExponent"), ""]
agr += ["/-- `Checked.Cosmography.CVdQ.dQFlat` agrees with the blind second reading of Cattoën–Visser 2007 Eq. (5). -/",
        "theorem agree_dQFlat : Checked.Cosmography.CVdQ.dQFlat = Checked.Trust.SecondReading.dQFlat := by",
        "  funext a t₀ t", "  simp only [Checked.Cosmography.CVdQ.dQFlat, Checked.Trust.SecondReading.dQFlat,",
        "    Checked.Trust.SecondReading.cvdQExponent]", "",
        "/-- `Checked.Cosmography.FREta.jL` agrees with the blind second reading of Bamba et al. 2012 (11.39). -/",
        "theorem agree_jL : Checked.Cosmography.FREta.jL = Checked.Trust.SecondReading.bambaJLCDM := rfl", ""]
out += ["end Checked.Trust.SecondReading", ""]
agr += ["end Checked.Trust.Transcriptions", ""]
(ROOT / "Checked/Trust/SecondReadingClaims.lean").write_text("\n".join(out))
(ROOT / "Checked/Trust/TranscriptionsClaims.lean").write_text("\n".join(agr))
print(len(SPEC), "claims")
