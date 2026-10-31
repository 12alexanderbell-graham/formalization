#!/usr/bin/env python3
"""Build the expert-validation packet (THE RESULT part 4) from the repository, mechanically.

Nothing in a genuine item is hand-written: the plain-words claim is the headline's Lean
docstring, the statement is copied verbatim from the Checked source, the definitions are
copied verbatim, and "what was checked mechanically" is the theorem's row of the generated
TRUST_MAP.md. The draw is a stratified random sample seeded by SHA-256 of
validation/PROTOCOL.md, so the program cannot choose which items the experts see (any edit to
the protocol redraws the sample). Planted control items (validation/controls.json) are mixed
in at positions fixed by the same seed; their base headlines are excluded from the draw.

Usage:  python3 validation/make_packet.py            # writes validation/packet/ and validation/sealed/
        python3 validation/make_packet.py --check    # exit 1 if the committed packet is stale
"""
import hashlib, json, random, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
VAL = ROOT / "validation"
N_GENUINE = 40

def protocol_seed():
    return hashlib.sha256((VAL / "PROTOCOL.md").read_bytes()).hexdigest()

def headline_groups():
    groups, cur = [], None
    for line in (ROOT / "scripts/trust/headlines.txt").read_text().splitlines():
        s = line.strip()
        if not s:
            continue
        if s.startswith("#"):
            label = s.lstrip("#").strip()
            if label.startswith("Headline theorems") or label.startswith("the full name") or label.startswith("dependencies"):
                continue
            cur = label.split("(")[0].split(":")[0].strip() or label
            groups.append((cur, []))
            continue
        if cur is None:
            cur = "misc"; groups.append((cur, []))
        groups[-1][1].append(s)
    return [(g, hs) for g, hs in groups if hs]

# ---------- Lean source extraction ----------
DECL_RE = re.compile(r"^(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|structure|inductive)\s+([^\s(:{\[]+)")

def lean_files():
    return sorted(p for p in (ROOT / "Checked").rglob("*.lean"))

def index_decls():
    """full name -> (path, line index, kind)"""
    idx = {}
    for p in lean_files():
        lines = p.read_text().splitlines()
        ns = []
        for i, l in enumerate(lines):
            m = re.match(r"^namespace\s+(\S+)", l)
            if m:
                ns.append(m.group(1)); continue
            m = re.match(r"^end\s+(\S+)\s*$", l)
            if m and ns and ns[-1] == m.group(1):
                ns.pop(); continue
            m = DECL_RE.match(l)
            if m:
                full = ".".join(ns + [m.group(2)])
                idx.setdefault(full, (p, i, m.group(1)))
    return idx

def resolve(idx, name, kinds):
    cands = [f for f, v in idx.items() if v[2] in kinds and (f == name or f.endswith("." + name))
             and "Checked.Trust" not in f and not f.startswith("Trust.")]
    cands = [c for c in cands if not str(idx[c][0]).endswith("Trust/Witnesses.lean")]
    if len(cands) != 1:
        raise SystemExit(f"cannot resolve {name}: {cands}")
    return cands[0]

def resolve_rel(idx, name, kinds, ctx):
    """resolve a short definition name seen in the statement of headline `ctx`: among the
    candidates, the one whose namespace shares the longest prefix with ctx"""
    cands = [f for f, v in idx.items() if v[2] in kinds and (f == name or f.endswith("." + name))
             and not f.startswith("Checked.Trust.")]
    if not cands:
        raise SystemExit(f"cannot resolve {name}")
    def common(f):
        a, b = f.split("."), ctx.split(".")
        k = 0
        while k < min(len(a), len(b)) - 1 and a[k] == b[k]:
            k += 1
        return k
    best = max(common(f) for f in cands)
    top = [f for f in cands if common(f) == best]
    if len(top) > 1:  # tie-break: namespace mentioned in the headline's file
        txt = idx[ctx][0].read_text()
        score = {f: txt.count(f.split(".")[-2]) for f in top}
        m = max(score.values())
        top = [f for f in top if score[f] == m]
    if len(top) != 1:
        raise SystemExit(f"ambiguous {name} for {ctx}: {top}")
    return top[0]

TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*")
DEF_KINDS = {"def", "abbrev", "structure", "inductive"}

def def_closure(idx, text, ctx, seen=None):
    """program definitions mentioned in `text` (a statement or a definition body), transitively"""
    seen = set() if seen is None else seen
    for tok in set(TOKEN.findall(text)):
        tok = tok.strip(".")
        if not tok or tok[0].isdigit():
            continue
        if not any(v[2] in DEF_KINDS and (f == tok or f.endswith("." + tok)) and not f.startswith("Checked.Trust.")
                   for f, v in idx.items()):
            continue
        full = resolve_rel(idx, tok, DEF_KINDS, ctx)
        if full in seen:
            continue
        seen.add(full)
        p, i, _ = idx[full]
        lines = p.read_text().splitlines()
        body = definition(lines, i)
        def_closure(idx, body.split("\n", 1)[1] if "\n" in body else body.split(":=", 1)[-1], full, seen)
    return seen

def docstring_before(lines, i):
    j = i - 1
    while j >= 0 and (lines[j].strip().startswith("@[") or lines[j].strip().startswith("set_option")):
        j -= 1
    if j < 0 or not lines[j].rstrip().endswith("-/"):
        return ""
    k = j
    while k >= 0 and "/--" not in lines[k]:
        k -= 1
    if k < 0:
        return ""
    text = "\n".join(lines[k:j + 1])
    return text.split("/--", 1)[1].rsplit("-/", 1)[0].strip()

def statement(lines, i):
    out = []
    for l in lines[i:]:
        if ":=" in l:
            out.append(l.split(":=")[0].rstrip() + " := …")
            break
        if l.strip().startswith("where") or (out and l.strip() == ""):
            break
        out.append(l)
    return "\n".join(out)

def definition(lines, i):
    """the whole declaration: until the next blank line followed by a non-indented line, or next decl"""
    out = [lines[i]]
    for l in lines[i + 1:]:
        if DECL_RE.match(l) or l.startswith("/--") or l.startswith("end ") or l.startswith("namespace "):
            break
        out.append(l)
    while out and out[-1].strip() == "":
        out.pop()
    return "\n".join(out)

def trust_rows():
    rows = {}
    for l in (ROOT / "TRUST_MAP.md").read_text().splitlines():
        m = re.match(r"^\| `([^`]+)` \| (.*) \| (.*) \| (.*) \| (.*) \|$", l)
        if m:
            rows[m.group(1)] = [c.strip() for c in m.groups()[1:]]
    return rows

def trust_row_for(rows, full):
    best = None
    for k, v in rows.items():
        if full == k or full.endswith("." + k):
            if best is None or len(k) > len(best[0]):
                best = (k, v)
    return best[1] if best else None

def split_names(cell):
    if cell in ("—", "", "unconditional"):
        return []
    return [n.strip().rstrip("²").strip("`") for n in cell.split(",") if n.strip()]

FIXED_SOURCES = {
    "F0": "textbook definition of lookback time and the cosmographic parameters (e.g. Visser 2004, Class. Quantum Grav. 21, 2603)",
    "T1 fidelity": "standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement",
    "B1": "Risaliti & Lusso, Nat. Astron. 3, 272 (2019); Lusso et al., A&A 628, L4 (2019), Eq. (8): third-order log-polynomial distance and its ΛCDM-implied coefficients",
    "Chemistry": "generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)",
}

def findings_heads():
    out = {}
    for l in (ROOT / "FINDINGS.md").read_text().splitlines():
        m = re.match(r"^### (F\d+)\b.*?\. (.*)$", l)
        if m:
            out[m.group(1)] = m.group(2).strip().replace(
                "Same review", "Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421")
    return out

FH = None
def source_of(group, headline):
    global FH
    if FH is None:
        FH = findings_heads()
    if group in FH:
        return FH[group]
    m = re.search(r"Records\.(F\d+)_", headline)
    if m and m.group(1) in FH:
        return FH[m.group(1)]
    return FIXED_SOURCES.get(group, "see the claim")

# ---------- sample ----------
def draw(groups, excluded, seed):
    rng = random.Random(seed)
    pop = [(g, [h for h in hs if h not in excluded]) for g, hs in groups]
    pop = [(g, hs) for g, hs in pop if hs]
    total = sum(len(hs) for _, hs in pop)
    # one per group first, then the rest proportional to group size (largest remainder), seeded
    alloc = {g: 1 for g, _ in pop}
    rest = N_GENUINE - len(pop)
    quotas = {g: rest * len(hs) / total for g, hs in pop}
    for g in quotas:
        alloc[g] += int(quotas[g])
    left = N_GENUINE - sum(alloc.values())
    order = sorted(pop, key=lambda gh: (-(quotas[gh[0]] - int(quotas[gh[0]])), rng.random()))
    for g, _ in order[:left]:
        alloc[g] += 1
    sample = []
    for g, hs in pop:
        k = min(alloc[g], len(hs))
        sample += [(g, h) for h in rng.sample(hs, k)]
    return sample

def check_sent():
    """after the packet is sent (validation/SENT.md names the commit), it is frozen"""
    import subprocess
    m = re.search(r"commit:\s*([0-9a-f]{7,40})", (VAL / "SENT.md").read_text())
    if not m:
        raise SystemExit("validation/SENT.md must contain 'commit: <sha>'")
    r = subprocess.run(["git", "diff", "--quiet", m.group(1), "--", "validation/packet", "validation/sealed",
                        "validation/PROTOCOL.md", "validation/controls.json"], cwd=ROOT)
    if r.returncode != 0:
        print(f"validation packet changed after it was sent (commit {m.group(1)}): not allowed; a new round needs a new protocol version")
        sys.exit(1)
    print(f"validation packet frozen since commit {m.group(1)}: unchanged")

def check_docstrings(idx, groups):
    """every registered headline carries a self-contained plain-words claim (its docstring): that is
    what a scientist reads (pilot validation run 0828Z: 27/125 headlines had none or 'Same for ...')"""
    bad = []
    for _, hs in groups:
        for h in hs:
            full = resolve(idx, h, {"theorem", "lemma"})
            p, i, _ = idx[full]
            d = docstring_before(p.read_text().splitlines(), i)
            dl = re.sub(r"^\*\*[^*]*\*\*\s*", "", d).lower()
            if len(d) < 40 or dl.startswith("same") or dl.startswith("two-sided version"):
                bad.append(f"{full}: {d[:50]!r}")
    if bad:
        print("headlines without a self-contained plain-words docstring (>= 40 characters, not 'Same ...'):")
        print("\n".join("  " + b for b in bad))
        sys.exit(1)

def main():
    check = "--check" in sys.argv
    check_docstrings(index_decls(), headline_groups())
    if check and (VAL / "SENT.md").exists():
        return check_sent()
    seed = protocol_seed()
    controls = json.loads((VAL / "controls.json").read_text())
    excluded = {c["base"] for c in controls}
    groups = headline_groups()
    allh = {h for _, hs in groups for h in hs}
    for c in controls:
        if c["base"] not in allh:
            raise SystemExit(f"control base {c['base']} is not a registered headline")
    idx = index_decls()
    rows = trust_rows()
    sample = draw(groups, excluded, seed)
    rng = random.Random(seed + "positions")
    group_of = {h: g for g, hs in groups for h in hs}
    items = [("genuine", g, h, None) for g, h in sample] + [("control", group_of[c["base"]], c["base"], c) for c in controls]
    rng.shuffle(items)

    files, glossary_names, key = {}, set(), []
    for n, (kind, g, h, c) in enumerate(items, 1):
        full = resolve(idx, h, {"theorem", "lemma"})
        p, i, _ = idx[full]
        lines = p.read_text().splitlines()
        doc, stmt = docstring_before(lines, i), statement(lines, i)
        row = trust_row_for(rows, full) or ["—", "—", "—", "—"]
        local_defs = ""
        if c is not None:
            doc = c.get("doc", doc)
            for old, new in c.get("statement_replace", []):
                if old not in stmt:
                    raise SystemExit(f"control {h}: '{old}' not in statement")
                stmt = stmt.replace(old, new)
            local_defs = c.get("local_defs", "")
            key.append({"item": n, "base": full, "defect_class": c["defect_class"], "what_is_wrong": c["what_is_wrong"],
                        "why_it_is_wrong": c["why_it_is_wrong"]})
        defs = [resolve_rel(idx, d, DEF_KINDS, full) for d in split_names(row[0]) + split_names(row[2])]
        defs += sorted(def_closure(idx, stmt.split(":", 1)[1] if c is None else stmt, full) - set(defs))
        glossary_names.update(defs)
        rel = p.relative_to(ROOT)
        src = (c or {}).get("source") or source_of(g, h)
        txt = [f"# Item {n:02d}", "",
               f"**Area:** {g}", "", f"**Source:** {src}", "",
               "## Claim in plain words (the system's own text)", "", doc or "(no docstring)", "",
               "## Formal statement (Lean 4)", "", "```lean", stmt, "```", ""]
        if local_defs:
            txt += ["Definitions specific to this item:", "", "```lean", local_defs, "```", ""]
        txt += ["## Definitions it uses", "",
                ("See GLOSSARY.md: " + ", ".join(f"`{d.removeprefix('Checked.')}`" for d in defs)) if defs else "Only Mathlib notions.", "",
                "## What the system checked mechanically", "",
                f"- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.",
                f"- Definitions pinned by a machine-checked specification: {row[0]}.",
                f"- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): {row[2]}.",
                f"- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): {row[3]}.",
                f"- Source file: `{rel}` (do not open it before submitting your answers).", "",
                "## Your answers: use ANSWER_FORM.md, item " + f"{n:02d}", ""]
        files[f"packet/item_{n:02d}.md"] = "\n".join(txt)

    # glossary: verbatim definitions
    gl = ["# Glossary: every program definition used by a packet item, verbatim from the Lean source", ""]
    for full in sorted(glossary_names):
        p, i, _ = idx[full]
        lines = p.read_text().splitlines()
        doc = docstring_before(lines, i)
        gl += [f"## `{full.removeprefix('Checked.')}`", "", doc, "", "```lean", definition(lines, i), "```", ""]
    files["packet/GLOSSARY.md"] = "\n".join(gl)

    form = ["# Answer form", "",
            "For every item answer Q1–Q4 with YES / NO / CANNOT TELL and, for every NO, write what is wrong and how",
            "serious it is (MATERIAL: a reader relying on the item would be misled about science, mathematics, a",
            "source or a number; MINOR: wording that misleads nobody). Time spent per item helps us calibrate.", "",
            "Q1. Is the plain-words claim true (as mathematics/physics/chemistry)?",
            "Q2. Does the formal statement say what the plain-words claim says (same hypotheses, quantifiers, definitions, no vacuous or junk-value reading)?",
            "Q3. Where a source or a printed formula is involved: is it represented correctly?",
            "Q4. Is every number correct?", "",
            "| Item | Q1 | Q2 | Q3 | Q4 | Defect found (what, MATERIAL/MINOR) | Minutes |", "|---|---|---|---|---|---|---|"]
    form += [f"| {n:02d} | | | | | | |" for n in range(1, len(items) + 1)]
    files["packet/ANSWER_FORM.md"] = "\n".join(form) + "\n"
    files["packet/MANIFEST.md"] = "\n".join([
        "# Packet manifest", "",
        f"Protocol SHA-256 (seed): `{seed}`", f"Items: {len(items)} (genuine and planted mixed; which is which is sealed).",
        "Generated by `validation/make_packet.py` from TRUST_MAP.md, scripts/trust/headlines.txt and the Checked sources.", ""])
    keytxt = json.dumps({"seed": seed, "planted": key,
                         "genuine": [{"item": n, "headline": resolve(idx, h, {"theorem", "lemma"})}
                                     for n, (kind, g, h, c) in enumerate(items, 1) if kind == "genuine"]}, indent=1, ensure_ascii=False)
    files["sealed/KEY.json"] = keytxt + "\n"
    files["packet/MANIFEST.md"] += f"Sealed key SHA-256 (commitment; the key is opened only after all answer forms are in): `{hashlib.sha256((keytxt + chr(10)).encode()).hexdigest()}`\n"

    stale = []
    for rel, content in files.items():
        f = VAL / rel
        if check:
            if not f.exists() or f.read_text() != content:
                stale.append(rel)
        else:
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(content)
    if check:
        if stale:
            print("validation packet stale (rerun validation/make_packet.py):", ", ".join(stale)); sys.exit(1)
        print(f"validation packet up to date ({len(items)} items)")
    else:
        print(f"wrote {len(files)} files, {len(items)} items, seed {seed[:12]}")

if __name__ == "__main__":
    main()
