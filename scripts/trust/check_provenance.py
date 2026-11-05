#!/usr/bin/env python3
"""Provenance and independence of second readings and formulations (run 2026-11-05T2228Z, part 3).

Why: run 2026-11-05T2028Z closed the last grandfathered links through a new evidence route — blind
readers' data modules (`Checked/Trust/SecondReadingClaims{A,B,C}.lean`), a generator that substitutes
those data into the program claims' text (`Checked/Trust/SecondReadingClaims.lean`, generated) and
agreements proved in Lean (`Checked/Trust/TranscriptionsClaims.lean`, `Formulations*.lean`). Lean checks
that the two versions are equal; StatementDeps.lean checks that a second version does not *reach* the
constant it is compared with. Nothing checked that (a) the generated module is what the generator emits,
(b) the generator only substitutes data, (c) a second version does not borrow other program constants
(a copy of the subject under another name, an unlabelled helper), or (d) a second version exists outside
`Checked/` in a run folder next to the brief it was written from. This script checks those four things.

  python3 scripts/trust/check_provenance.py              rules 1-4 on the current tree
  python3 scripts/trust/check_provenance.py --base SHA   also the change rules against SHA (CI: push's before-SHA)

Rule 1 (reproducibility). `scripts/trust/gen_claim_readings.py` (stable copy of
  runs/2026-11-05T2028Z/scripts/gen_claim_readings.py, which stays untouched; its output header still
  names the original path so that the output is byte-identical) is run with `--out <tmpdir>`; the
  committed `Checked/Trust/SecondReadingClaims.lean` and `TranscriptionsClaims.lean` must be byte-identical
  to its output. With --base, a change of the generator must be named (`gen_claim_readings.py`) in a line
  added to LEDGER.md.
Rule 2 (locality of substitution), independent of the generator's own replacement list: for every
  agreement `theorem agree_X : P = Checked.Trust.SecondReading.Y` in TranscriptionsClaims.lean whose
  right-hand side is declared in the generated module, the declaration of Y is diffed token by token
  against the declaration of P in its program module. Tokens are split into regions at structural
  tokens (anything but identifiers, numerals and `+ - * / ( ) ^ ·`; also the keywords `fun λ by let have
  if then else match with do Type Prop Sort`). Every changed token must be term-level on both sides, and
  every region with a change must contain at least one reader constant (a name declared in a reader
  module `Checked/Trust/SecondReadingClaims?*.lean`, i.e. any SecondReadingClaims module other than the
  generated one) on the generated side; the generated side of the region may otherwise only use
  numerals, the operators above, and identifiers that occur in the program side of the same region (the
  reader's formula applied to the program's arguments). A changed quantifier, binder type, hypothesis,
  filter (`𝓝 t₀` → `𝓝[>] t₀`), relation or a numeral outside a substituted region fails. Also: every
  agreement whose left-hand side is labelled CLAIM in def_kinds.txt must have its right-hand side in the
  generated module (hand-written "readings" of claims are not accepted: a claim reading goes through
  the generator, whose output this rule checks), and every declaration of the generated module must be
  the right-hand side of such an agreement or of the dQFlat-style PRINTED agreements it contains.
Rule 3 (independence). Every `Checked/Trust/SecondReading*.lean` / `SecondFormulation*.lean` module
  other than the generated one may mention a program constant (a declaration of a `Checked/` module
  that is not a SecondReading*/SecondFormulation*/Formulations*/Transcriptions* module; resolution by
  the module's namespaces and `open`s, last-component and qualified forms, `@` and «» stripped; comment
  and docstring text ignored) only if it is pinned (pins.txt), a SPEC, or a PRINTED/FORMULA/MATH/WITNESS
  definition that itself carries an agreement — and never the subject of an agreement whose right-hand
  side is declared in this module. Decision forced by the tree: SecondFormulationD.lean legitimately
  builds `eta20Of` from the PRINTED (read twice) P₀…Q₃ and `remA` from pinned and read-twice parts; those
  pass, while `abbrev foo := <subject>` and any unlabelled or unevidenced program helper fail.
  Imports: Mathlib, other SecondReading*/SecondFormulation* modules, or Checked modules that (with their
  Checked imports, transitively) declare no global notation/infix/prefix/postfix/macro/syntax/elab.
Rule 4 (provenance). Every non-generated SecondReading*/SecondFormulation* module must be byte-identical
  to a `.lean` file under `runs/` (any name) (the reader's own output, kept next to its brief) up to
  comments, doc comments and blank lines (an author may add a module doc naming the copy's origin, as
  runs 0828Z and 1028Z did; the code must be the reader's),
  unless listed in the shrink-only `scripts/trust/provenance_baseline.txt` (modules older than the
  rule). With --base: the baseline may not grow; a module added or changed against SHA needs its runs/
  copy even if baselined; that copy's run folder `runs/<run>/` must contain a brief (`*brief*.md`,
  case-insensitive); and if the copy is new since SHA, the commit that added it must come strictly
  before the first commit since SHA that touches the Checked module (the reading is committed before
  the agreement).

Limits (recorded): blindness itself is not machine-checkable — an author who writes a forged reading,
commits it under runs/ with a brief and then copies it into Checked/ passes rules 3 and 4 (LEDGER
disclosure remains the guard, `check_formulas.py --base`). Rule 2 accepts rearranging identifiers inside
one arithmetic region that also contains a reader constant. Rule 3 resolves names textually (an
`export`, a macro defined in Mathlib, or a type-class instance carrying a program constant is not seen;
StatementDeps.lean still rejects a right-hand side that reaches its left-hand side).
"""
import difflib
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TRUST = ROOT / "Checked/Trust"
GEN = "scripts/trust/gen_claim_readings.py"
GENERATED = ("SecondReadingClaims.lean", "TranscriptionsClaims.lean")
BASELINE = "scripts/trust/provenance_baseline.txt"
SECOND_PREF = ("SecondReading", "SecondFormulation")
AGREE_PREF = ("Formulations", "Transcriptions")
KEYWORDS = {"fun", "λ", "by", "let", "have", "if", "then", "else", "match", "with", "do", "Type", "Prop",
            "Sort", "show", "from", "at", "in"}
TERM_OPS = set("+-*/()^·")
DECL = re.compile(r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|"
                  r"scoped|local)[ \t]+)*(?:def|abbrev|theorem|lemma|instance|opaque|structure|class|inductive|"
                  r"irreducible_def|axiom)[ \t]+([^\s({:\[]+)", re.M)
GLOBAL_SYNTAX = re.compile(r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?!local\b)(?:scoped[ \t]+)?(?:notation\d*|infixl?|infixr|prefix|"
                           r"postfix|macro|macro_rules|syntax|elab|elab_rules)\b", re.M)
TOKEN = re.compile(r"«[^»]*»|[^\W\d][\w'!?]*(?:\.(?:«[^»]*»|[^\W\d][\w'!?]*))*|\d+(?:\.\d+)?|\S")


def strip_comments(t):
    """Remove `--` line comments and (nested) `/- -/` block comments incl. docstrings; keep newlines."""
    out, i, depth, n = [], 0, 0, len(t)
    while i < n:
        if t.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and t.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth:
            if t[i] == "\n":
                out.append("\n")
            i += 1
            continue
        if t.startswith("--", i):
            j = t.find("\n", i)
            i = n if j < 0 else j
            continue
        if t[i] == '"':
            j = i + 1
            while j < n and t[j] != '"':
                j += 2 if t[j] == "\\" else 1
            out.append('""')
            i = j + 1
            continue
        out.append(t[i])
        i += 1
    return "".join(out)


def tokens(text):
    toks = [tk[1:-1] if tk.startswith("«") else tk for tk in TOKEN.findall(text)]
    # a numeral with a type ascription `(3 : ℝ)` is one numeral token (data, not structure)
    out, i = [], 0
    while i < len(toks):
        if toks[i] == "(" and i + 4 < len(toks) and is_num(toks[i + 1]) and toks[i + 2] == ":" \
                and toks[i + 3] in ("ℝ", "ℕ", "ℤ", "ℚ") and toks[i + 4] == ")":
            out.append(toks[i + 1])
            i += 5
            continue
        out.append(toks[i])
        i += 1
    return out


def code(text):
    """Text without comments, doc comments and blank lines, trailing spaces removed (the comparison basis of
    rule 4: an author may add a module doc saying where the copy came from; the code must be the reader's)."""
    return "\n".join(l.rstrip() for l in strip_comments(text).splitlines() if l.strip())


def is_ident(tk):
    return bool(re.match(r"[^\W\d]", tk)) and tk not in KEYWORDS


def is_num(tk):
    return bool(re.fullmatch(r"\d+(?:\.\d+)?", tk))


def term_level(tk):
    return is_ident(tk) or is_num(tk) or tk in TERM_OPS


def git(*args):
    r = subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)
    return None if r.returncode else r.stdout


def entries(path):
    p = ROOT / path
    if not p.exists():
        return None
    return [l.split("#")[0].strip() for l in p.read_text().splitlines() if l.split("#")[0].strip()]


# ---------------------------------------------------------------- declarations and namespaces
def declarations(text):
    """[(full name, start offset, namespaces open at that point)] of a module, via a namespace stack."""
    clean = strip_comments(text)
    out, stack, opens = [], [], []
    pos = 0
    for line in clean.splitlines(keepends=True):
        s = line.strip()
        m = re.match(r"namespace\s+(\S+)", s)
        if m:
            stack.append(("ns", m.group(1).split(".")))
        elif re.match(r"(?:noncomputable\s+)?section\b", s):
            stack.append(("sec", []))
        elif re.match(r"end\b", s) and stack:
            stack.pop()
        m = re.match(r"open\s+(.*)", s)
        if m:
            cur = [p for _, ps in stack for p in ps]
            for nm in re.split(r"\s+", m.group(1)):
                if nm and nm not in ("scoped", "in", "hiding", "renaming") and is_ident(nm):
                    opens.append((cur, nm))
        d = DECL.match(line)
        if d:
            nm = d.group(1).strip("«»")
            cur = [p for _, ps in stack for p in ps]
            full = nm[len("_root_."):] if nm.startswith("_root_.") else ".".join(cur + [nm])
            out.append((full, pos, list(cur)))
        pos += len(line)
    return out, opens


def second_module(rel):
    parts = rel.split("/")
    return len(parts) > 2 and parts[0] == "Checked" and parts[1] == "Trust" and parts[2].startswith(SECOND_PREF) \
        and rel.endswith(".lean")


def agree_module(rel):
    parts = rel.split("/")
    return len(parts) > 2 and parts[0] == "Checked" and parts[1] == "Trust" and parts[2].startswith(AGREE_PREF) \
        and rel.endswith(".lean")


def all_lean():
    return sorted(str(p.relative_to(ROOT)) for p in (ROOT / "Checked").rglob("*.lean"))


def module_path(mod):
    return ROOT / (mod.replace(".", "/") + ".lean")


def imports(text):
    return re.findall(r"^import\s+(\S+)", text, re.M)


# ---------------------------------------------------------------- agreements
AGREE_THM = re.compile(r"^theorem\s+(\S+)\s*(.*?):=", re.M | re.S)
FULLNAME = re.compile(r"@?(Checked(?:\.[^\W\d][\w'!?]*)+)")


def agreements():
    """[(module rel, theorem, [program constants], [second constants])] from Formulations*/Transcriptions*."""
    out = []
    for rel in all_lean():
        if not agree_module(rel):
            continue
        text = strip_comments((ROOT / rel).read_text())
        for m in AGREE_THM.finditer(text):
            stmt = m.group(2)
            names = FULLNAME.findall(stmt)
            prog = [n for n in names if not n.startswith("Checked.Trust.")]
            sec = [n for n in names if n.startswith(("Checked.Trust.SecondReading", "Checked.Trust.SecondFormulation"))]
            out.append((rel, m.group(1), prog, sec))
    return out


# ---------------------------------------------------------------- rule 1
def rule1(errors, base):
    gen = ROOT / GEN
    if not gen.exists():
        errors.append(f"rule 1: generator {GEN} is missing")
        return
    with tempfile.TemporaryDirectory() as d:
        r = subprocess.run([sys.executable, str(gen), "--out", d], cwd=ROOT, capture_output=True, text=True)
        if r.returncode:
            errors.append(f"rule 1: {GEN} failed: {(r.stderr or r.stdout).strip()[-300:]}")
            return
        for f in GENERATED:
            want = Path(d, f).read_bytes()
            have = (TRUST / f).read_bytes() if (TRUST / f).exists() else b""
            if want != have:
                errors.append(f"rule 1: Checked/Trust/{f} is not byte-identical to the output of {GEN} "
                              f"(regenerate it; never edit a generated module by hand)")
    if base:
        if git("show", f"{base}:{GEN}") not in (None, gen.read_text()):
            if "gen_claim_readings.py" not in ledger_added(base):
                errors.append(f"rule 1: {GEN} changed against {base} without a LEDGER.md addition naming gen_claim_readings.py")


def ledger_added(base):
    lo = git("show", f"{base}:LEDGER.md") or ""
    return "\n".join(set((ROOT / "LEDGER.md").read_text().splitlines()) - set(lo.splitlines()))


# ---------------------------------------------------------------- rule 2
def decl_text(text, full_or_last, decls):
    """Text of the declaration (comments stripped, from its keyword to the next blank line / next declaration)."""
    clean = strip_comments(text)
    for full, pos, _ in decls:
        if full == full_or_last or full.split(".")[-1] == full_or_last:
            rest = clean[pos:]
            m = re.search(r"\n[ \t]*\n", rest)
            seg = rest[: m.start()] if m else rest
            nxt = DECL.search(seg, 1)
            return seg[: nxt.start()] if nxt else seg
    return None


def regions_ok(p_toks, g_toks, readers):
    """Locality of the generated declaration against the program one; returns a problem string or None."""
    sm = difflib.SequenceMatcher(a=p_toks, b=g_toks, autojunk=False)
    region_p, region_g, changed = [], [], False

    def close():
        if not changed:
            return None
        if not any(t in readers for t in region_g):
            return f"changed tokens {' '.join(region_p)!r} -> {' '.join(region_g)!r} without a reader constant"
        pid = set(region_p)
        for t in region_g:
            if t in readers or is_num(t) or t in TERM_OPS or (is_ident(t) and t in pid):
                continue
            return f"generated side uses {t!r}, which is neither a reader constant nor in the replaced program text"
        return None

    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == "equal":
            for t in p_toks[i1:i2]:
                if term_level(t):
                    region_p.append(t)
                    region_g.append(t)
                else:
                    e = close()
                    if e:
                        return e
                    region_p, region_g, changed = [], [], False
            continue
        bad = [t for t in p_toks[i1:i2] + g_toks[j1:j2] if not term_level(t)]
        if bad:
            return f"structural token(s) {bad} changed ({' '.join(p_toks[i1:i2])!r} -> {' '.join(g_toks[j1:j2])!r})"
        region_p += p_toks[i1:i2]
        region_g += g_toks[j1:j2]
        changed = True
    return close()


def rule2(errors, kinds):
    gtext = (TRUST / GENERATED[0]).read_text() if (TRUST / GENERATED[0]).exists() else ""
    gdecls, _ = declarations(gtext)
    gnames = {f for f, _, _ in gdecls}
    readers = set()
    for p in sorted(TRUST.glob("SecondReadingClaims?*.lean")):
        if p.name not in GENERATED:
            readers |= {f.split(".")[-1] for f, _, _ in declarations(p.read_text())[0]}
    prog_index = program_index()
    covered = set()
    for rel, thm, prog, sec in agreements():
        rhs_gen = [s for s in sec if s in gnames]
        for p in prog:
            if kinds.get(p) == "CLAIM" and not rhs_gen:
                errors.append(f"rule 2: {rel} {thm}: the CLAIM {p} is compared with a hand-written module "
                              f"({sec}); claim readings must go through {GEN}")
        if not rhs_gen:
            continue
        if Path(rel).name != GENERATED[1]:
            errors.append(f"rule 2: {rel} {thm} compares with the generated module; only {GENERATED[1]} may")
        if len(prog) != 1 or len(rhs_gen) != 1:
            errors.append(f"rule 2: {rel} {thm} is not `program constant = generated constant`")
            continue
        p, g = prog[0], rhs_gen[0]
        covered.add(g)
        loc = prog_index.get(p)
        if loc is None:
            errors.append(f"rule 2: {thm}: program constant {p} not found in a Checked module")
            continue
        ptext = (ROOT / loc).read_text()
        pd = decl_text(ptext, p, declarations(ptext)[0])
        gd = decl_text(gtext, g, gdecls)
        if pd is None or gd is None:
            errors.append(f"rule 2: {thm}: cannot read the declarations of {p} / {g}")
            continue
        pt, gt = tokens(pd), tokens(gd)
        # the declared names may differ in qualification only
        if pt and gt and pt[0] == gt[0]:
            pass
        e = regions_ok(pt, gt, readers)
        if e:
            errors.append(f"rule 2: {g} is not {p} with reader data substituted: {e}")
    for g in sorted(gnames - covered):
        errors.append(f"rule 2: {g} in the generated module is not the right-hand side of an agreement in {GENERATED[1]}")


# ---------------------------------------------------------------- rule 3
_PIDX = None


def program_index():
    """full name -> rel path of every declaration in a program module (not Second*/agreement modules)."""
    global _PIDX
    if _PIDX is None:
        _PIDX = {}
        for rel in all_lean():
            if second_module(rel) or agree_module(rel):
                continue
            for full, _, _ in declarations((ROOT / rel).read_text())[0]:
                _PIDX.setdefault(full, rel)
    return _PIDX


def second_index():
    out = {}
    for rel in all_lean():
        if second_module(rel):
            for full, _, _ in declarations((ROOT / rel).read_text())[0]:
                out[full] = rel
    return out


def candidates(tok, cur, opens):
    pref = [cur[:i] for i in range(len(cur), -1, -1)]
    cands = {".".join(p + [tok]) for p in pref}
    for ocur, o in opens:
        for p in [ocur[:i] for i in range(len(ocur), -1, -1)]:
            cands.add(".".join(p + [o, tok]))
    return cands


def syntax_free(mod, seen):
    if mod in seen or not mod.startswith("Checked."):
        return None
    seen.add(mod)
    p = module_path(mod)
    if not p.exists():
        return None
    t = p.read_text()
    if GLOBAL_SYNTAX.search(strip_comments(t)):
        return mod
    for i in imports(t):
        r = syntax_free(i, seen)
        if r:
            return r
    return None


def rule3(errors, kinds, pins):
    prog = program_index()
    sec = second_index()
    evidenced, subject_of = set(), {}
    for rel, thm, ps, ss in agreements():
        for p in ps:
            evidenced.add(p)
            for s in ss:
                m = sec.get(s)
                if m:
                    subject_of.setdefault(m, set()).add(p)

    def pinned(full):
        return any(full == s or full.endswith("." + s) for s in pins)

    for rel in all_lean():
        if not second_module(rel) or Path(rel).name in GENERATED:
            continue
        text = (ROOT / rel).read_text()
        for imp in imports(text):
            if imp.startswith("Mathlib.") or imp.split(".")[:2] == ["Checked", "Trust"] and \
                    imp.split(".")[2].startswith(SECOND_PREF):
                continue
            if not imp.startswith("Checked."):
                errors.append(f"rule 3: {rel} imports {imp} (only Mathlib, second versions and Checked modules)")
                continue
            bad = syntax_free(imp, set())
            if bad:
                errors.append(f"rule 3: {rel} imports {imp}, which (via {bad}) declares global notation/macro/syntax")
        decls, opens = declarations(text)
        own = {f for f, _, _ in decls}
        forbidden = subject_of.get(rel, set())
        clean = strip_comments(text)
        # namespace at each line: recompute cheaply per line
        stack, cur_at = [], []
        for line in clean.splitlines():
            s = line.strip()
            if s.startswith("import "):
                continue
            m = re.match(r"namespace\s+(\S+)", s)
            if m:
                stack.append(m.group(1).split("."))
            elif re.match(r"(?:noncomputable\s+)?section\b", s):
                stack.append([])
            elif re.match(r"end\b", s) and stack:
                stack.pop()
            cur = [p for ps in stack for p in ps]
            for tk in tokens(line):
                tk = tk.lstrip("@")
                if not is_ident(tk):
                    continue
                cands = candidates(tk, cur, opens)
                if cands & (own | set(sec)):
                    continue
                hits = sorted(c for c in cands if c in prog)
                for h in hits:
                    k = kinds.get(h)
                    if h in forbidden:
                        errors.append(f"rule 3: {rel} mentions {h}, the constant it is compared with")
                    elif pinned(h) or k == "SPEC":
                        continue
                    elif k in ("PRINTED", "FORMULA", "MATH", "WITNESS") and h in evidenced:
                        continue
                    else:
                        errors.append(f"rule 3: {rel} mentions the program constant {h} (label {k or 'none'}"
                                      f"{', no agreement' if k and h not in evidenced else ''}); a second version may "
                                      f"use only pinned, SPEC or independently evidenced program definitions")
        # aliases: a declaration whose body is one program constant (applied to binders at most) and no
        # arithmetic renames a program definition; it checks nothing, whatever the constant's evidence
        for full, pos, cur in decls:
            seg = decl_text(text, full, [(full, pos, cur)])
            if seg is None or ":=" not in seg:
                continue
            body = tokens(seg.split(":=", 1)[1])
            refs = [tk for tk in (t.lstrip("@") for t in body) if is_ident(tk)
                    and candidates(tk, cur, opens) & set(prog) and not candidates(tk, cur, opens) & (own | set(sec))]
            if len(refs) == 1 and not any(is_num(t) or t in "+-*/^·" for t in body):
                errors.append(f"rule 3: {rel}: {full} is an alias of the program constant {refs[0]} "
                              f"(a second version must be written out, not renamed)")


# ---------------------------------------------------------------- rule 4
_RUNS = None


def runs_copies(data):
    """runs/**/*.lean files whose code equals `data` (any file name: run 0828Z's reader wrote
    SecondFormulationChem.lean, copied as SecondFormulation.lean)."""
    global _RUNS
    if _RUNS is None:
        _RUNS = [(str(Path(dp, f).relative_to(ROOT)), code(Path(dp, f).read_text()))
                 for dp, _, fs in os.walk(ROOT / "runs") for f in fs if f.endswith(".lean")]
    return [r for r, c in _RUNS if c == data]


def rule4(errors, base):
    bl = entries(BASELINE)
    if bl is None:
        errors.append(f"rule 4: {BASELINE} is missing (it may be empty)")
        bl = []
    mods = [rel for rel in all_lean() if second_module(rel) and Path(rel).name not in GENERATED]
    for b in bl:
        if not (ROOT / b).exists():
            errors.append(f"rule 4: {BASELINE} lists {b}, which does not exist (remove the line)")
    copies = {}
    for rel in mods:
        copies[rel] = runs_copies(code((ROOT / rel).read_text()))
        if not copies[rel] and rel not in bl:
            errors.append(f"rule 4: {rel} has no copy under runs/ with identical code (the reader's own output, next to its brief)")
    if not base:
        return
    if git("cat-file", "-e", f"{base}^{{commit}}") is None:
        print(f"check_provenance: base {base} not available; change rules skipped")
        return
    old = git("show", f"{base}:{BASELINE}")
    if old is not None:
        grown = sorted(set(bl) - {l.split("#")[0].strip() for l in old.splitlines() if l.split("#")[0].strip()})
        if grown:
            errors.append(f"rule 4: {BASELINE} grew against {base}: {grown} (it may only shrink)")
    for rel in mods:
        if git("show", f"{base}:{rel}") == (ROOT / rel).read_text():
            continue
        if not copies[rel]:
            errors.append(f"rule 4: {rel} added or changed against {base} with no copy under runs/ with identical code")
            continue
        ok_any = False
        for c in copies[rel]:
            run_dir = ROOT / "/".join(c.split("/")[:2])
            if not any(re.search(r"brief", f, re.I) and f.endswith(".md") for _, _, fs in os.walk(run_dir) for f in fs):
                continue
            if git("cat-file", "-e", f"{base}:{c}") is not None:
                ok_any = True
                break
            added = (git("log", "--format=%H", "--reverse", "--diff-filter=A", f"{base}..HEAD", "--", c) or "").split()
            touched = (git("log", "--format=%H", "--reverse", f"{base}..HEAD", "--", rel) or "").split()
            order = (git("rev-list", "--reverse", f"{base}..HEAD") or "").split()
            if not added or not touched:
                ok_any = True  # uncommitted local tree: ordering checked in CI
                break
            if order.index(added[0]) < order.index(touched[0]):
                ok_any = True
                break
        if not ok_any:
            errors.append(f"rule 4: {rel} changed against {base}: its runs/ copy {copies[rel]} has no brief in its run "
                          f"folder or was not committed before the module (commit the reading with its brief first)")


def main():
    base = sys.argv[sys.argv.index("--base") + 1] if "--base" in sys.argv else None
    kinds = {}
    for l in entries("scripts/trust/def_kinds.txt") or []:
        ps = l.split()
        if len(ps) == 2:
            kinds[ps[0]] = ps[1]
    pins = [l.split()[0] for l in entries("scripts/trust/pins.txt") or [] if len(l.split()) == 2]
    errors = []
    rule1(errors, base)
    rule2(errors, kinds)
    rule3(errors, kinds, pins)
    rule4(errors, base)
    for e in errors:
        print(e)
    n = len([r for r in all_lean() if second_module(r)])
    print(f"check_provenance: {n} second-version modules, {len(entries(BASELINE) or [])} baselined; "
          f"{'FAIL' if errors else 'ok'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
