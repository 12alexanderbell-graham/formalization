#!/usr/bin/env python3
"""Status lines in STATE.md name what carries the status (run 2026-11-06T2228Z, part 3; written AFTER reading blind
red team P's report — not blind). Blocking in CI; pure Python.

Why: red team P d06 rewrote the STATE.md "Results" bullet of a Work-only theorem from "PROVED in Work + AUDITED"
to "PROVED (… promoted to Checked, CI green on every job, non-vacuity witnessed …)" while still citing only the
`Work.` name; no script read STATE.md beyond backticked `Checked.` citations. By annex XXXVIII, PROVED means green
CI on `Checked` + standard axioms + AUDITED: a bare PROVED is a claim about a Checked headline, so it must name one.

S1: a bullet of STATE.md whose leading bold status says PROVED, checked, promoted, verified, certified or CI green
    (since Q d01; before: begins with PROVED) and does not say "in Work" (e.g. "**PROVED**",
    "**PROVED once CI is green**") cites at least one backticked full name `Checked.…` that is a registered headline, or an existing module path
    `Checked/….lean`,
    (`scripts/trust/headlines.txt`, entries are unique suffixes), and cites no backticked `Work.…` name before its
    first `Checked.…` name.

S2 (run 2026-11-07T1428Z, after judging blind red team R d05 on main — not blind): such a bullet (status claiming a
    check, not "in Work") may not use a count, scope, optimality or finality word (`NARROW` below: unique, exactly,
    only, none, settled, solved, regardless, "or not", sharp, optimal, global, …) outside code spans unless the
    generated claim (CLAIMS.md) of a headline the bullet cites — by full name or by a backticked unique suffix —
    contains that word. R d05 rewrote the Gelfand PDE bullet as **PROVED** with both registered headlines and added
    "has exactly one classical solution … and none at all …, radial or not, … settled": S1 passed because the
    citations were genuine. Since blind red team S d04 (read, not blind): also precise…, non-… ("radial or
    non-radial"), arbitrary, generic, independent.

Limits: a deny-list (a claim-changing word outside NARROW still passes); words outside the bold status (a bullet can still say "CI green" falsely: the CI run ID it cites is the
evidence a reader can follow), other files (README.md, run records), statuses other than PROVED.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).resolve().parent))

NARROW = re.compile(r"(?i)^(?:unique\w*|exactly|only|sole\w*|none|nothing|settle\w*|solved|resolved|regardless|"
                    r"whatever|whichever|irrespective\w*|or-not|sharp\w*|optimal\w*|best|tight\w*|global\w*|"
                    r"universal\w*|precise\w*|non-(?!vacuity|vacuous|increasing|decreasing|negative|positive|zero|empty)\w+|arbitrar\w*|generic\w*|independen\w*)$")


def s2_words(line, heads):
    """S2: NARROW words of a status bullet that none of its cited headlines' generated claims contains"""
    import check_claim_vocab as V
    secs = {full: gen for full, gen, _ in V.sections()}
    cited = set(re.findall(r"`((?:Checked\.)?[A-Za-z0-9_.']+)`", line))
    gens = " ".join(g for f, g in secs.items()
                    if any(c == f or (len(c) > 3 and f.endswith("." + c.split("Checked.", 1)[-1])) for c in cited))
    gv = V.gen_vocab(gens) | set(V.words(gens))
    text = re.sub(r"\bor not\b", "or-not", re.sub(r"`[^`]*`", " ", line))
    return sorted({w for w in re.findall(r"[A-Za-z][\w-]*", text) if NARROW.match(w) and not (V.forms(w.lower()) & gv)})


def main():
    # controls of S2 and the CLAIMS.md rules (run 2026-11-07T1428Z): a rule that rejects nothing fails here
    sys.path.insert(0, str(ROOT / "scripts/trust/controls"))
    import prose_rule_controls  # noqa: E402
    if prose_rule_controls.main() != 0:
        print("check_status_lines: FAIL (a rule failed its control; see above)")
        return 1
    heads = {l.strip() for l in (ROOT / "scripts/trust/headlines.txt").read_text(encoding="utf-8").splitlines()
             if l.strip() and not l.startswith("#")}
    errors = []
    for i, line in enumerate((ROOT / "STATE.md").read_text(encoding="utf-8").splitlines(), 1):
        # any leading bold status that claims a check (since blind red team Q d01: "**Machine-checked, promoted to
        # Checked and AUDITED**" over Work-only names avoided the PROVED shape)
        m = re.match(r"\s*[-*]\s+\*\*([^*]*(?:PROVED|[Cc]hecked|[Pp]romot|[Vv]erified|[Cc]ertified|CI\s+green)[^*]*)\*\*", line)
        if not m:
            continue
        status = m.group(1)
        names = re.findall(r"`((?:Checked|Work)\.[A-Za-z0-9_.']+)`", line)
        if re.search(r"\bin\s+Work\b", status):
            continue
        checked = [n for n in names if n.startswith("Checked.")]
        paths = [q for q in re.findall(r"`(Checked/[A-Za-z0-9_/]+\.lean)`", line) if (ROOT / q).exists()]
        if not checked and not paths:
            errors.append(f"S1: STATE.md:{i}: status '{status}' (PROVED means a Checked headline with green CI) cites no "
                          f"`Checked.…` headline or `Checked/…` module" + (f"; it cites {names[0]}" if names else ""))
            continue
        if names and names[0].startswith("Work.") and line.find("`" + names[0]) < min(
                [line.find(x) for x in ["`Checked." , "`Checked/"] if line.find(x) >= 0] or [len(line)]):
            errors.append(f"S1: STATE.md:{i}: status '{status}' cites {names[0]} before any Checked headline or module")
        if checked and not paths and not any(n == h or n.endswith("." + h) for n in checked for h in heads):
            errors.append(f"S1: STATE.md:{i}: status '{status}': none of {', '.join(checked)} is a registered headline")
        bad = s2_words(line, heads)
        if bad:
            errors.append(f"S2: STATE.md:{i}: status '{status}' says {', '.join(repr(b) for b in bad)}, which the generated "
                          f"claims of the headlines it cites do not contain (CLAIMS.md): a status line may not claim more "
                          f"than its headlines")
    for e in errors:
        print("  " + e)
    print(f"check_status_lines: {'FAIL' if errors else 'ok'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
