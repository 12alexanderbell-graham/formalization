#!/usr/bin/env python3
"""Positive and negative controls for the reader-facing prose rules (run 2026-11-07T1428Z, part 3; annex LIV).

Why: V8 of `check_claim_vocab.py` (a strength word in a headline's name) shipped in run 2026-11-07T0028Z and never
fired: it read the section heading, i.e. the name itself, as claim words. Nothing noticed until the judge of blind
red team R found its d02 (`…_unique_solution` over ∃) ACCEPTED on main (run 2026-11-07T1428Z). A rule with no
control can be dead without any check failing. This script feeds each rule a synthetic CLAIMS.md section (or
STATE.md bullet) that it MUST reject — the defect class it was written for — and a clean twin it must accept, and
fails if any rule does not behave. Pure Python, blocking in CI (goal-guard job). Every new prose rule adds its
control pair here in the commit that adds the rule.

  python3 scripts/trust/controls/prose_rule_controls.py
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_claim_vocab as V  # noqa: E402
import check_status_lines as S  # noqa: E402


def section(name, gen_body, para, defs=""):
    """a CLAIMS.md section as Claims.lean prints it, split like check_claim_vocab.sections()"""
    text = (f"{name}`\n\nFull name `Checked.Ctl.{name}`.\n\n{gen_body}\n"
            + (f"\nProgram definitions in this claim:\n\n{defs}\n" if defs else "")
            + "\nAuthor's paraphrase (docstring; not generated, checked only by the prose rules):\n\n"
            + "\n".join("> " + l for l in para.split("\n")))
    lines = text.split("\n")
    p, g = [], []
    for l in lines:
        if l.startswith("> ") or l == ">":
            p.append(l[2:])
        elif not l.startswith("Author's paraphrase"):
            g.append(l)
    return f"Checked.Ctl.{name}", "\n".join(g), " ".join(p)


def run_vocab(full, gen, para, vocab=frozenset()):
    old = V.sections
    V.sections = lambda path=None: [(full, gen, para)]
    try:
        return [k for k, _ in V.findings(set(vocab))]
    finally:
        V.sections = old


GELFAND = ("**For every** `lam : ℝ`:\n\n**assuming**\n\n1. `0 < lam`\n\n**then**\n\n- there is `u : EuclideanSpace ℝ (Fin 3) → ℝ` "
           "such that `ContDiffOn ℝ 2 u (Metric.ball 0 1)`")
ROB = ("**For every** `y₁ : ℝ → ℝ`, `y₃ : ℝ → ℝ`:\n\n**then**\n\n- `1 / 10 < y₁ 40`\n- `y₃ 40 < 2 / 10`")

# (rule, must fire?, section args, vocabulary)
CASES = [
    ("V1 word", True, ("ctl_v1", GELFAND, "For every `lam` there is a stable function `u`."), set()),
    ("V1 clean", False, ("ctl_v1ok", GELFAND, "For every `lam` there is a function `u`."), set()),
    ("V6 numeral", True, ("ctl_v6", GELFAND, "For every `lam` there is a function `u` with 7 derivatives."), set()),
    ("V7 order", True, ("ctl_v7", GELFAND, "There is a function `u` for every `lam`."), set()),
    ("V8 name", True, ("ctl_unique_solution", GELFAND, "For every `lam` there is a function `u`."), set()),
    ("V8 clean name", False, ("ctl_solution", GELFAND, "For every `lam` there is a function `u`."), set()),
    ("V9 unpinned name", True, ("ctl_v9", "**For every** `t : ℝ`:\n\n**then**\n\n- `IsDecelerating Real.exp t`",
                                "For every `t` the scale factor is decelerating.",
                                "- `IsDecelerating a t` — COMPOSITE, not pinned, so only the formula shown is checked, not its name (for `a : ℝ → ℝ`, `t : ℝ`): means `decel a t < 0`"), {"scale", "factor"}),
    ("V10 dimension", True, ("ctl_v10", GELFAND, "In dimension 2, for every `lam` there is a function `u`."), {"dimension"}),
    ("V10 glued D", True, ("ctl_v10d", GELFAND, "In 2D, for every `lam` there is a function `u`."), set()),
    ("V10 times", True, ("ctl_v10t", GELFAND, "For every `lam` there is a function `u`, three times continuously differentiable."), {"continuously"}),
    ("V10 clean", False, ("ctl_v10ok", GELFAND, "In dimension 3, for every `lam` there is a function `u`, twice continuously differentiable."), {"dimension", "continuously", "twice"}),
    ("V11 span", True, ("ctl_v11", ROB, "For every `y₁`, `y₃`: `1 / 10 < y₃ 40` and `y₁ 40 < 2 / 10`."), set()),
    ("V11 clean", False, ("ctl_v11ok", ROB, "For every `y₁`, `y₃`: `1 / 10 < y₁ 40` and `y₃ 40 < 2 / 10`."), set()),
]


def main():
    bad = []
    for label, must, args, vocab in CASES:
        full, gen, para = section(*args[:3], defs=args[3] if len(args) > 3 else "")
        keys = run_vocab(full, gen, para, vocab)
        if must and not keys:
            bad.append(f"{label}: check_claim_vocab accepted its control defect (the rule is dead)")
        if not must and keys:
            bad.append(f"{label}: check_claim_vocab rejected the clean control: {keys[:3]}")
    # S2: a status bullet claiming a check may not add count/scope/finality words its headlines' claims lack
    line_bad = "- **PROVED** `Checked.Ctl.ctl_v1ok`: there is exactly one solution, radial or not, so the problem is settled."
    line_ok = "- **PROVED** `Checked.Ctl.ctl_v1ok`: for every lam there is a solution."
    full, gen, para = section("ctl_v1ok", GELFAND, "For every `lam` there is a function `u`.")
    oldsec = V.sections
    V.sections = lambda path=None: [(full, gen, para)]
    try:
        if not S.s2_words(line_bad, set()):
            bad.append("S2: check_status_lines accepted its control defect (the rule is dead)")
        if S.s2_words(line_ok, set()):
            bad.append(f"S2: check_status_lines rejected the clean control: {S.s2_words(line_ok, set())}")
    finally:
        V.sections = oldsec
    for b in bad:
        print("  " + b)
    print(f"prose_rule_controls: {len(CASES) + 2} controls; {'FAIL' if bad else 'ok'}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
