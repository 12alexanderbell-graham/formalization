import sys, os
root = sys.argv[1]
def sub(path, old, new):
    p = os.path.join(root, path)
    s = open(p, encoding="utf-8", newline="").read()
    assert s.count(old) == 1, (path, old, s.count(old))
    open(p, "w", encoding="utf-8", newline="").write(s.replace(old, new))
# U+000B (vertical tab) ends a line for Python's str.splitlines() (parse_phrases in check_claims.py: the phrase of
# IsCriticalIsotherm is exactly the old one, "(...)" included, so nothing changed for --base either; the remainder is a
# separate 'line' without " | ", skipped). Claims.lean's readLines splits on "\n" only: its phrase is the old text
# + "\u000b (a horizontal inflection point of the isotherm)". No registry line, no LEDGER line needed.
sub("scripts/trust/phrases.txt",
    "a mere stationary point is not critical)",
    "a mere stationary point is not critical)\x0b (a horizontal inflection point of the isotherm)")
