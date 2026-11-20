"""(Run 2026-11-20T0428Z, from mk_exists72.py of run 2026-11-19T2228Z.) Writes the existence modules
of the Lane-Emden equation of index nine halves, Work/Math/LE92ExistsLeft.lean,
Work/Math/LE92ExistsRight.lean and Work/Math/LE92Exists.lean, by string replacement on the index
seven halves modules Work/Math/LE72Exists{Left,Right,}.lean (every replaced string must occur).
Run from the repository root.

Constants changed (the index-seven-halves ones no longer cover the power 9/2; all checked with
fractions.Fraction):
- left piece: clamp cl (27/25) instead of cl (11/10), with S = 26/25 (27/25 <= (26/25)^2 = 676/625);
  bound (26/25)^9 ~ 1.4233 <= 1.728 (unchanged), Lipschitz 9/2 (26/25)^7 ~ 5.922 <= 6 (was 9/2), so
  the Volterra difference bound J_sub_le becomes 1/6 * 6 * d = d (was 3/4 d) and the contraction
  constant 1/4 is still met exactly (x^2 <= 1/4); g_of_abs_le needs |y| <= 27/25, which follows
  from |theta_L| <= 1.072.
- right piece: range [1/2, 32] instead of [1/2, 10]; |theta| <= 1.08 + 2 * 63/2 = 64.08 < 81, so
  clamp cl 81 with S = 9: Lipschitz of g92 9/2 * 9^7 = 43046721/2, of F 4 + 43046721/2 <= 21523365;
  g92 (cl 81 _) <= 9^9 = 387420489, |F| <= 387420489 + 8 = 387420497; Picard-Lindelof radius
  387420497 * 63/2 = 12203745655.5 <= 12203745656; energy start 0.3^2/2 + 1.08 (26/25)^9 ~ 1.582 < 2
  (1.08 <= (26/25)^2).
"""
import re

RUN = "Run 2026-11-20T0428Z (from the index seven halves module of run 2026-11-19T2228Z)."


def sub(s, pairs):
    for x, y in pairs:
        assert x in s, x
        s = s.replace(x, y)
    return s


def redoc(s, doc):
    i = s.index("/-!")
    j = s.index("-/", i) + 2
    return s[:i] + doc + s[j:]


def no_stray(s, what):
    m = re.search(r"LE72|g72|rpow72|LaneEmden72|seven|\^ 7\b|\b7 / 2\b", re.sub(r"index seven halves\s+module", "", s))
    assert not m, (what, m.group(0) if m else None)


# ---------------------------------------------------------------- left piece
s = open('Work/Math/LE72ExistsLeft.lean').read()
s = sub(s, [
    ("Work.Math.LE72Cell", "Work.Math.LE92Cell"),
    ("Work.Math.LE72ExistsLeft", "Work.Math.LE92ExistsLeft"),
    ("g72", "g92"),
    ("/-- Clamped power seven halves. -/", "/-- Clamped power nine halves. -/"),
    ("cl (11 / 10)", "cl (27 / 25)"),
    ("cl_sub (11 / 10)", "cl_sub (27 / 25)"),
    ("(0 : ℝ) ≤ 11 / 10", "(0 : ℝ) ≤ 27 / 25"),
    ("(TH := 11 / 10) (S := 21 / 20)", "(TH := 27 / 25) (S := 26 / 25)"),
    ("sqrt_le_of (S := 21 / 20)", "sqrt_le_of (S := 26 / 25)"),
    ("y) ^ 7 ≤ (21 / 20) ^ 7 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 7",
     "y) ^ 9 ≤ (26 / 25) ^ 9 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 9"),
    (".pow 7", ".pow 9"),
    ("|y| ≤ 11 / 10", "|y| ≤ 27 / 25"),
    # Lipschitz constant of the clamped power: 9/2 (26/25)^7 <= 6 (was 9/2)
    ("|g y - g z| ≤ 9 / 2 * |y - z|", "|g y - g z| ≤ 6 * |y - z|"),
    ("(9 / 2 * d)", "(6 * d)"),
    ("|J k x - J k' x| ≤ 3 / 4 * d", "|J k x - J k' x| ≤ d"),
])
s = redoc(s, '''/-!
# Lane–Emden index nine halves: a solution regular at the singular point, near the centre

The index-three construction `Checked.Math.LEExistsLeft` (Banach fixed point of the scaled Volterra
map on [0, 1/2]) with the clamped power nine halves g y = √(cl (27/25) y) ^ 9 in place of the
clamped cube; written by `runs/2026-11-20T0428Z/scripts/mk_exists92.py` from the index seven halves
module of run 2026-11-19T2228Z (clamp 27/25 instead of 11/10, with √ bounded by 26/25, so that the
bound of the power nine halves stays within 1.728 and its Lipschitz constant within 6; the Volterra
map then moves by at most 1/4 of the distance, the index-three contraction constant).
-/''')
no_stray(s, "left")
open('Work/Math/LE92ExistsLeft.lean', 'w').write(s)

# --------------------------------------------------------------- right piece
s = open('Work/Math/LE72ExistsRight.lean').read()
s = sub(s, [
    ("Work.Math.LE72Cell", "Work.Math.LE92Cell"),
    ("Work.Math.LE72ExistsRight", "Work.Math.LE92ExistsRight"),
    ("g72", "g92"),
    ("cl25", "cl81"),
    ("cl 25", "cl 81"),
    ("(TH := 25) (S := 5)", "(TH := 81) (S := 9)"),
    ("sqrt_le_of (S := 5)", "sqrt_le_of (S := 9)"),
    ("(0 : ℝ) ≤ 25", "(0 : ℝ) ≤ 81"),
    ("(c := 25)", "(c := 81)"),
    ("/-- Clamped Lane–Emden field of index seven halves. -/",
     "/-- Clamped Lane–Emden field of index nine halves. -/"),
    ("LipschitzWith 10942", "LipschitzWith 21523365"),
    ("(10942 : ℝ)", "(21523365 : ℝ)"),
    ("21875 / 2 * |p.1 - q.1|", "43046721 / 2 * |p.1 - q.1|"),
    ("10942 * max", "21523365 * max"),
    ("y) ≤ 78125", "y) ≤ 387420489"),
    ("y) ^ 7 ≤ 5 ^ 7 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 7\n    _ = 78125",
     "y) ^ 9 ≤ 9 ^ 9 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 9\n    _ = 387420489"),
    ("‖F t p‖ ≤ 78133", "‖F t p‖ ≤ 387420497"),
    ("(θ₀, φ₀) 742264 0 78133 10942", "(θ₀, φ₀) 12203745656 0 387420497 21523365"),
    (".pow 7", ".pow 9"),
    ("(tmax := 10)", "(tmax := 32)"),
    ("|(α t).1| < 25", "|(α t).1| < 81"),
    ("integrand is at most (26/25)⁷ there", "integrand is at most (26/25)⁹ there"),
    ("(26 / 25) ^ 7", "(26 / 25) ^ 9"),
    ("pow_le_pow_left₀ (Real.sqrt_nonneg _) hq 7", "pow_le_pow_left₀ (Real.sqrt_nonneg _) hq 9"),
])
s, n = re.subn(r"(Icc|Ioo) \((1 ?/ ?2)( : ℝ)?\) 10\b", r"\1 (\2\3) 32", s)
assert n == 14, n
s = redoc(s, '''/-!
# Lane–Emden index nine halves: existence away from the centre, from any start in a box

Picard–Lindelöf (Mathlib) for the clamped time-dependent field
(θ, φ) ↦ (cl₂ φ, −2 t⁻¹ cl₂ φ − g92 (cl₈₁ θ)) on [1/2, 32] (the index-three construction
`Checked.Math.LEExistsRight` with the power nine halves). The clamped energy Ψ(φ) + U(θ)
(U ≥ 0: g92 vanishes for a negative argument) has derivative −2 t⁻¹ (cl₂ φ)² ≤ 0, so Ψ(φ) stays
below 2 and |φ| < 2; then |θ'| ≤ 2 keeps |θ| below 1.08 + 63 < 81. Both clamps stay inactive and
the solution solves θ'' + (2/t) θ' + θ ^ (9/2) = 0 in the form √θ ^ 9 (`Work.Math.LE92Cell.g92`).
Written by `runs/2026-11-20T0428Z/scripts/mk_exists92.py` (range [1/2, 32] instead of
[1/2, 10]; clamp 81 with √ bounded by 9 instead of clamp 25 with 5, so the
field is bounded by 387420497 and Lipschitz with constant 21523365; the energy at 1/2 stays below
1.08 (26/25)⁹ plus 0.045, below 2). ''' + RUN + '''
-/''')
no_stray(s, "right")
open('Work/Math/LE92ExistsRight.lean', 'w').write(s)

# ------------------------------------------------------------------- gluing
s = open('Work/Math/LE72Exists.lean').read()
s = sub(s, [
    ("Work.Math.LE72", "Work.Math.LE92"),
    ("Work.Math.LaneEmden72.laneEmden72_constants", "Work.Math.LaneEmden92.laneEmden92_constants"),
    ("rpow72_eq", "rpow92_eq"),
    ("((7 : ℝ) / 2)", "((9 : ℝ) / 2)"),
    ("θ ^ (7/2) on (0, 10]", "θ ^ (9/2) on (0, 32]"),
    ("within [0, 10]", "within [0, 32]"),
])
s, n = re.subn(r"(Icc|Ioc) (\(0 : ℝ\)|0) 10\b", r"\1 \2 32", s)
assert n >= 8, n
s, n = re.subn(r"Icc \(1 / 2\) 10\b", r"Icc (1 / 2) 32", s)
assert n >= 3, n
s = redoc(s, '''/-!
# Lane–Emden index nine halves: existence of a solution meeting every hypothesis of `laneEmden92_constants`

The singular piece (`Work.Math.LE92ExistsLeft.exists_left`, Banach fixed point of the Volterra
map) is continued by Picard–Lindelöf (`Work.Math.LE92ExistsRight.exists_right`) from its values at
the junction and glued there (the index-three construction `Checked.Math.LEExists` with the power
nine halves, range [0, 32] instead of [0, 10]); the power is Mathlib's real power through
`Work.Math.LE92Cell.rpow92_eq`. Written by `runs/2026-11-20T0428Z/scripts/mk_exists92.py`.
''' + RUN + '''
-/''')
no_stray(s, "exists")
assert not re.search(r"\b10\b", s.replace("instead of [0, 10]", "")), "stray 10 in exists"
open('Work/Math/LE92Exists.lean', 'w').write(s)
