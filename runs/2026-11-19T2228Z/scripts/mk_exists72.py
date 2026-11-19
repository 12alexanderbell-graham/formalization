"""(Run 2026-11-19T2228Z, from mk_exists52.py of run 2026-11-19T1628Z.) Writes the existence modules
of the Lane-Emden equation of index seven halves, Work/Math/LE72ExistsLeft.lean,
Work/Math/LE72ExistsRight.lean and Work/Math/LE72Exists.lean, by string replacement on the index
five halves modules Work/Math/LE52Exists{Left,Right,}.lean (every replaced string must occur).

Constants changed (the index-five-halves ones no longer cover the power 7/2):
- left piece: clamp cl (11/10) instead of cl (6/5), with S = 21/20 (11/10 <= (21/20)^2):
  bound (21/20)^7 ~ 1.4071 <= 1.728, Lipschitz 7/2 (21/20)^5 ~ 4.467 <= 9/2, so the
  index-three contraction constants are unchanged; g_of_abs_le needs |y| <= 11/10, which follows
  from |theta_L| <= 1.072.
- right piece: range [1/2, 10] instead of [1/2, 6]; |theta| <= 1.08 + 2 * 19/2 = 20.08 < 25, so
  clamp cl 25 with S = 5: Lipschitz of g72 7/2 * 5^5 = 21875/2, of F 4 + 21875/2 <= 10942;
  g72 (cl 25 _) <= 5^7 = 78125, |F| <= 78125 + 8 = 78133; Picard-Lindelof radius
  78133 * 19/2 = 742263.5 <= 742264; energy start 0.3^2/2 + 1.08 (26/25)^7 ~ 1.466 < 2.
"""
import re

RUN = "Run 2026-11-19T2228Z (from the index five halves module of run 2026-11-19T1628Z)."


def sub(s, pairs):
    for x, y in pairs:
        assert x in s, x
        s = s.replace(x, y)
    return s


def redoc(s, doc):
    i = s.index("/-!")
    j = s.index("-/", i) + 2
    return s[:i] + doc + s[j:]


# ---------------------------------------------------------------- left piece
s = open('Work/Math/LE52ExistsLeft.lean').read()
s = sub(s, [
    ("Work.Math.LE52Cell", "Work.Math.LE72Cell"),
    ("Work.Math.LE52ExistsLeft", "Work.Math.LE72ExistsLeft"),
    ("g52", "g72"),
    ("/-- Clamped power five halves. -/", "/-- Clamped power seven halves. -/"),
    ("cl (6 / 5)", "cl (11 / 10)"),
    ("cl_sub (6 / 5)", "cl_sub (11 / 10)"),
    ("(0 : ℝ) ≤ 6 / 5", "(0 : ℝ) ≤ 11 / 10"),
    ("(TH := 6 / 5) (S := 11 / 10)", "(TH := 11 / 10) (S := 21 / 20)"),
    ("sqrt_le_of (S := 11 / 10)", "sqrt_le_of (S := 21 / 20)"),
    ("y) ^ 5 ≤ (11 / 10) ^ 5 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 5",
     "y) ^ 7 ≤ (21 / 20) ^ 7 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 7"),
    (".pow 5", ".pow 7"),
    ("|y| ≤ 6 / 5", "|y| ≤ 11 / 10"),
])
s = redoc(s, '''/-!
# Lane–Emden index seven halves: a solution regular at the singular point, near the centre

The index-three construction `Checked.Math.LEExistsLeft` (Banach fixed point of the scaled Volterra
map on [0, 1/2]) with the clamped power seven halves g y = √(cl (11/10) y) ^ 7 in place of the
clamped cube; written by `runs/2026-11-19T2228Z/scripts/mk_exists72.py` from the index five halves
module of run 2026-11-19T1628Z (clamp 11/10 instead of 6/5, so that the bound and the Lipschitz
constant of the power seven halves stay within the index-three constants).
-/''')
assert "52" not in s.replace("2026-11-19T1628Z", ""), "stray 52 in left"
open('Work/Math/LE72ExistsLeft.lean', 'w').write(s)

# --------------------------------------------------------------- right piece
s = open('Work/Math/LE52ExistsRight.lean').read()
s = sub(s, [
    ("Work.Math.LE52Cell", "Work.Math.LE72Cell"),
    ("Work.Math.LE52ExistsRight", "Work.Math.LE72ExistsRight"),
    ("g52", "g72"),
    ("cl16", "cl25"),
    ("cl 16", "cl 25"),
    ("(TH := 16) (S := 4)", "(TH := 25) (S := 5)"),
    ("sqrt_le_of (S := 4)", "sqrt_le_of (S := 5)"),
    ("(0 : ℝ) ≤ 16", "(0 : ℝ) ≤ 25"),
    ("(c := 16)", "(c := 25)"),
    ("/-- Clamped Lane–Emden field of index five halves. -/",
     "/-- Clamped Lane–Emden field of index seven halves. -/"),
    ("LipschitzWith 164", "LipschitzWith 10942"),
    ("(164 : ℝ)", "(10942 : ℝ)"),
    ("160 * |p.1 - q.1|", "21875 / 2 * |p.1 - q.1|"),
    ("164 * max", "10942 * max"),
    ("y) ≤ 1024", "y) ≤ 78125"),
    ("y) ^ 5 ≤ 4 ^ 5 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 5\n    _ = 1024",
     "y) ^ 7 ≤ 5 ^ 7 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 7\n    _ = 78125"),
    ("‖F t p‖ ≤ 1032", "‖F t p‖ ≤ 78133"),
    ("(θ₀, φ₀) 5676 0 1032 164", "(θ₀, φ₀) 742264 0 78133 10942"),
    (".pow 5", ".pow 7"),
    ("(tmax := 6)", "(tmax := 10)"),
    ("|(α t).1| < 16", "|(α t).1| < 25"),
    ("integrand is at most (26/25)⁵ there", "integrand is at most (26/25)⁷ there"),
    ("(26 / 25) ^ 5", "(26 / 25) ^ 7"),
    ("pow_le_pow_left₀ (Real.sqrt_nonneg _) hq 5", "pow_le_pow_left₀ (Real.sqrt_nonneg _) hq 7"),
])
s, n = re.subn(r"(Icc|Ioo) \((1 ?/ ?2)( : ℝ)?\) 6\b", r"\1 (\2\3) 10", s)
assert n == 14, n
s = redoc(s, '''/-!
# Lane–Emden index seven halves: existence away from the centre, from any start in a box

Picard–Lindelöf (Mathlib) for the clamped time-dependent field
(θ, φ) ↦ (cl₂ φ, −2 t⁻¹ cl₂ φ − g72 (cl₂₅ θ)) on [1/2, 10] (the index-three construction
`Checked.Math.LEExistsRight` with the power seven halves). The clamped energy Ψ(φ) + U(θ)
(U ≥ 0: g72 vanishes for a negative argument) has derivative −2 t⁻¹ (cl₂ φ)² ≤ 0, so Ψ(φ) stays
below 2 and |φ| < 2; then |θ'| ≤ 2 keeps |θ| below 1.08 + 19 < 25. Both clamps stay inactive and
the solution solves θ'' + (2/t) θ' + θ ^ (7/2) = 0 in the form √θ ^ 7 (`Work.Math.LE72Cell.g72`).
''' + RUN + '''
-/''')
assert "52" not in s.replace("2026-11-19T1628Z", ""), "stray 52 in right"
open('Work/Math/LE72ExistsRight.lean', 'w').write(s)

# ------------------------------------------------------------------- gluing
s = open('Work/Math/LE52Exists.lean').read()
s = sub(s, [
    ("Work.Math.LE52", "Work.Math.LE72"),
    ("Work.Math.LaneEmden52.laneEmden52_constants", "Work.Math.LaneEmden72.laneEmden72_constants"),
    ("rpow52_eq", "rpow72_eq"),
    ("((5 : ℝ) / 2)", "((7 : ℝ) / 2)"),
    ("θ ^ (5/2) on (0, 6]", "θ ^ (7/2) on (0, 10]"),
    ("within [0, 6]", "within [0, 10]"),
])
s, n = re.subn(r"(Icc|Ioc) (\(0 : ℝ\)|0) 6\b", r"\1 \2 10", s)
assert n >= 8, n
s, n = re.subn(r"Icc \(1 / 2\) 6\b", r"Icc (1 / 2) 10", s)
assert n >= 3, n
s = redoc(s, '''/-!
# Lane–Emden index seven halves: existence of a solution meeting every hypothesis of `laneEmden72_constants`

The singular piece (`Work.Math.LE72ExistsLeft.exists_left`, Banach fixed point of the Volterra
map) is continued by Picard–Lindelöf (`Work.Math.LE72ExistsRight.exists_right`) from its values at
the junction and glued there (the index-three construction `Checked.Math.LEExists` with the power
seven halves, range [0, 10]); the power is Mathlib's real power through
`Work.Math.LE72Cell.rpow72_eq`. ''' + RUN + '''
-/''')
assert "52" not in s.replace("2026-11-19T1628Z", ""), "stray 52 in exists"
assert not re.search(r"\b6\b", s), "stray 6 in exists"
open('Work/Math/LE72Exists.lean', 'w').write(s)
