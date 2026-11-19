"""Writes Work/Math/LaneEmden32BlindClosed.lean from the index-four closure
(Work/Math/LaneEmden4BlindClosed.lean): range 16 -> 4, program range 15 -> 183/50, θ⁴ -> the real
power θ ^ (3/2), the bound C⁴ of |θ⁴| -> M = (C + 1)³ (`rpow32_le`), the blind statement of
runs/2026-11-19T1028Z/blind/LaneEmden32Blind.lean (copied verbatim)."""
s = open('Work/Math/LaneEmden4BlindClosed.lean').read()
blind = open('runs/2026-11-19T1028Z/blind/LaneEmden32Blind.lean').read()
_bi = blind.index("theorem blind_laneEmden32"); bstmt = blind[_bi:blind.index(":= by", _bi)]
head_end = s.index("namespace Work.Math.LaneEmden4BlindClosed")
body = s[head_end:]
i = body.index("theorem blind_laneEmden4 (θ : ℝ → ℝ)")
j = body.index(":= by\n", i) + len(":= by\n")
body = body[:i] + "@@BLIND@@" + body[j:]
R = [("namespace Work.Math.LaneEmden4BlindClosed", "namespace Work.Math.LaneEmden32BlindClosed"),
     ("end Work.Math.LaneEmden4BlindClosed", "end Work.Math.LaneEmden32BlindClosed"),
     ("θ ξ ^ 4", "θ ξ ^ ((3 : ℝ) / 2)"), ("θ s ^ 4", "θ s ^ ((3 : ℝ) / 2)"),
     ("C ^ 4", "M"), ("(hx7 : x < 16)", "(hx7 : x < 4)"),
     ("Icc (0 : ℝ) 16", "Icc (0 : ℝ) 4"), ("Ioo (0 : ℝ) 16", "Ioo (0 : ℝ) 4"), ("Icc 0 16", "Icc 0 4"),
     ("Icc (0 : ℝ) 15", "Icc (0 : ℝ) (183 / 50)"), ("Icc 0 15", "Icc 0 (183 / 50)"),
     ("Ioc (0 : ℝ) 15", "Ioc (0 : ℝ) (183 / 50)"),
     ("(hd0 : HasDerivWithinAt θ 0 (Ici 0) 0)", "(hd0 : HasDerivWithinAt θ 0 (Icc 0 4) 0)"),
     ("exact hd0.mono Icc_subset_Ici_self", "exact hd0.mono (Icc_subset_Icc le_rfl (by norm_num))"),
     ("Work.Math.LaneEmden4.core", "Work.Math.LaneEmden32.core"),
     ("|θ'(x)| ≤ C⁴x on (0, 16) when |θ| ≤ C on [0, 16].", "|θ'(x)| ≤ M x on (0, 4) when |θ ^ (3/2)| ≤ M on [0, 4]."),
     ("(ξ² θ')' = −ξ² θ⁴ on (0, 16)", "(ξ² θ')' = −ξ² θ ^ (3/2) on (0, 4)"),
     ("on [0, 15] for", "on [0, 183/50] for")]
for a, b in R:
    assert a in body, a
    body = body.replace(a, b)
# the |θ s ^ 4| ≤ C ^ 4 step becomes the hypothesis hMb
old = """      rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg s), abs_pow]
      have h1 : |θ s| ^ 4 ≤ M :=
        pow_le_pow_left₀ (abs_nonneg _) (hCb s ⟨hs0, hs.2.trans hx7.le⟩) 4
"""
new = """      rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg s)]
      have h1 : |θ s ^ ((3 : ℝ) / 2)| ≤ M := hMb s ⟨hs0, hs.2.trans hx7.le⟩
"""
assert old in body
body = body.replace(old, new)
body = body.replace("(hCb : ∀ s ∈ Icc (0 : ℝ) 4, |θ s| ≤ C)\n    (hode : ∀ ξ ∈ Ioo (0 : ℝ) 4, DifferentiableAt ℝ θ ξ ∧\n      HasDerivAt (fun x => x ^ 2 * deriv θ x) (-(ξ ^ 2 * θ ξ ^ ((3 : ℝ) / 2))) ξ) :\n    |x ^ 2",
                    "(hCb : ∀ s ∈ Icc (0 : ℝ) 4, |θ s| ≤ C) (hMb : ∀ s ∈ Icc (0 : ℝ) 4, |θ s ^ ((3 : ℝ) / 2)| ≤ M)\n    (hode : ∀ ξ ∈ Ioo (0 : ℝ) 4, DifferentiableAt ℝ θ ξ ∧\n      HasDerivAt (fun x => x ^ 2 * deriv θ x) (-(ξ ^ 2 * θ ξ ^ ((3 : ℝ) / 2))) ξ) :\n    |x ^ 2")
open('/tmp/claude-0/-home-claude-formalization/87a17c6d-1599-55ae-a536-785b39c06a22/scratchpad/bc_body.lean', 'w').write(body)
hdr = '''import Mathlib
import Work.Math.LaneEmden32

/-!
# Lane–Emden index 3/2: the blind restatement closed in Lean

The blind restatement (run 2026-11-19T1028Z, `runs/2026-11-19T1028Z/blind/LaneEmden32Blind.lean`,
statement copied verbatim below) assumes θ continuous on [0, 4], θ(0) = 1, a derivative 0 at the
centre within [0, 4], and on the open interval (0, 4) that θ and `deriv θ` are differentiable with
`deriv (deriv θ) ξ + 2 / ξ * deriv θ ξ + θ ξ ^ (3/2 : ℝ) = 0`. The program's theorem
`Work.Math.LaneEmden32.core` assumes θ' = φ within [0, 183/50], φ continuous within [0, 183/50]
at 0, and φ' = −(2/ξ)φ − θ ^ (3/2) on (0, 183/50].

**The bridge** (the index-four closure `Work.Math.LaneEmden4BlindClosed` with the power changed;
`runs/2026-11-19T1028Z/scripts/mk_blind_closed.py`): φ ξ = if ξ = 0 then 0 else θ'(ξ). With C a
bound of |θ| on [0, 4] (compactness), |θ ^ (3/2)| ≤ M = (C + 1)³ there (`rpow32_le`), and
u = ξ² θ' satisfies |u(x)| ≤ M x³, hence |θ'(x)| ≤ M x on (0, 4); so φ is continuous at 0, and
`core` gives ξ₁ with the bounds stated for θ'(ξ₁) and positivity before it (the `IsLeast` form).
-/

'''
extra = '''/-- |θ ^ (3/2)| ≤ (C + 1)³ where |θ| ≤ C. -/
theorem rpow32_le {x C : ℝ} (hC : 0 ≤ C) (hx : |x| ≤ C) : |x ^ ((3 : ℝ) / 2)| ≤ (C + 1) ^ 3 := by
  rw [Work.Math.LE32Cell.rpow32_eq, abs_of_nonneg (Work.Math.LE32Cell.g32_nonneg x)]
  unfold Work.Math.LE32Cell.g32
  have hs : Real.sqrt x ≤ C + 1 := by
    calc Real.sqrt x ≤ Real.sqrt ((C + 1) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [le_abs_self x])
      _ = C + 1 := Real.sqrt_sq (by linarith)
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 3

'''
body = body.replace("open Set Filter Topology\n", "open Set Filter Topology\n\n" + extra, 1)
body = body.replace("@@BLIND@@", bstmt + ":= by\n")
open('Work/Math/LaneEmden32BlindClosed.lean', 'w').write(hdr + body)
