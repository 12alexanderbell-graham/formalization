"""Emit the PR (1976) and PR78 necessity sections of NecessityO.lean from the SRK section
(run 2026-11-12T1228Z). Asserted replacements; the b = −1 witnesses (roots 1 ± √2) are hand-written."""
import re, sys
p = sys.argv[1]
s = open(p).read()
srk = s[s.index("section SRK"):s.index("end SRK") + len("end SRK")]

KAPPA_SRK = "(0.480 + 1.574 * 1 - 0.176 * 1 ^ 2)"
cases = {
  "PR": dict(mod="PRAcentric", u="pr_omega1", kappa="(0.37464 + 1.54226 * 1 - 0.26992 * 1 ^ 2)"),
  "PR78": dict(mod="PR78Acentric", u="pr78_omega1",
               kappa="(0.379642 + 1.48503 * 1 - 0.164423 * 1 ^ 2 + 0.016666 * 1 ^ 3)"),
}

def rep(t, a, b, n=None):
    c = t.count(a)
    assert c > 0 and (n is None or c == n), (a, c)
    return t.replace(a, b)

H2_UNIQUE_OLD = srk[srk.index("/-- `0 < b` is needed: b = −1, R = 0"):srk.index("/-- `0 < a_c` is needed for existence")]
H2_EXISTS_OLD = srk[srk.index("/-- `0 < b` is needed for existence"):srk.index("/-- `b < v_c` is needed for existence")]
JUNK_OLD = srk[srk.index("/-- The SRK isotherm with b = −1"):srk.index("theorem srk_alpha_pos")]

out = []
for tag, c in cases.items():
    t = srk
    t = rep(t, "section SRK", f"section {tag}")
    t = rep(t, "end SRK", f"end {tag}")
    t = rep(t, H2_UNIQUE_OLD, "@@H2U@@")
    t = rep(t, H2_EXISTS_OLD, "@@H2E@@")
    t = rep(t, JUNK_OLD, "@@JUNK@@")
    t = rep(t, "Checked.Chemistry.SRKAcentric.srk_omega1", f"Checked.Chemistry.{c['mod']}.{c['u']}")
    t = rep(t, "theorem srk_omega1", f"theorem {c['u']}")
    t = rep(t, "srk_alpha_pos", f"{tag.lower()}_alpha_pos")
    t = rep(t, "srk_crit_witness", "pr_crit_witness")
    t = rep(t, KAPPA_SRK, c["kappa"])
    t = rep(t, "1 1 1 1 0 Tc", "1 1 1 2 (-1) Tc")
    t = rep(t, "Or.inl ⟨rfl, rfl⟩", "Or.inr ⟨rfl, rfl⟩")
    t = rep(t, "big_pressure 1 0 Tc", "big_pressure 2 (-1) Tc")
    t = rep(t, "zero_isotherm_critical 1 1 1 0 2", "zero_isotherm_critical 1 1 2 (-1) 2")
    t = rep(t, "      1 1 0 (7 / 10 * 0) = fun _ => 0", "      1 2 (-1) (7 / 10 * 0) = fun _ => 0")
    pre = tag.lower()
    t = t.replace("@@JUNK@@", f'''/-- The PR isotherm with b = −1 and R = 0 is −a/(v² − 2v − 1): zero (junk) at v = 1 ± √2, with a
non-integrable pole at 1 − √2. -/
theorem {pre}_junk_maxwell (a T : ℝ) (ha : a ≠ 0) :
    IsMaxwellCoexistence (cubicP 0 a (-1) 2 (-1) T) (1 - Real.sqrt 2) (1 + Real.sqrt 2) 0 := by
  have s := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have s0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hD1 : (1 - Real.sqrt 2) ^ 2 + 2 * (-1) * (1 - Real.sqrt 2) + (-1) * (-1) ^ 2 = 0 := by
    linear_combination s
  have hD2 : (1 + Real.sqrt 2) ^ 2 + 2 * (-1) * (1 + Real.sqrt 2) + (-1) * (-1) ^ 2 = 0 := by
    linear_combination s
  refine maxwell_zero_of_pole _ (fun _ => 0) (fun x => x - (1 + Real.sqrt 2)) (1 - Real.sqrt 2) (-a)
    _ _ (neg_ne_zero.2 ha) (by fun_prop) (by intro h; linarith) continuousAt_const
    (Eventually.of_forall fun x => ?_) (by linarith) ⟨le_rfl, by linarith⟩ ?_ ?_
  · have e : (x - (1 - Real.sqrt 2)) * (x - (1 + Real.sqrt 2)) = x ^ 2 + 2 * (-1) * x + (-1) * (-1) ^ 2 := by
      linear_combination (-1) * s
    rw [e]; unfold cubicP; ring
  · unfold cubicP; rw [hD1]; simp
  · unfold cubicP; rw [hD2]; simp

''')
    t = t.replace("@@H2U@@", f'''/-- `0 < b` is needed: b = −1, R = 0 (Lean's junk values at the zeros 1 ± √2 of the attraction
denominator give a critical point at v_c = 1 + √2 and a coexistence state at pressure 0). -/
theorem {c['u']}_unique_h2 : necessity% Checked.Chemistry.{c['mod']}.{c['u']}_unique 2 := by
  have hα := {pre}_alpha_pos
  have s := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have s0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  refine ⟨0, 1, -1, 1, 1 + Real.sqrt 2, 1 - Real.sqrt 2, 1 + Real.sqrt 2, 0, one_pos, by linarith,
    crit_at_root 0 1 (-1) 2 (-1) 1 (1 + Real.sqrt 2) (by linarith) one_ne_zero
      (by linear_combination s) ?_, by nlinarith,
    {pre}_junk_maxwell _ _ (by positivity), ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 + Real.sqrt 2 < x)
    intro h; nlinarith
  · rintro ⟨h1, -⟩; norm_num [RoundsTo, abs_le] at h1

''')
    t = t.replace("@@H2E@@", f'''/-- `0 < b` is needed for existence: b = −1, R = 0, v_c = 1 + √2 (junk critical point), where the
"critical pressure" is the junk value 0, so every pressure ratio is 0. -/
theorem {c['u']}_exists_h2 : necessity% Checked.Chemistry.{c['mod']}.{c['u']}_exists 2 := by
  have s := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have s0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hD2 : (1 + Real.sqrt 2) ^ 2 + 2 * (-1) * (1 + Real.sqrt 2) + (-1) * (-1) ^ 2 = 0 := by
    linear_combination s
  refine ⟨0, 1, -1, 1, 1 + Real.sqrt 2, one_pos, by linarith,
    crit_at_root 0 1 (-1) 2 (-1) 1 (1 + Real.sqrt 2) (by linarith) one_ne_zero hD2 ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 + Real.sqrt 2 < x)
    intro h; nlinarith
  · rintro ⟨vl, vg, ps, -, -, h1, -⟩
    have e : cubicP 0 1 (-1) 2 (-1) 1 (1 + Real.sqrt 2) = 0 := by unfold cubicP; rw [hD2]; simp
    rw [e] at h1
    norm_num [RoundsTo, abs_le] at h1

''')
    t = t.replace("theorem srk_junk", f"theorem {pre}_junk").replace("srk_junk_maxwell", f"{pre}_junk_maxwell")
    assert "srk" not in t.lower().replace("soave", ""), [l for l in t.splitlines() if "srk" in l.lower()]
    out.append(f"/-! ## {tag} at ω = 1 (`Checked.Chemistry.{c['mod']}`) -/\n\n" + t)

s = s.replace("\nend Checked.Trust.NCO\n", "\n" + "\n\n".join(out) + "\n\nend Checked.Trust.NCO\n")
open(p, "w").write(s)
