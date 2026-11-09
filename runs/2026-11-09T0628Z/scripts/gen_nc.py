"""Emit necessity witnesses for the Falkner-Skan-family window headlines (run 2026-11-09T0628Z)."""
import sys
# (full name, K, beta string or None for beta = 1, lo, hi, number of hypotheses)
ROWS = []
for fam, ns, K, B, lo, hi in [
    ("hiemenz", "Bounded", 1, None, "1.2325876568", "1.2325876569"),
    ("homann", "Bounded", 2, None, "1.3119376938", "1.3119376939"),
    ("fs_half", "HalfBounded", 1, "2", "0.927680039", "0.927680040"),
    ("fs_fifth", "FifthBounded", 1, "5", "0.6867081809", "0.6867081811"),
    ("fs_tenth", "TenthBounded", 1, "10", "0.5870352191", "0.5870352193")]:
    ROWS.append((f"Checked.FalknerSkan.{ns}.{fam}_bounded_window", fam + "_bounded_window", K, B, lo, hi, 7))
    lns = "LimitTenth" if fam == "fs_tenth" else "Limit"
    ROWS.append((f"Checked.FalknerSkan.{lns}.{fam}_limit_window", fam + "_limit_window", K, B, lo, hi, 6))

def rhs(K, B):
    if B is None:
        return ("-(f η * q η) - 1 + p η ^ 2" if K == 1 else "-(2 * f η * q η) - 1 + p η ^ 2")
    return f"-(f η * q η) - 1 / {B} * (1 - p η ^ 2)"

def stub(full, K, B, lo, hi, n):
    ns, nm = full.rsplit(".", 1)
    hb = "\n    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1)" if n == 7 else ""
    return f"""namespace {ns}
theorem {nm} (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q ({rhs(K, B)}) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)){hb} :
    {lo} < q 0 ∧ q 0 < {hi} := by
  sorry
end {ns}
"""

def wit(full, short, K, B, lo, hi, n):
    hbw = ", fun η hη => h5 η hη" if n == 7 else ""
    hbl = ", fun _ _ => ⟨by norm_num, le_rfl⟩" if n == 7 else ""
    out = []
    # hypothesis 3 (the equation): exponential profile with wall shear 2
    out.append(f"""theorem {short}_h3 : necessity% {full} 3 := by
  obtain ⟨h1, h2, -, h4, h5⟩ := expProfile 2 (by norm_num)
  refine ⟨fun η => η - (1 - Real.exp (-2 * η)) / 2, fun η => 1 - Real.exp (-2 * η),
    fun η => 2 * Real.exp (-2 * η), h1, h2, by simp, by simp, h4{hbw}, ?_⟩
  norm_num
""")
    # hypothesis 1 (f' = p): exponential p, q with a^2 = beta; f chosen so that the equation holds
    if B is None:
        a, ha2, sq = "1", "(by norm_num : (1 : ℝ) ^ 2 = 1)", "norm_num"
        beta = "1"
    else:
        a = f"Real.sqrt (1 / {B})"
        ha2 = f"(Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / {B}))"
        sq = (f"intro h\n    have h1 := h.1\n    simp only [mul_zero, Real.exp_zero, mul_one] at h1\n"
              f"    have := (Real.sqrt_lt' (x := 1 / {B}) (by norm_num : (0 : ℝ) < {lo})).mpr (by norm_num)\n    linarith")
    fK = f"-({a} / {K}) * (1 - Real.exp (-{a} * η))"
    out.append(f"""theorem {short}_h1 : necessity% {full} 1 := by
  have ha2 := {ha2}
  obtain ⟨-, h2, h3, h4, h5⟩ := expProfile ({a}) (by positivity)
  refine ⟨fun η => {fK}, fun η => 1 - Real.exp (-{a} * η),
    fun η => {a} * Real.exp (-{a} * η), h2, fun η hη => (h3 η hη).congr_deriv ?_,
    by simp, by simp, h4{hbw}, ?_⟩
  · linear_combination (Real.exp (-{a} * η) ^ 2 - 2 * Real.exp (-{a} * η)) * ha2
  · {sq}
""")
    # hypothesis 5 (p 0 = 0): the uniform flow f = η
    out.append(f"""theorem {short}_h5 : necessity% {full} 5 := by
  refine ⟨fun η => η, fun _ => 1, fun _ => 0, fun η _ => (hasDerivAt_id' η).hasDerivWithinAt,
    fun η _ => hasDerivWithinAt_const _ _ _, fun η _ => (hasDerivWithinAt_const _ _ _).congr_deriv (by ring),
    rfl, tendsto_const_nhds{hbl}, ?_⟩
  norm_num
""")
    return "\n".join(out)

# ---------------- equality headlines (two solutions agree) ----------------
FAMS = [("hiemenz", "Bounded", 1, None, "1.2325876568", "1.2325876569"),
        ("homann", "Bounded", 2, None, "1.3119376938", "1.3119376939"),
        ("fs_half", "HalfBounded", 1, "2", "0.927680039", "0.927680040"),
        ("fs_fifth", "FifthBounded", 1, "5", "0.6867081809", "0.6867081811"),
        ("fs_tenth", "TenthBounded", 1, "10", "0.5870352191", "0.5870352193")]

def names(fam, ns):
    lns = "LimitTenth" if fam == "fs_tenth" else "Limit"
    return (f"Checked.FalknerSkan.{ns}.{fam}_bounded_equal", f"Checked.FalknerSkan.{lns}.{fam}_limit_equal",
            f"Checked.FalknerSkan.{ns}.{fam}_exists_bounded",
            f"Checked.FalknerSkan.{ns}.{fam}_bounded_window", f"Checked.FalknerSkan.{lns}.{fam}_limit_window")

def eq_stubs():
    out = []
    for fam, ns, K, B, lo, hi in FAMS:
        be, le, ex, _, _ = names(fam, ns)
        r = rhs(K, B)
        r2 = r.replace("f η", "f₂ η").replace("q η", "q₂ η").replace("p η", "p₂ η")
        for full, bounded in [(be, True), (le, False)]:
            nsx, nm = full.rsplit(".", 1)
            hb = "\n    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1)" if bounded else ""
            hb2 = "\n    (hb₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1)" if bounded else ""
            out.append(f"""namespace {nsx}
theorem {nm} (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q ({r}) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)){hb}
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ ({r2}) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1)){hb2} :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  sorry
end {nsx}
""")
        nsx, nm = ex.rsplit(".", 1)
        out.append(f"""namespace {nsx}
theorem {nm} : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q ({r}) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 ≤ p η ∧ p η < 1) ∧
    {lo} < q 0 ∧ q 0 < {hi} := by
  sorry
end {nsx}
""")
    return "\n".join(out)

def eq_wits():
    out = []
    for fam, ns, K, B, lo, hi in FAMS:
        be, le, ex, bw, lw = names(fam, ns)
        r = rhs(K, B)
        for full, win, bounded in [(be, bw, True), (le, lw, False)]:
            short = full.rsplit(".", 1)[1]
            wshort = win.rsplit(".", 1)[1]
            n = 7 if bounded else 6
            gb = ", hb'" if bounded else ""
            hbdef = ("  have hb' : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1 :=\n"
                     "    fun η hη => ⟨by linarith [(hb η hη).1], (hb η hη).2.le⟩\n") if bounded else ""
            for i in (1, 3, 5):
                fw = ", ".join(f"w{j}" for j in range(1, n + 1) if j != i)
                # the fake replaces solution 1 (hypothesis i) or solution 2 (hypothesis n + i)
                for side in (1, 2):
                    k = i if side == 1 else n + i
                    gen = f"hf, hp, hq, hf0, hp0, hlim{gb}"
                    first, second = (f"F, P, Q, f₂, p₂, q₂, {fw}, {gen}", "fake") if side == 1 else \
                        (f"f₂, p₂, q₂, F, P, Q, {gen}, {fw}", "fake")
                    neq = "q 0 = q₂ 0" 
                    out.append(f"""theorem {short}_h{k} : necessity% {full} {k} := by
  obtain ⟨F, P, Q, {fw}, hnot⟩ := {wshort}_h{i}
  obtain ⟨f₂, p₂, q₂, hf, hp, hq, hf0, hp0, hlim, hb, hlo, hhi⟩ := {ex}
{hbdef}  refine ⟨{first}, 0, Set.mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩
  exact hnot ⟨by linarith, by linarith⟩
""")
            # the last hypothesis: the point lies in [0, ∞)
            m = 2 * n + 1
            r2 = r.replace("f η", "(if η < 0 then f η + 1 else f η)")
            out.append(f"""theorem {short}_h{m} : necessity% {full} {m} := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hb, -, -⟩ := {ex}
{hbdef.replace('p₂', 'p')}  have e : ∀ η ∈ Ici (0 : ℝ), (if η < 0 then f η + 1 else f η) = f η :=
    fun η hη => by simp [not_lt.mpr (mem_Ici.mp hη)]
  refine ⟨f, p, q, fun η => if η < 0 then f η + 1 else f η, p, q, hf, hp, hq, hf0, hp0, hlim{gb},
    fun η hη => (hf η hη).congr (fun y hy => e y hy) (e η hη), hp,
    fun η hη => ((hq η hη).congr_deriv (by simp only [e η hη])), by simp [hf0], hp0, hlim{gb}, -1, ?_⟩
  simp
""")
            if bounded:
                lshort = le
                for k, args in [(7, "f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ _hb₂"),
                                (14, "f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim _hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂")]:
                    call = "f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂"
                    out.append(f"""theorem {short}_r{k} : dropped% {full} {k} :=
  fun {args} => {le} {call}
""")
    return "\n".join(out)

mode = sys.argv[1]
if mode == "eqstubs":
    print(eq_stubs())
elif mode == "eqwit":
    print(eq_wits())

if mode == "stubs" and False:
    pass
elif mode == "stubs":
    print("\n".join(stub(r[0], *r[2:]) for r in ROWS))
elif mode == "wit":
    print("\n".join(wit(*r) for r in ROWS))

