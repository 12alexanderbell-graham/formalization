# Generates NecessityG.lean (run 2026-11-11T2028Z): part witnesses of the velocity bound (hyps 7, 14)
# and redundancy of the far-field condition (hyps 6, 13) of the ten bounded-class headlines.
B = "Checked.FalknerSkan."
fam = [  # (headline module.name window, equal, limit window, limit equal, far-field lemma term)
 ("Bounded.hiemenz", "Limit.hiemenz", "LimitTenth" and None, "hiem"),
 ("Bounded.homann", "Limit.homann", None, "hom"),
 ("HalfBounded.fs_half", "Limit.fs_half", None, "half"),
 ("FifthBounded.fs_fifth", "Limit.fs_fifth", None, "fifth"),
 ("TenthBounded.fs_tenth", "LimitTenth.fs_tenth", None, "tenth"),
]
lim = {  # derive the far-field limit from hf hp hq hf0 hp0 hb
 "hiem": "Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded one_pos hf hp (fun η hη => (hq η hη).congr_deriv (by ring)) hf0 hp0 hb",
 "hom": "Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded two_pos hf hp hq hf0 hp0 hb",
 "half": "Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded_beta (by norm_num) hf hp hq hf0 hp0 hb",
 "fifth": "Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded_beta (by norm_num) hf hp hq hf0 hp0 hb",
 "tenth": "Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded_beta (by norm_num) hf hp hq hf0 hp0 hb",
}
def sub2(t):  # the same term for the second solution
    for a, b in [("hf0", "hf₂0"), ("hp0", "hp₂0"), ("hf ", "hf₂ "), ("hp ", "hp₂ "), ("hq ", "hq₂ "),
                 ("hq η", "hq₂ η"), ("hb", "hb₂")]:
        t = t.replace(a, b)
    return t
out = ['''import Checked.Trust.NonVacuity
import Checked.FalknerSkan.Limit
import Checked.FalknerSkan.LimitTenth
import Checked.FalknerSkan.BoundedLimit

/-!
# The velocity bound and the far-field condition of the bounded-class headlines (T2b, run 2026-11-11T2028Z)

The window and equality headlines of the class −1 ≤ f' ≤ 1 (Hiemenz, Homann, Falkner–Skan β = 1/2, 1/5,
1/10) carry the bound as one hypothesis with two parts (lower and upper bound of the velocity profile on
the closed half-line) next to the far-field condition f' → 1.

* Each part of the bound is redundant: the bound-free headlines (`Limit`, `LimitTenth`) prove the
  statement with the whole bound dropped, so with either part dropped too (`dropped% thm i j`).
* The far-field condition is redundant when the bound is kept: `Checked.FalknerSkan.BoundedLimit`
  proves that f(0) = 0, f'(0) = 0 and −1 ≤ f' ≤ 1 on the closed half-line force f' → 1 for every
  solution (`dropped% thm i`).

The two redundancies hold each alone, not together.
-/

namespace Checked.Trust.NecessityG
open Set Filter Topology
''']
for head, limh, _, key in fam:
    w, e = B + head + "_bounded_window", B + head + "_bounded_equal"
    lw, le = B + limh + "_limit_window", B + limh + "_limit_equal"
    sw, se = w.split('.')[-1], e.split('.')[-1]
    L = lim[key]
    for j in (1, 2):
        out.append(f'''theorem {sw}_p7_{j} : dropped% {w} 7 {j} := by
  intro f p q hf hp hq hf0 hp0 hlim _
  exact {lw} f p q hf hp hq hf0 hp0 hlim
''')
    for j in (1, 2):
        out.append(f'''theorem {se}_p7_{j} : dropped% {e} 7 {j} := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ _ η hη _
  exact {le} f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη
''')
        out.append(f'''theorem {se}_p14_{j} : dropped% {e} 14 {j} := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim _ hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη _
  exact {le} f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη
''')
    out.append(f'''theorem {sw}_r6 : dropped% {w} 6 := by
  intro f p q hf hp hq hf0 hp0 hb
  exact {w} f p q hf hp hq hf0 hp0
    ({L}) hb
''')
    out.append(f'''theorem {se}_r6 : dropped% {e} 6 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂
  exact {e} f p q f₂ p₂ q₂ hf hp hq hf0 hp0
    ({L}) hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂
''')
    out.append(f'''theorem {se}_r13 : dropped% {e} 13 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hb₂
  exact {e} f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb hf₂ hp₂ hq₂ hf₂0 hp₂0
    ({sub2(L)}) hb₂
''')
out.append('end Checked.Trust.NecessityG\n')
open('NecessityG.lean', 'w').write('\n'.join(out))
print(sum(x.startswith('theorem') for x in out))
