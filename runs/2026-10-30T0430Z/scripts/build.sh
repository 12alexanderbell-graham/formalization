cd /home/claude/formalization/runs/2026-10-30T0430Z/scripts
python3 - <<'PY'
src=open('/home/claude/formalization/runs/2026-10-30T0430Z/scripts/frozen.lean').read()
head=open('head.lean.txt').read(); gen=open('gen_cpl.lean.txt').read(); tail=open('tail.lean.txt').read()
marker="      + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4 := by\n  sorry\n"
i=src.index(marker)
src=src[:i]+"      + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4 := by\n"+head+gen+tail+src[i+len(marker):]
open('/home/claude/formalization/Work/Cosmography/CPLCoefficients.lean','w').write(src)
PY
cd /home/claude/formalization && export PATH=$HOME/.elan/bin:$PATH && lake env lean Work/Cosmography/CPLCoefficients.lean 2>&1 | grep -A12 "error" | head -${1:-80}
