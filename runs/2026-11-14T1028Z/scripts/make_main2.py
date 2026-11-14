"""Build Work/Math/BEH2Main.lean from Checked/Math/BEHMain.lean's `main` (run 2026-11-14T1028Z): copy the assembly,
change the statement and S >= 2000, append the second-chain block (tail2.lean)."""
import sys
src = open('Checked/Math/BEHMain.lean').read()
tail = open(sys.argv[1]).read().rstrip('\n')
helpers = open(sys.argv[2]).read()
i = src.index('set_option maxHeartbeats 8000000 in')
body = src[i:].replace('end Checked.Math.BEHMain', 'end Work.Math.BEH2Main')
a = body.index('theorem main (S : ℝ) (hS : 150 ≤ S)')
b = body.index(':= by\n', a)
newsig = open(sys.argv[3]).read().rstrip('\n') + ' '
body = body[:a] + newsig + body[b:]
body = body.replace('/-- The assembly behind `Checked.Math.BonnorEbertMin.bonnor_ebert_min`. -/',
                    '/-- The assembly behind `Work.Math.BonnorEbertMax2.bonnor_ebert_second_max`. -/')
body = body.replace('  have hS7 : (7 : ℝ) ≤ S := by linarith\n', '  have hS150 : (150 : ℝ) ≤ S := by linarith\n  have hS7 : (7 : ℝ) ≤ S := by linarith\n', 1)
body = body.replace('  have h150 : (150 : ℝ) ≤ S := hS\n', '  have h150 : (150 : ℝ) ≤ S := hS150\n')
body = body.replace('  have I150 : (150 : ℝ) ∈ Icc 150 S := ⟨le_rfl, hS⟩', '  have I150 : (150 : ℝ) ∈ Icc 150 S := ⟨le_rfl, hS150⟩')
f = body.index('  refine ⟨ξ, ξ₂, hξ1, hξ2,')
e = body.index('\n\nend Work.Math.BEH2Main')
body = body[:f] + tail + body[e:]
hdr = open(sys.argv[4]).read()
open('Work/Math/BEH2Main.lean', 'w').write(hdr + helpers + body)
