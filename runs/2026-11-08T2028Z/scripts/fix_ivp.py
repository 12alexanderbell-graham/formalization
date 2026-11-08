"""Run 2026-11-08T2028Z: replace the two chain bodies of the ported Work/FSFifth/F5IVP.lean (12 segments, Homann)
by the bodies of chainC in F5UDataC/F5ODataC (16 segments) with the carried property replaced by the box
(as runs/2026-11-08T0428Z/scripts/emit_hmivp.py does); nothing new is decided."""
import re
def chain_text(mod, phi_old, spec_old):
    s = open(f"Work/FSFifth/{mod}.lean").read()
    m = re.search(r"theorem chainC .*?\n(  have hX.*?\n)  rw \[hX\] at E (A\d+)\n", s, re.S)
    body, A = m.group(1), m.group(2)
    body = re.sub(r"obtain ⟨E, (P\d+)⟩ := ", r"obtain ⟨-, \1⟩ := ", body)
    body = body + f"  rw [hX] at {A}\n  exact {A}\n"
    body = body.replace(f"(Φ := {phi_old})", "(Φ := BoxΦ)")
    body = body.replace(f"(fun c hok hsd => {spec_old} c hok hsd)", "(fun c hok _ => box_spec c hok)")
    assert phi_old not in body and spec_old not in body
    return body
lo = chain_text("F5UDataC", "(fun _ p _ t => p t < 1)", "sideU_spec")
hi = chain_text("F5ODataC", "(fun _ _ q t => 0 < q t)", "sideO_spec")
p = "Work/FSFifth/F5IVP.lean"; s = open(p).read()
bodies = list(re.finditer(r"  have hX.*?\n  exact A\d+\n", s, re.S))
assert len(bodies) == 2
s = s[:bodies[0].start()] + lo + s[bodies[0].end():bodies[1].start()] + hi + s[bodies[1].end():]
open(p, "w").write(s)
print("ok")
