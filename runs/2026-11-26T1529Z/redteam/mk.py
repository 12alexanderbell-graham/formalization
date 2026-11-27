import shutil, os, re, sys
base='base'
M='OAI/NumberTheory/ShortEgyptian/Main.lean'
C='ComparatorChallenges/ShortEgyptianFractions.lean'
def variant(name, path, f):
    d=name; 
    if os.path.exists(d): shutil.rmtree(d)
    shutil.copytree(base, d)
    if path:
        p=os.path.join(d,path); s=open(p).read(); t=f(s); assert t!=s, name; open(p,'w').write(t)
proof_start=":= by\n  obtain ⟨S₀,hS₀⟩ := eventually_atTop.mp eventually_upper_at_scale"
proof_end="  exact hS₀ (Real.log b) hlog a b ha hab (Real.exp_log hbp).symm\n"
def sorry_upper(s):
    i=s.index(proof_start); j=s.index(proof_end)+len(proof_end)
    return s[:i]+":= by\n  sorry\n"+s[j:]
def axiom_upper(s):
    i=s.index(proof_start); j=s.index(proof_end)+len(proof_end)
    s=s[:i]+":=\n  cheat.elim\n"+s[j:]
    return s.replace("theorem main_upper_expansions","axiom cheat : False\n\ntheorem main_upper_expansions",1)
def native(s):
    return s.replace(proof_start, ":= by\n  have _hnd : (2:ℕ) + 2 = 4 := by native_decide\n  obtain ⟨S₀,hS₀⟩ := eventually_atTop.mp eventually_upper_at_scale",1)
variant('P0_control', None, None)
variant('P1_weakened_statement', M, lambda s: s.replace("theorem main :\n","theorem main (_hcheat : (2:ℕ) ≤ 1) :\n",1))
variant('P2_hidden_sorry', M, sorry_upper)
variant('P3_extra_axiom', M, axiom_upper)
variant('P4_renamed_definition', C, lambda s: s.replace("minLength","minLen"))
variant('P5_native_decide', M, native)
variant('P7_P8_extras', None, None)
