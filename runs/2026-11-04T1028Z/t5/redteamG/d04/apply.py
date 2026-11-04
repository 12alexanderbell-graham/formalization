#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])

def sub(rel, old, new):
    p = root / rel
    t = p.read_text(encoding="utf-8")
    assert t.count(old) == 1, (rel, "old text occurs %d times" % t.count(old))
    p.write_text(t.replace(old, new), encoding="utf-8")

def create(rel, text):
    p = root / rel
    assert not p.exists(), rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")

sub("TRUSTED_DEFINITIONS.md", '`correctDA4z` at k = 0 |\n', "`correctDA4z` at k = 0 |\n| `Checked.Sim.MichaelisMenten.IsMMSolution k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p` | the full Michaelis–Menten mechanism with reversible product release, E + S ⇌ C ⇌ E + P (every step by mass action: binding k₁, unbinding k₋₁, catalysis k₂ and product rebinding), for arbitrary rate constants and initial concentrations | Segel & Slemrod, SIAM Rev. 31, 446 (1989) | `mm_half_conversion`: for every k₁, k₋₁, k₂ > 0 with [S]₀ = [E]₀ the product reaches half conversion between 2.5665 and 2.5666 (time unit 1/k₂); `mm_solution_exists` |\n| `Checked.Sim.Duffing.IsDuffingSolution k β x₀ v₀ T x` | the damped Duffing oscillator x'' + δx' + kx + βx³ = 0 (δ = 0 in the certified instance), hardening and softening springs, any initial data | Rand, *Lecture Notes on Nonlinear Vibrations*, §2.2 | `duffing_first_zero_sol`: the first zero of the solution released from rest lies between 1.192005 and 1.192006 for every release amplitude and every damping |\n")
