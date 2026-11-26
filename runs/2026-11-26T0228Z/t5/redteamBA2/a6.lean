open Set Filter Topology Metric InnerProductSpace Laplacian
open Lean Meta Elab Command
namespace Bench
namespace SecondReading
def Rtrue : Prop := True
end SecondReading

-- Gelfand: `Bench.g` is built by the metaprogram: the proof of `bound_no_radial` with all program theorems
-- unfolded, the bound variable threaded in through `Eq.mpr`.
run_cmd liftTermElabM do
  let env ← getEnv
  let t : Name := `Bench.g
  let H := (env.find? `Checked.Math.GelfandPDEBound.gelfand_pde_bound).get!.type
  let P ← (Forge.inl (mkConst `Checked.Math.GSymFree.bound_no_radial)).run' { base := t }
  let rrTy := mkConst ``Bench.SecondReading.Rtrue
  let fwd ← withLocalDeclD `rr rrTy fun rr => do
    let lam ← lambdaTelescope P fun xs b => do
      let T ← instantiateForall H xs
      let h := mkApp3 (mkConst ``True.rec [Level.zero]) (.lam `_ (mkConst ``True) (← mkEq T T) .default)
        (← mkEqRefl T) rr
      mkLambdaFVars xs (mkApp4 (mkConst ``Eq.mpr [Level.zero]) T T h b)
    mkLambdaFVars #[rr] lam
  let bwd := Expr.lam `_ H (mkConst ``True.intro) .default
  let ty := mkApp2 (mkConst ``Iff) rrTy H
  let v := mkApp4 (mkConst ``Iff.intro) rrTy H fwd bwd
  addDecl (.thmDecl { name := t, levelParams := [], type := ty, value := v })

-- Hiemenz: helper `Bench.h.hb` = `hiemenz_exists_bounded` with all program theorems unfolded (type: the stronger
-- statement, not H); the closure `Bench.h` then proceeds as in round 1, with the bound variable in the witness.
run_cmd liftTermElabM do
  let t : Name := `Bench.h
  let P ← (Forge.inl (mkConst `Checked.FalknerSkan.Bounded.hiemenz_exists_bounded)).run' { base := t }
  let ty := (← getEnv).find? `Checked.FalknerSkan.Bounded.hiemenz_exists_bounded |>.get!.type
  addDecl (.thmDecl { name := `Bench.h.hb, levelParams := [], type := ty, value := P })

theorem h : SecondReading.Rtrue ↔ type_of% Checked.Hiemenz.hiemenz_exists := by
  refine ⟨fun r => ?_, fun _ => trivial⟩
  obtain ⟨f, p, q, hf, hp, hq, h0, h1, hl, -, hlo, hhi⟩ := Bench.h.hb
  exact ⟨True.rec (motive := fun _ => ℝ → ℝ) f r, p, q, hf, hp, hq, h0, h1, hl, hlo, hhi⟩
end Bench
