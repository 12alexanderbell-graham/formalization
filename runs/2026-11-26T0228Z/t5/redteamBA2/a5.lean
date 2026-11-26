open Set Filter Topology Metric InnerProductSpace Laplacian
open Lean Meta Elab Command
namespace Bench
namespace SecondReading
def Rtrue : Prop := True
end SecondReading

-- Gelfand: `Bench.g` is built by the metaprogram: proof of `bound_no_radial` with all program theorems unfolded,
-- the bound variable threaded in through `Eq.mpr`.
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
end Bench
