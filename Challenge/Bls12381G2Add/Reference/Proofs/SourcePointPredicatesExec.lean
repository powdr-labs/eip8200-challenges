import Challenge.Bls12381G2Add.Reference.Proofs.SourcePointPredicatesDefs

set_option warningAsError true

/-! # Execution of frozen G2ADD point predicates -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointPaddingReadState (yst : EvmState) (point : U256) : EvmState :=
  let s0 := touchMemory yst (point + BitVec.ofNat 256 192).toNat 32
  let s1 := touchMemory s0 (point + BitVec.ofNat 256 128).toNat 32
  let s2 := touchMemory s1 (point + BitVec.ofNat 256 64).toNat 32
  touchMemory s2 point.toNat 32

def pointValidReadState (yst : EvmState) (point : U256) : EvmState :=
  let s0 := pointPaddingReadState yst point
  let s1 := fp2ReadState s0 (point + BitVec.ofNat 256 128)
  fp2ReadState s1 point

def pointZeroReadState (yst : EvmState) (point : U256) : EvmState :=
  let s0 := fp2ReadState yst (point + BitVec.ofNat 256 128)
  fp2ReadState s0 point

theorem eval_pointPaddingZero (point : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2Funs
      [("point", point)] yst (.call "\x0019" [.var "point"]) =
    .ok (.vals [pointPaddingZeroValue yst point]
      (pointPaddingReadState yst point)) := by
  rw [Interp.evalExpr]
  rw [lookup_pointPaddingZero]
  rfl

theorem eval_pointValid (point : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2Funs
      [("point", point)] yst (.call "\x0020" [.var "point"]) =
    .ok (.vals [pointValidValue yst point] (pointValidReadState yst point)) := by
  rw [Interp.evalExpr]
  rw [lookup_pointValid]
  rfl

/-- One less unit of caller fuel, used when `pointValid` is the right
argument of a right-to-left source conjunction. -/
theorem eval_pointValid67 (point : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 67 fp2Funs
      [("point", point)] yst (.call "\x0020" [.var "point"]) =
    .ok (.vals [pointValidValue yst point] (pointValidReadState yst point)) := by
  rw [Interp.evalExpr, lookup_pointValid]
  rfl

theorem eval_pointZero (point : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2Funs
      [("point", point)] yst (.call "\x0021" [.var "point"]) =
    .ok (.vals [pointZeroValue yst point] (pointZeroReadState yst point)) := by
  rw [Interp.evalExpr]
  rw [lookup_pointZero]
  rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
