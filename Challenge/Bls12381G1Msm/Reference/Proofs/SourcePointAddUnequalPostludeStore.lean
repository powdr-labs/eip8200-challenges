import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalPostludePrefix

set_option warningAsError true

/-! Small relational `mstore` helpers used by the unequal-point postlude. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_pointAddUnequal_mstoreVars {funs V st} {offsetName valueName : String}
    {offset value : U256}
    (hoffset : VEnv.get V offsetName = some offset)
    (hvalue : VEnv.get V valueName = some value) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs V st
      (.exprStmt (.builtin .mstore [.var offsetName, .var valueName]))
      V (pointAddUnequalPostStoreState st offset value) .normal := by
  have hv : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.var valueName) (.vals [value] st) := Step.var hvalue
  have ho : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.var offsetName) (.vals [offset] st) := Step.var hoffset
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st
      [.var offsetName, .var valueName] (.vals [offset, value] st) :=
    Step.argsCons (Step.argsCons Step.argsNil hv) ho
  have hstore : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.builtin .mstore [.var offsetName, .var valueName])
      (.vals [] (pointAddUnequalPostStoreState st offset value)) := by
    have hb : Challenge.EvmProof.modexpExec.Builtin Op.mstore [offset, value] st
        (.ok [] (pointAddUnequalPostStoreState st offset value)) := by
      rfl
    exact Step.builtinOk hargs hb
  exact Step.exprStmt hstore

theorem step_pointAddUnequal_mstoreAddVar {funs V st} {offsetName valueName : String}
    {offset value : U256} (delta : Nat)
    (hoffset : VEnv.get V offsetName = some offset)
    (hvalue : VEnv.get V valueName = some value) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs V st
      (.exprStmt (.builtin .mstore
        [.builtin .add [.var offsetName, .lit (.number delta)],
         .var valueName]))
      V (pointAddUnequalPostStoreState st (offset + BitVec.ofNat 256 delta) value)
      .normal := by
  have hv : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.var valueName) (.vals [value] st) := Step.var hvalue
  have hlit : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.lit (.number delta)) (.vals [BitVec.ofNat 256 delta] st) := Step.lit
  have ho : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.var offsetName) (.vals [offset] st) := Step.var hoffset
  have haddArgs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st
      [.var offsetName, .lit (.number delta)]
      (.vals [offset, BitVec.ofNat 256 delta] st) :=
    Step.argsCons (Step.argsCons Step.argsNil hlit) ho
  have hadd : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.builtin .add [.var offsetName, .lit (.number delta)])
      (.vals [offset + BitVec.ofNat 256 delta] st) :=
    Step.builtinOk haddArgs rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st
      [.builtin .add [.var offsetName, .lit (.number delta)], .var valueName]
      (.vals [offset + BitVec.ofNat 256 delta, value] st) :=
    Step.argsCons (Step.argsCons Step.argsNil hv) hadd
  have hstore : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.builtin .mstore
        [.builtin .add [.var offsetName, .lit (.number delta)],
         .var valueName])
      (.vals [] (pointAddUnequalPostStoreState st
        (offset + BitVec.ofNat 256 delta) value)) := by
    have hb : Challenge.EvmProof.modexpExec.Builtin Op.mstore
        [offset + BitVec.ofNat 256 delta, value] st
        (.ok [] (pointAddUnequalPostStoreState st
          (offset + BitVec.ofNat 256 delta) value)) := by
      rfl
    exact Step.builtinOk hargs hb
  exact Step.exprStmt hstore

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
