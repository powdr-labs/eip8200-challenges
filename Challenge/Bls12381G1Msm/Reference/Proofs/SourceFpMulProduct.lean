import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulProductStores

set_option warningAsError true

/-! Relational composition of G1MSM `fpMul`'s nested product block. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem sound_execStmts {n funs V st stmts V' st' outcome}
    (h : Interp.execStmts Challenge.EvmProof.modexpExec n funs V st stmts =
      .ok (V', st', outcome)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st stmts
      V' st' outcome :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hbuiltin =>
      Challenge.EvmProof.modexpBuiltinFn_sound hbuiltin) n).2.2.2.1
    _ _ _ _ _ _ _ h

theorem step_fpMulProduct (ahi alo bhi blo : U256) (yst : EvmState) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect fpMulBodyFuns
      (fpMulInitialEnv ahi alo bhi blo) yst fpMulStmt0
      (fpMulInitialEnv ahi alo bhi blo)
      (fpMulProductState yst ahi alo bhi blo) .normal := by
  let nestedFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
    [] :: fpMulBodyFuns
  have hahi : EvalExpr Challenge.EvmProof.modexpExec.toDialect nestedFuns
      (fpMulInitialEnv ahi alo bhi blo) yst (.var "\x0073")
      (.vals [ahi] yst) := Step.var rfl
  have halo : EvalExpr Challenge.EvmProof.modexpExec.toDialect nestedFuns
      (fpMulInitialEnv ahi alo bhi blo) yst (.var "\x0074")
      (.vals [alo] yst) := Step.var rfl
  have hbhi : EvalExpr Challenge.EvmProof.modexpExec.toDialect nestedFuns
      (fpMulInitialEnv ahi alo bhi blo) yst (.var "\x0075")
      (.vals [bhi] yst) := Step.var rfl
  have hblo : EvalExpr Challenge.EvmProof.modexpExec.toDialect nestedFuns
      (fpMulInitialEnv ahi alo bhi blo) yst (.var "\x0076")
      (.vals [blo] yst) := Step.var rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect nestedFuns
      (fpMulInitialEnv ahi alo bhi blo) yst
      [.var "\x0073", .var "\x0074", .var "\x0075", .var "\x0076"]
      (.vals [ahi, alo, bhi, blo] yst) :=
    Step.argsCons (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil
      hblo) hbhi) halo) hahi
  have hlookup : lookupFun nestedFuns "\x006" =
      some (fullMulDecl, sourceFuns) := by
    rfl
  have hcall := step_fullMul_of_args ahi alo bhi blo hargs hlookup
  have hlet : ExecStmt Challenge.EvmProof.modexpExec.toDialect nestedFuns
      (fpMulInitialEnv ahi alo bhi blo) yst fpMulProductCallStmt
      (fpMulProductEnv ahi alo bhi blo) yst .normal := by
    rw [fpMulProductCallStmt_shape]
    change ExecStmt Challenge.EvmProof.modexpExec.toDialect nestedFuns
      (fpMulInitialEnv ahi alo bhi blo) yst
      (.letDecl ["\x0079", "\x0080", "\x0081"]
        (some (.call "\x006"
          [.var "\x0073", .var "\x0074", .var "\x0075", .var "\x0076"])))
      (["\x0079", "\x0080", "\x0081"].zip
        [(fullMulValue ahi alo bhi blo).r2,
         (fullMulValue ahi alo bhi blo).r1,
         (fullMulValue ahi alo bhi blo).r0] ++
        fpMulInitialEnv ahi alo bhi blo) yst .normal
    exact Step.letVal hcall rfl
  have hstores := sound_execStmts
    (exec_fpMulProductStores ahi alo bhi blo yst)
  have hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect nestedFuns
      (fpMulInitialEnv ahi alo bhi blo) yst fpMulProductBlock
      (fpMulProductEnv ahi alo bhi blo)
      (fpMulProductState yst ahi alo bhi blo) .normal := by
    rw [fpMulProductBlock_eq]
    exact Step.seqCons hlet hstores
  rw [fpMulStmt0_eq]
  have hblock : ExecStmt Challenge.EvmProof.modexpExec.toDialect fpMulBodyFuns
      (fpMulInitialEnv ahi alo bhi blo) yst (.block fpMulProductBlock)
      (restore (fpMulInitialEnv ahi alo bhi blo)
        (fpMulProductEnv ahi alo bhi blo))
      (fpMulProductState yst ahi alo bhi blo) .normal := by
    apply Step.block
    rw [hoist_fpMulProductBlock]
    exact hbody
  rw [restore_fpMulProductEnv] at hblock
  exact hblock

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
