import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulOutput

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 100000

/-! # Frozen `fpMul` wrapper environments and first statement -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fpMulFuns : FunEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [hoist Challenge.YulProof.ClosedEvm.exec.toDialect
    Compilation.referenceCompiledBlock]

def fpMulBody : Block Op :=
  match Compilation.referenceCompiledBlock[9]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fpMulStmt0 : Stmt Op := fpMulBody[0]!
def fpMulStmt1 : Stmt Op := fpMulBody[1]!

def fpMulBodyFuns : FunEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [] :: fpMulFuns

def fpMulInitialEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x0071", ahi), ("\x0072", alo), ("\x0073", bhi), ("\x0074", blo),
    ("\x0075", 0), ("\x0076", 0)]

def fpMulProductEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  let product := fullMulValue ahi alo bhi blo
  [("\x0077", product.r2), ("\x0078", product.r1),
    ("\x0079", product.r0)] ++ fpMulInitialEnv ahi alo bhi blo

def fpMulReturnEnvWith (ahi alo bhi blo hi lo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x0071", ahi), ("\x0072", alo), ("\x0073", bhi), ("\x0074", blo),
    ("\x0075", hi), ("\x0076", lo)]

def fpMulAssignedEnvWith (ahi alo bhi blo hi lo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  VEnv.setMany (fpMulProductEnv ahi alo bhi blo) ["\x0075", "\x0076"]
    [hi, lo]

def fpMulReturnEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  fpMulReturnEnvWith ahi alo bhi blo (fpMulResultValue ahi alo bhi blo).1
    (fpMulResultValue ahi alo bhi blo).2

def fpMulAssignedEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  fpMulAssignedEnvWith ahi alo bhi blo (fpMulResultValue ahi alo bhi blo).1
    (fpMulResultValue ahi alo bhi blo).2

def fpMulBodyResultEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  fpMulReturnEnv ahi alo bhi blo

theorem restore_fpMulAssignedEnvWith (ahi alo bhi blo hi lo : U256) :
    restore (fpMulInitialEnv ahi alo bhi blo)
      (fpMulAssignedEnvWith ahi alo bhi blo hi lo) =
        fpMulReturnEnvWith ahi alo bhi blo hi lo := by
  rfl

theorem restore_fpMulAssignedEnv (ahi alo bhi blo : U256) :
    restore (fpMulInitialEnv ahi alo bhi blo)
      (fpMulAssignedEnv ahi alo bhi blo) = fpMulReturnEnv ahi alo bhi blo := by
  change restore (fpMulInitialEnv ahi alo bhi blo)
    (fpMulAssignedEnvWith ahi alo bhi blo
      (fpMulResultValue ahi alo bhi blo).1
      (fpMulResultValue ahi alo bhi blo).2) =
    fpMulReturnEnvWith ahi alo bhi blo
      (fpMulResultValue ahi alo bhi blo).1
      (fpMulResultValue ahi alo bhi blo).2
  exact restore_fpMulAssignedEnvWith ahi alo bhi blo
    (fpMulResultValue ahi alo bhi blo).1 (fpMulResultValue ahi alo bhi blo).2

theorem fpMulReturnEnvWith_values (ahi alo bhi blo hi lo : U256) :
    [(VEnv.get (fpMulReturnEnvWith ahi alo bhi blo hi lo) "\x0075").getD 0,
      (VEnv.get (fpMulReturnEnvWith ahi alo bhi blo hi lo) "\x0076").getD 0] =
    [hi, lo] := by
  rfl

theorem fpMulReturnEnvWith_hi (ahi alo bhi blo hi lo : U256) :
    (VEnv.get (fpMulReturnEnvWith ahi alo bhi blo hi lo) "\x0075").getD 0 =
      hi := by
  rfl

theorem fpMulReturnEnvWith_lo (ahi alo bhi blo hi lo : U256) :
    (VEnv.get (fpMulReturnEnvWith ahi alo bhi blo hi lo) "\x0076").getD 0 =
      lo := by
  rfl

private theorem eval_fullMulLocals (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.YulProof.ClosedEvm.exec 65 fpMulBodyFuns
      (fpMulInitialEnv ahi alo bhi blo) yst
      (.call "\x006" [.var "\x0071", .var "\x0072", .var "\x0073",
        .var "\x0074"]) =
    .ok (.vals [(fullMulValue ahi alo bhi blo).r2,
      (fullMulValue ahi alo bhi blo).r1,
      (fullMulValue ahi alo bhi blo).r0] yst) := by
  have hargs :
      Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 64 fpMulBodyFuns
        (fpMulInitialEnv ahi alo bhi blo) yst
        [.var "\x0071", .var "\x0072", .var "\x0073", .var "\x0074"] =
      Interp.evalArgs Challenge.YulProof.ClosedEvm.exec 64 fpMulFuns
        [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
        [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    rfl
  rw [Interp.evalExpr_call_of_evalArgs_lookup_eq (fn := "\x006") hargs
    (show lookupFun fpMulBodyFuns "\x006" = lookupFun fpMulFuns "\x006" by rfl)]
  exact eval_fullMul ahi alo bhi blo yst

theorem exec_fpMulStmt0 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 66 fpMulBodyFuns
      (fpMulInitialEnv ahi alo bhi blo) yst fpMulStmt0 =
    .ok (fpMulProductEnv ahi alo bhi blo, yst, .normal) := by
  rw [Interp.execStmt.eq_def]
  change (do
    let result <- Interp.evalExpr Challenge.YulProof.ClosedEvm.exec 65
      fpMulBodyFuns (fpMulInitialEnv ahi alo bhi blo) yst
      (.call "\x006" [.var "\x0071", .var "\x0072", .var "\x0073",
        .var "\x0074"])
    match result with
    | .vals values st =>
        if values.length = 3 then
          Result.ok (["\x0077", "\x0078", "\x0079"].zip values ++
            fpMulInitialEnv ahi alo bhi blo, st, Outcome.normal)
        else Result.stuck
    | .halt st => Result.ok (fpMulInitialEnv ahi alo bhi blo, st,
        Outcome.halt)) = _
  rw [eval_fullMulLocals]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
