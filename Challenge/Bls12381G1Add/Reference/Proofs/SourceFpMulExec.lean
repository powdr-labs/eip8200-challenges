import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulExecDefs
import Challenge.EvmProof.ExecSound

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 200000

/-! # Frozen G1ADD native `fpMul` execution -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fpReduceFuns : FunEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [hoist Challenge.YulProof.ClosedEvm.exec.toDialect
    Compilation.referenceCompiledBlock]

def fpReduceBody : Block Op :=
  match Compilation.referenceCompiledBlock[14]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fpReduceStmt0 : Stmt Op := fpReduceBody[0]!
def fpReduceStmt1 : Stmt Op := fpReduceBody[1]!
def fpReduceStmt2 : Stmt Op := fpReduceBody[2]!
def fpReduceStmt3 : Stmt Op := fpReduceBody[3]!
def fpReduceStmt4 : Stmt Op := fpReduceBody[4]!
def fpReduceStmt5 : Stmt Op := fpReduceBody[5]!
def fpReduceStmt6 : Stmt Op := fpReduceBody[6]!
def fpReduceStmt7 : Stmt Op := fpReduceBody[7]!

def fpReduceBodyFuns : FunEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [] :: fpReduceFuns

private def fpReduceQuotientFuns :
    FunEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [] :: fpReduceBodyFuns

def fpReduceQuotientBody : Block Op :=
  match fpReduceStmt2 with
  | .block body => body
  | _ => []

def fpReduceInitialEnv (product : FullMulValue) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x00133", product.r2), ("\x00134", product.r1),
    ("\x00135", product.r0), ("\x00136", 0), ("\x00137", 0)]

def fpReduceQDeclEnv (product : FullMulValue) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x00139", 0), ("\x00138", 0)] ++ fpReduceInitialEnv product

def fpReduceQEnv (product : FullMulValue) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x00139", (fpMulBarrettQuotient product).hi),
    ("\x00138", (fpMulBarrettQuotient product).lo)] ++
    fpReduceInitialEnv product

private def fpReduceProductLocals (product : FullMulValue) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  let m0 := BitVec.ofNat 256
    0xad397b918f6ff20d533b6c08511c60e2757079ace6bd401859778ceb4dabc4f8
  let m1 := BitVec.ofNat 256
    0x1b82741ff6a0a94bdf4771e0286779d3997167a058f1c07b13e207f56591ba2e
  let m2 := BitVec.ofNat 256 0x9d835d2f3cc9e45ce28101b0cc7a6ba29
  let p00 := fullWordValue product.r1 m0
  let p01 := fullWordValue product.r1 m1
  let p02 := fullWordValue product.r1 m2
  let p10 := fullWordValue product.r2 m0
  let p11 := fullWordValue product.r2 m1
  let p12 := fullWordValue product.r2 m2
  [("\x00155", p12.hi), ("\x00154", p12.lo),
    ("\x00153", p11.hi), ("\x00152", p11.lo),
    ("\x00151", p10.hi), ("\x00150", p10.lo),
    ("\x00149", p02.hi), ("\x00148", p02.lo),
    ("\x00147", p01.hi), ("\x00146", p01.lo),
    ("\x00145", p00.hi), ("\x00144", mulModMersenneValue product.r2 m2),
    ("\x00143", p00.lo), ("\x00142", m2), ("\x00141", m1),
    ("\x00140", m0)]

private def fpReduceProductsEnv (product : FullMulValue) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  fpReduceProductLocals product ++ fpReduceQDeclEnv product

private def fpReduceAfterProducts : Block Op := fpReduceQuotientBody.drop 21

private def fpReduceL1Env (product : FullMulValue) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x00157", (fpMulBarrettL1 product).carry),
    ("\x00156", (fpMulBarrettL1 product).word)] ++
      fpReduceProductsEnv product

private def fpReduceL2Env (product : FullMulValue) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x00158", (fpMulBarrettL2 product).carry),
    ("\x00157", (fpMulBarrettL1 product).carry),
    ("\x00156", (fpMulBarrettL2 product).word)] ++
      fpReduceProductsEnv product

private def fpReduceScheduleEnv (product : FullMulValue) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x00158", (fpMulBarrettL2 product).carry),
    ("\x00157", (fpMulBarrettL3 product).carry),
    ("\x00156", (fpMulBarrettL2 product).word)] ++
      fpReduceProductLocals product ++ fpReduceQEnv product

theorem exec_fpReduceDecls (product : FullMulValue) (yst : EvmState) :
    Interp.execStmts Challenge.YulProof.ClosedEvm.exec 63 fpReduceBodyFuns
      (fpReduceInitialEnv product) yst [fpReduceStmt0, fpReduceStmt1] =
    .ok (fpReduceQDeclEnv product, yst, .normal) := by
  rfl

private theorem exec_fpReduceProducts (product : FullMulValue) (yst : EvmState) :
    Interp.execStmts Challenge.YulProof.ClosedEvm.exec 59 fpReduceQuotientFuns
      (fpReduceQDeclEnv product) yst (fpReduceQuotientBody.take 21) =
    .ok (fpReduceProductsEnv product, yst, .normal) := by
  rfl

private theorem exec_fpReduceL1 (product : FullMulValue) (yst : EvmState) :
    Interp.execStmts Challenge.YulProof.ClosedEvm.exec 38 fpReduceQuotientFuns
      (fpReduceProductsEnv product) yst (fpReduceAfterProducts.take 4) =
    .ok (fpReduceL1Env product, yst, .normal) := by
  rfl

private theorem exec_fpReduceL2 (product : FullMulValue) (yst : EvmState) :
    Interp.execStmts Challenge.YulProof.ClosedEvm.exec 34 fpReduceQuotientFuns
      (fpReduceL1Env product) yst ((fpReduceAfterProducts.drop 4).take 8) =
    .ok (fpReduceL2Env product, yst, .normal) := by
  rfl

private theorem exec_fpReduceL3 (product : FullMulValue) (yst : EvmState) :
    Interp.execStmts Challenge.YulProof.ClosedEvm.exec 26 fpReduceQuotientFuns
      (fpReduceL2Env product) yst (fpReduceAfterProducts.drop 12) =
    .ok (fpReduceScheduleEnv product, yst, .normal) := by
  rfl

private theorem exec_fpReduceL2L3 (product : FullMulValue) (yst : EvmState) :
    Interp.execStmts Challenge.YulProof.ClosedEvm.exec 34 fpReduceQuotientFuns
      (fpReduceL1Env product) yst (fpReduceAfterProducts.drop 4) =
    .ok (fpReduceScheduleEnv product, yst, .normal) := by
  rw [show fpReduceAfterProducts.drop 4 =
      (fpReduceAfterProducts.drop 4).take 8 ++
        fpReduceAfterProducts.drop 12 by rfl]
  exact Interp.execStmts_append_normal
    (E := Challenge.YulProof.ClosedEvm.exec) (n := 26)
    (funs := fpReduceQuotientFuns) (V := fpReduceL1Env product) (st := yst)
    (pre := (fpReduceAfterProducts.drop 4).take 8)
    (tail := fpReduceAfterProducts.drop 12) (by omega)
    (exec_fpReduceL2 product yst) (exec_fpReduceL3 product yst)

private theorem exec_fpReduceSchedule (product : FullMulValue) (yst : EvmState) :
    Interp.execStmts Challenge.YulProof.ClosedEvm.exec 38 fpReduceQuotientFuns
      (fpReduceProductsEnv product) yst fpReduceAfterProducts =
    .ok (fpReduceScheduleEnv product, yst, .normal) := by
  rw [show fpReduceAfterProducts = fpReduceAfterProducts.take 4 ++
      fpReduceAfterProducts.drop 4 by rfl]
  exact Interp.execStmts_append_normal
    (E := Challenge.YulProof.ClosedEvm.exec) (n := 34)
    (funs := fpReduceQuotientFuns) (V := fpReduceProductsEnv product)
    (st := yst) (pre := fpReduceAfterProducts.take 4)
    (tail := fpReduceAfterProducts.drop 4) (by omega)
    (exec_fpReduceL1 product yst)
    (exec_fpReduceL2L3 product yst)

private theorem exec_fpReduceQuotientStmts (product : FullMulValue)
    (yst : EvmState) :
    Interp.execStmts Challenge.YulProof.ClosedEvm.exec 59 fpReduceQuotientFuns
      (fpReduceQDeclEnv product) yst fpReduceQuotientBody =
    .ok (fpReduceScheduleEnv product, yst, .normal) := by
  rw [show fpReduceQuotientBody = fpReduceQuotientBody.take 21 ++
      fpReduceQuotientBody.drop 21 by rw [List.take_append_drop]]
  exact Interp.execStmts_append_normal
    (E := Challenge.YulProof.ClosedEvm.exec) (n := 38)
    (funs := fpReduceQuotientFuns) (V := fpReduceQDeclEnv product) (st := yst)
    (pre := fpReduceQuotientBody.take 21)
    (tail := fpReduceQuotientBody.drop 21) (by omega)
    (exec_fpReduceProducts product yst) (exec_fpReduceSchedule product yst)

theorem exec_fpReduceQuotient (product : FullMulValue) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 60 fpReduceBodyFuns
      (fpReduceQDeclEnv product) yst fpReduceStmt2 =
    .ok (fpReduceQEnv product, yst, .normal) := by
  rw [show fpReduceStmt2 = .block fpReduceQuotientBody by rfl,
    Interp.execStmt]
  change (do
    let (V, st, outcome) ← Interp.execStmts Challenge.YulProof.ClosedEvm.exec 59
      fpReduceQuotientFuns (fpReduceQDeclEnv product) yst fpReduceQuotientBody
    return (restore (fpReduceQDeclEnv product) V, st, outcome)) = _
  rw [exec_fpReduceQuotientStmts product yst]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
