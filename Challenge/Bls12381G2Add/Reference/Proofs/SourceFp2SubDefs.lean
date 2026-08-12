import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddRefinement

set_option warningAsError true

/-!
# Frozen G2ADD `fp2Sub` boundary

This module freezes the six source statements and names their exact memory
graph.  In particular, the second component is read after the first component
has been stored.  That distinction preserves the source program's behaviour
even for aliased pointers, without exposing the evaluator to later proofs.
-/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fp2SubFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect := fp2Funs

def fp2SubBody : Block Op :=
  match Compilation.referenceCompiledBlock[15]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fp2SubStmt0 : Stmt Op := fp2SubBody[0]!
def fp2SubStmt1 : Stmt Op := fp2SubBody[1]!
def fp2SubStmt2 : Stmt Op := fp2SubBody[2]!
def fp2SubStmt3 : Stmt Op := fp2SubBody[3]!
def fp2SubStmt4 : Stmt Op := fp2SubBody[4]!
def fp2SubStmt5 : Stmt Op := fp2SubBody[5]!

theorem fp2SubBody_eq : fp2SubBody =
    [fp2SubStmt0, fp2SubStmt1, fp2SubStmt2,
      fp2SubStmt3, fp2SubStmt4, fp2SubStmt5] := by
  rfl

theorem hoist_fp2SubBody :
    hoist Challenge.EvmProof.modexpExec.toDialect fp2SubBody = [] := by
  rfl

def fp2SubBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: fp2SubFuns

theorem fp2SubBodyFuns_eq :
    hoist Challenge.EvmProof.modexpExec.toDialect fp2SubBody :: fp2SubFuns =
      fp2SubBodyFuns := by
  rw [hoist_fp2SubBody]
  rfl

def fp2SubDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00105", "\x00106", "\x00107"]
    rets := []
    body := fp2SubBody }

theorem lookup_fp2Sub : lookupFun fp2SubFuns "\x0015" =
    some (fp2SubDecl, fp2SubFuns) := by
  rfl

def fp2SubInitialEnv (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00105", out), ("\x00106", a), ("\x00107", b)]

private def mstoreState (yst : EvmState) (offset value : U256) : EvmState :=
  { touchMemory yst offset.toNat 32 with
    memory := storeWord yst.memory offset.toNat value }

/-- Four scalar limbs loaded for a call to `fpSub`.  The source interpreter
evaluates call arguments from right to left. -/
def fp2SubReadState (yst : EvmState)
    (ahi alo bhi blo : U256) : EvmState :=
  let s0 := touchMemory yst blo.toNat 32
  let s1 := touchMemory s0 bhi.toNat 32
  let s2 := touchMemory s1 alo.toNat 32
  touchMemory s2 ahi.toNat 32

theorem fp2SubReadState_memory (yst : EvmState) (ahi alo bhi blo : U256) :
    (fp2SubReadState yst ahi alo bhi blo).memory = yst.memory := by
  rfl

/-- The first Fp component is read from the incoming state. -/
def fp2SubC0 (yst : EvmState) (a b : U256) : U256 × U256 :=
  fpSubValue
    (loadWord yst.memory a.toNat)
    (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)
    (loadWord yst.memory b.toNat)
    (loadWord yst.memory (b + BitVec.ofNat 256 32).toNat)

def fp2SubAfterC0Reads (yst : EvmState) (a b : U256) : EvmState :=
  fp2SubReadState yst a (a + BitVec.ofNat 256 32)
    b (b + BitVec.ofNat 256 32)

def fp2SubAfterC0High (yst : EvmState) (out a b : U256) : EvmState :=
  mstoreState (fp2SubAfterC0Reads yst a b) out (fp2SubC0 yst a b).1

def fp2SubAfterC0Stores (yst : EvmState) (out a b : U256) : EvmState :=
  mstoreState (fp2SubAfterC0High yst out a b)
    (out + BitVec.ofNat 256 32) (fp2SubC0 yst a b).2

/-- The second Fp component is intentionally read after the first component's
stores, so this graph remains exact for arbitrary pointer aliasing. -/
def fp2SubC1 (yst : EvmState) (out a b : U256) : U256 × U256 :=
  let s := fp2SubAfterC0Stores yst out a b
  fpSubValue
    (loadWord s.memory (a + BitVec.ofNat 256 64).toNat)
    (loadWord s.memory (a + BitVec.ofNat 256 96).toNat)
    (loadWord s.memory (b + BitVec.ofNat 256 64).toNat)
    (loadWord s.memory (b + BitVec.ofNat 256 96).toNat)

def fp2SubAfterC1Reads (yst : EvmState) (out a b : U256) : EvmState :=
  fp2SubReadState (fp2SubAfterC0Stores yst out a b)
    (a + BitVec.ofNat 256 64) (a + BitVec.ofNat 256 96)
    (b + BitVec.ofNat 256 64) (b + BitVec.ofNat 256 96)

def fp2SubAfterC1High (yst : EvmState) (out a b : U256) : EvmState :=
  mstoreState (fp2SubAfterC1Reads yst out a b)
    (out + BitVec.ofNat 256 64) (fp2SubC1 yst out a b).1

def fp2SubFinalState (yst : EvmState) (out a b : U256) : EvmState :=
  mstoreState (fp2SubAfterC1High yst out a b)
    (out + BitVec.ofNat 256 96) (fp2SubC1 yst out a b).2

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
