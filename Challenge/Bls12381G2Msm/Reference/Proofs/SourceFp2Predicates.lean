import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpMemory
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2PredicatesDefs

set_option warningAsError true

/-! Frozen G2MSM Fp2 predicate representation and execution. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

abbrev fp2At :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2At
abbrev fp2ValidValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2ValidValue
abbrev fp2ZeroValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2ZeroValue
abbrev fp2EqValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2EqValue

export Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
  (fp2At_c0_hi fp2At_c0_lo fp2At_c1_hi fp2At_c1_lo
    fp2ZeroValue_zero_or_one fp2EqValue_zero_or_one)

def fp2ReadState (yst : EvmState) (ptr : U256) : EvmState :=
  let s0 := touchMemory yst (ptr + BitVec.ofNat 256 96).toNat 32
  let s1 := touchMemory s0 (ptr + BitVec.ofNat 256 64).toNat 32
  let s2 := touchMemory s1 (ptr + BitVec.ofNat 256 32).toNat 32
  touchMemory s2 ptr.toNat 32

theorem fp2ReadState_memory (yst : EvmState) (ptr : U256) :
    (fp2ReadState yst ptr).memory = yst.memory := by
  rfl

def fp2EqReadState (yst : EvmState) (a b : U256) : EvmState :=
  let s0 := touchMemory yst (b + BitVec.ofNat 256 96).toNat 32
  let s1 := touchMemory s0 (b + BitVec.ofNat 256 64).toNat 32
  let s2 := touchMemory s1 (a + BitVec.ofNat 256 96).toNat 32
  let s3 := touchMemory s2 (a + BitVec.ofNat 256 64).toNat 32
  let s4 := touchMemory s3 (b + BitVec.ofNat 256 32).toNat 32
  let s5 := touchMemory s4 b.toNat 32
  let s6 := touchMemory s5 (a + BitVec.ofNat 256 32).toNat 32
  touchMemory s6 a.toNat 32

theorem fp2EqReadState_memory (yst : EvmState) (a b : U256) :
    (fp2EqReadState yst a b).memory = yst.memory := by
  rfl

def fp2Funs : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [hoist Challenge.EvmProof.modexpExec.toDialect referenceCompiledBlock]

def fp2ValidBody : Block Op :=
  match referenceCompiledBlock[11]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fp2ValidDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0099"], rets := ["\x00100"], body := fp2ValidBody }

theorem lookup_fp2Valid : lookupFun fp2Funs "\x0011" =
    some (fp2ValidDecl, fp2Funs) := by rfl

def fp2ZeroBody : Block Op :=
  match referenceCompiledBlock[12]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fp2ZeroDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00101"], rets := ["\x00102"], body := fp2ZeroBody }

theorem lookup_fp2Zero : lookupFun fp2Funs "\x0012" =
    some (fp2ZeroDecl, fp2Funs) := by rfl

def fp2EqBody : Block Op :=
  match referenceCompiledBlock[13]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fp2EqDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00103", "\x00104"], rets := ["\x00105"],
    body := fp2EqBody }

theorem lookup_fp2Eq : lookupFun fp2Funs "\x0013" =
    some (fp2EqDecl, fp2Funs) := by rfl

theorem eval_fp2Valid (ptr : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2Funs
      [("a", ptr)] yst (.call "\x0011" [.var "a"]) =
    .ok (.vals [fp2ValidValue yst ptr] (fp2ReadState yst ptr)) := by
  rw [Interp.evalExpr]
  rfl

theorem eval_fp2Zero (ptr : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2Funs
      [("a", ptr)] yst (.call "\x0012" [.var "a"]) =
    .ok (.vals [fp2ZeroValue yst ptr] (fp2ReadState yst ptr)) := by
  rw [Interp.evalExpr]
  rfl

theorem eval_fp2Eq (a b : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2Funs
      [("a", a), ("b", b)] yst
      (.call "\x0013" [.var "a", .var "b"]) =
    .ok (.vals [fp2EqValue yst a b] (fp2EqReadState yst a b)) := by
  rw [Interp.evalExpr]
  rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
