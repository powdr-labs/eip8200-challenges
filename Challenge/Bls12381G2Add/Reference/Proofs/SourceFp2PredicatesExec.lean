import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2PredicatesDefs

set_option warningAsError true

/-! # Frozen G2ADD Fp2 predicate execution -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- Memory-touch order for one four-word Fp2 read.  Arguments are evaluated
right-to-left by the source interpreter. -/
def fp2ReadState (yst : EvmState) (ptr : U256) : EvmState :=
  let s0 := touchMemory yst (ptr + BitVec.ofNat 256 96).toNat 32
  let s1 := touchMemory s0 (ptr + BitVec.ofNat 256 64).toNat 32
  let s2 := touchMemory s1 (ptr + BitVec.ofNat 256 32).toNat 32
  touchMemory s2 ptr.toNat 32

theorem fp2ReadState_memory (yst : EvmState) (ptr : U256) :
    (fp2ReadState yst ptr).memory = yst.memory := by
  rfl

/-- Memory-touch order for the eight loads in one Fp2 equality. -/
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

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

