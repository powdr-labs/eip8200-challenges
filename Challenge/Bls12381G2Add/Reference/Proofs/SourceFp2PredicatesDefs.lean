import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpInvExec
import Challenge.Bls12381.ProofSupport.Fp2Predicates

set_option warningAsError true

/-!
# Frozen G2ADD Fp2 predicate definitions

This module names the four-word memory representation and the three read-only
Fp2 helper bodies.  Execution is deliberately deferred to a separate module,
so downstream arithmetic can import the representation without unfolding the
source evaluator.
-/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fp2Funs : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock]

/-- Four source words at `ptr`, in EIP-2537 `c0.hi,c0.lo,c1.hi,c1.lo` order. -/
def fp2At (yst : EvmState) (ptr : U256) :
    Challenge.Bls12381.ProofSupport.Fp2.Repr :=
  { c0 :=
      { hi := YulEvmCompiler.conv (loadWord yst.memory ptr.toNat)
        lo := YulEvmCompiler.conv
          (loadWord yst.memory (ptr + BitVec.ofNat 256 32).toNat) }
    c1 :=
      { hi := YulEvmCompiler.conv
          (loadWord yst.memory (ptr + BitVec.ofNat 256 64).toNat)
        lo := YulEvmCompiler.conv
          (loadWord yst.memory (ptr + BitVec.ofNat 256 96).toNat) } }

@[simp] theorem fp2At_c0_hi (yst : EvmState) (ptr : U256) :
    (fp2At yst ptr).c0.hi =
      YulEvmCompiler.conv (loadWord yst.memory ptr.toNat) := rfl

@[simp] theorem fp2At_c0_lo (yst : EvmState) (ptr : U256) :
    (fp2At yst ptr).c0.lo = YulEvmCompiler.conv
      (loadWord yst.memory (ptr + BitVec.ofNat 256 32).toNat) := rfl

@[simp] theorem fp2At_c1_hi (yst : EvmState) (ptr : U256) :
    (fp2At yst ptr).c1.hi = YulEvmCompiler.conv
      (loadWord yst.memory (ptr + BitVec.ofNat 256 64).toNat) := rfl

@[simp] theorem fp2At_c1_lo (yst : EvmState) (ptr : U256) :
    (fp2At yst ptr).c1.lo = YulEvmCompiler.conv
      (loadWord yst.memory (ptr + BitVec.ofNat 256 96).toNat) := rfl

def fp2ValidValue (yst : EvmState) (ptr : U256) : U256 :=
  fpValidValue (loadWord yst.memory ptr.toNat)
      (loadWord yst.memory (ptr + BitVec.ofNat 256 32).toNat) &&&
    fpValidValue
      (loadWord yst.memory (ptr + BitVec.ofNat 256 64).toNat)
      (loadWord yst.memory (ptr + BitVec.ofNat 256 96).toNat)

def fp2ZeroValue (yst : EvmState) (ptr : U256) : U256 :=
  fpZeroValue (loadWord yst.memory ptr.toNat)
      (loadWord yst.memory (ptr + BitVec.ofNat 256 32).toNat) &&&
    fpZeroValue
      (loadWord yst.memory (ptr + BitVec.ofNat 256 64).toNat)
      (loadWord yst.memory (ptr + BitVec.ofNat 256 96).toNat)

def fp2EqValue (yst : EvmState) (a b : U256) : U256 :=
  fpEqValue (loadWord yst.memory a.toNat)
      (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)
      (loadWord yst.memory b.toNat)
      (loadWord yst.memory (b + BitVec.ofNat 256 32).toNat) &&&
    fpEqValue
      (loadWord yst.memory (a + BitVec.ofNat 256 64).toNat)
      (loadWord yst.memory (a + BitVec.ofNat 256 96).toNat)
      (loadWord yst.memory (b + BitVec.ofNat 256 64).toNat)
      (loadWord yst.memory (b + BitVec.ofNat 256 96).toNat)

private theorem fpZeroValue_zero_or_one (hi lo : U256) :
    fpZeroValue hi lo = 0 ∨ fpZeroValue hi lo = 1 := by
  simp only [
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpZeroValue,
    b2w]
  split <;> split <;> decide

private theorem fpEqValue_zero_or_one (ahi alo bhi blo : U256) :
    fpEqValue ahi alo bhi blo = 0 ∨ fpEqValue ahi alo bhi blo = 1 := by
  simp only [
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpEqValue,
    b2w]
  split <;> split <;> decide

theorem fp2ZeroValue_zero_or_one (yst : EvmState) (ptr : U256) :
    fp2ZeroValue yst ptr = 0 ∨ fp2ZeroValue yst ptr = 1 := by
  rcases fpZeroValue_zero_or_one (loadWord yst.memory ptr.toNat)
      (loadWord yst.memory (ptr + BitVec.ofNat 256 32).toNat) with h0 | h0 <;>
    rcases fpZeroValue_zero_or_one
      (loadWord yst.memory (ptr + BitVec.ofNat 256 64).toNat)
      (loadWord yst.memory (ptr + BitVec.ofNat 256 96).toNat) with h1 | h1 <;>
    unfold fp2ZeroValue
  all_goals
    rw [h0, h1]
    decide

theorem fp2EqValue_zero_or_one (yst : EvmState) (a b : U256) :
    fp2EqValue yst a b = 0 ∨ fp2EqValue yst a b = 1 := by
  rcases fpEqValue_zero_or_one (loadWord yst.memory a.toNat)
      (loadWord yst.memory (a + BitVec.ofNat 256 32).toNat)
      (loadWord yst.memory b.toNat)
      (loadWord yst.memory (b + BitVec.ofNat 256 32).toNat) with h0 | h0 <;>
    rcases fpEqValue_zero_or_one
      (loadWord yst.memory (a + BitVec.ofNat 256 64).toNat)
      (loadWord yst.memory (a + BitVec.ofNat 256 96).toNat)
      (loadWord yst.memory (b + BitVec.ofNat 256 64).toNat)
      (loadWord yst.memory (b + BitVec.ofNat 256 96).toNat) with h1 | h1 <;>
    unfold fp2EqValue
  all_goals
    rw [h0, h1]
    decide

def fp2ValidBody : Block Op :=
  match Compilation.referenceCompiledBlock[11]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fp2ValidDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0093"], rets := ["\x0094"], body := fp2ValidBody }

theorem lookup_fp2Valid : lookupFun fp2Funs "\x0011" =
    some (fp2ValidDecl, fp2Funs) := by rfl

def fp2ZeroBody : Block Op :=
  match Compilation.referenceCompiledBlock[12]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fp2ZeroDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0095"], rets := ["\x0096"], body := fp2ZeroBody }

theorem lookup_fp2Zero : lookupFun fp2Funs "\x0012" =
    some (fp2ZeroDecl, fp2Funs) := by rfl

def fp2EqBody : Block Op :=
  match Compilation.referenceCompiledBlock[13]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fp2EqDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0097", "\x0098"], rets := ["\x0099"], body := fp2EqBody }

theorem lookup_fp2Eq : lookupFun fp2Funs "\x0013" =
    some (fp2EqDecl, fp2Funs) := by rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
