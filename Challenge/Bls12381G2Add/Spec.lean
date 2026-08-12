import EvmSemantics.EVM.BigStep
import Challenge.Bls12381.ProofSupport.CodecG2
import Challenge.Bls12381.ProofSupport.G2Affine

set_option warningAsError true

namespace Challenge.Bls12381G2Add

open EvmSemantics EvmSemantics.EVM

/-- Exact EIP-2537 G2ADD input length: two 256-byte decoded points. -/
def inputBytes : Nat := 2 * Challenge.Bls12381.ProofSupport.Codec.g2Bytes

/--
EIP-correct G2ADD adapter at the decoded affine boundary. Addition is routed
through the local lawful `Fp2` semantics and does not depend on the opaque
pinned inverse. Ordinary G2 decoding deliberately performs no prime-subgroup
check, as required by EIP-2537 G2ADD.
-/
def spec (input : ByteArray) : Option ByteArray :=
  if input.size ≠ inputBytes then none
  else do
    let left ← Challenge.Bls12381.ProofSupport.Codec.decodeG2 input 0
    let right ← Challenge.Bls12381.ProofSupport.Codec.decodeG2 input
      Challenge.Bls12381.ProofSupport.Codec.g2Bytes
    some (Challenge.Bls12381.ProofSupport.Codec.encodeG2
      (Challenge.Bls12381.ProofSupport.G2Affine.toWire
        (Challenge.Bls12381.ProofSupport.G2Affine.add
          (Challenge.Bls12381.ProofSupport.G2Affine.ofWire left)
          (Challenge.Bls12381.ProofSupport.G2Affine.ofWire right))))

theorem spec_eq_some_iff {input output : ByteArray} :
    spec input = some output ↔
      input.size = inputBytes ∧
      ∃ left right,
        Challenge.Bls12381.ProofSupport.Codec.decodeG2 input 0 = some left ∧
        Challenge.Bls12381.ProofSupport.Codec.decodeG2 input
          Challenge.Bls12381.ProofSupport.Codec.g2Bytes = some right ∧
        output = Challenge.Bls12381.ProofSupport.Codec.encodeG2
          (Challenge.Bls12381.ProofSupport.G2Affine.toWire
            (Challenge.Bls12381.ProofSupport.G2Affine.add
              (Challenge.Bls12381.ProofSupport.G2Affine.ofWire left)
              (Challenge.Bls12381.ProofSupport.G2Affine.ofWire right))) := by
  unfold spec
  by_cases hsize : input.size = inputBytes
  · rw [if_neg (not_not_intro hsize)]
    cases hleft : Challenge.Bls12381.ProofSupport.Codec.decodeG2 input 0 with
    | none => simp_all
    | some left =>
        cases hright : Challenge.Bls12381.ProofSupport.Codec.decodeG2 input
            Challenge.Bls12381.ProofSupport.Codec.g2Bytes with
        | none => simp_all
        | some right => simp_all [eq_comm]
  · rw [if_pos hsize]
    simp [hsize]

theorem spec_eq_none_iff {input : ByteArray} :
    spec input = none ↔
      input.size ≠ inputBytes ∨
      Challenge.Bls12381.ProofSupport.Codec.decodeG2 input 0 = none ∨
      Challenge.Bls12381.ProofSupport.Codec.decodeG2 input
        Challenge.Bls12381.ProofSupport.Codec.g2Bytes = none := by
  unfold spec
  by_cases hsize : input.size = inputBytes
  · rw [if_neg (not_not_intro hsize)]
    cases hleft : Challenge.Bls12381.ProofSupport.Codec.decodeG2 input 0 with
    | none => simp_all
    | some left =>
        cases hright : Challenge.Bls12381.ProofSupport.Codec.decodeG2 input
            Challenge.Bls12381.ProofSupport.Codec.g2Bytes with
        | none => simp_all
        | some right => simp_all
  · rw [if_pos hsize]
    simp [hsize]

theorem spec_invalid_length {input : ByteArray}
    (hsize : input.size ≠ inputBytes) : spec input = none := by
  exact spec_eq_none_iff.mpr (Or.inl hsize)

theorem spec_success {input : ByteArray}
    {left right : Crypto.Bls12381.G2Point}
    (hsize : input.size = inputBytes)
    (hleft : Challenge.Bls12381.ProofSupport.Codec.decodeG2 input 0 = some left)
    (hright : Challenge.Bls12381.ProofSupport.Codec.decodeG2 input
      Challenge.Bls12381.ProofSupport.Codec.g2Bytes = some right) :
    spec input = some (Challenge.Bls12381.ProofSupport.Codec.encodeG2
      (Challenge.Bls12381.ProofSupport.G2Affine.toWire
        (Challenge.Bls12381.ProofSupport.G2Affine.add
          (Challenge.Bls12381.ProofSupport.G2Affine.ofWire left)
          (Challenge.Bls12381.ProofSupport.G2Affine.ofWire right)))) := by
  apply spec_eq_some_iff.mpr
  exact ⟨hsize, left, right, hleft, hright, rfl⟩

def deployAddress : AccountAddress := AccountAddress.ofNat 0x820d

def executionConfig : PrecompileConfig :=
  { disabled := [Precompile.blsG2AddAddress] }

def initialState (code calldata : ByteArray) (gas : Nat) : EVM.State :=
  let account : Account := { Account.empty with code }
  let accounts := AccountMap.empty.set deployAddress account
  let env : ExecutionEnv := {
    (default : ExecutionEnv) with
    address := deployAddress
    codeAddr := deployAddress
    origin := AccountAddress.ofNat 0
    caller := AccountAddress.ofNat 0
    weiValue := 0
    calldata
    code
    gasPrice := 0
    depth := 0
    permitStateMutation := true
    blobVersionedHashes := #[]
    fork := .Osaka
    precompileConfig := executionConfig
  }
  { (default : EVM.State) with
    pc := 0
    stack := []
    execLength := 0
    halt := .Running
    callStack := []
    gasAvailable := gas
    activeWords := 0
    memory := .empty
    returnData := .empty
    hReturn := .empty
    accountMap := accounts
    substate := { Substate.empty with originalAccountMap := accounts }
    executionEnv := env }

def Matches (input : ByteArray) : ExecutionResult → Prop :=
  match spec input with
  | some output => fun result => result = .returned output
  | none => fun result => ∃ exception, result = .exception exception

def Correct (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, calldata.size < 2 ^ 64 →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
      ∃ result, Eval (initialState code calldata g) result ∧ Matches calldata result

end Challenge.Bls12381G2Add
