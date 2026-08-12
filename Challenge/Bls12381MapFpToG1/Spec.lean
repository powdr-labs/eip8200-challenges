import EvmSemantics.EVM.BigStep
import Challenge.Bls12381.ProofSupport.MapToG1Map

set_option warningAsError true

namespace Challenge.Bls12381MapFpToG1

open EvmSemantics EvmSemantics.EVM

/-- Exact EIP-2537 MAP_FP_TO_G1 input length: one padded Fp element. -/
def inputBytes : Nat := Challenge.Bls12381.ProofSupport.Codec.fpBytes

/--
Strict challenge adapter to the shared lawful MAP_FP_TO_G1 operation. The
shared adapter checks the exact 64-byte frame before decoding the canonical Fp
value, then applies projective SSWU, the pole-aware 11-isogeny, and naive
effective-cofactor multiplication.
-/
def spec (input : ByteArray) : Option ByteArray :=
  Challenge.Bls12381.ProofSupport.MapToG1.run input

theorem spec_eq_some_iff {input output : ByteArray} :
    spec input = some output ↔
      ∃ u, input.size = Challenge.Bls12381.ProofSupport.Codec.fpBytes ∧
        Challenge.Bls12381.ProofSupport.Codec.decodeFp input 0 = some u ∧
        output = Challenge.Bls12381.ProofSupport.Codec.encodeG1
          (Challenge.Bls12381.ProofSupport.G1Affine.toWire
            (Challenge.Bls12381.ProofSupport.MapToG1.map
              (Challenge.Bls12381.ProofSupport.PrimeField.finEquiv u))) := by
  exact Challenge.Bls12381.ProofSupport.MapToG1.run_eq_some_iff input output

theorem spec_eq_none_iff {input : ByteArray} :
    spec input = none ↔
      input.size ≠ Challenge.Bls12381.ProofSupport.Codec.fpBytes ∨
        Challenge.Bls12381.ProofSupport.Codec.decodeFp input 0 = none := by
  rw [Option.eq_none_iff_forall_some_ne]
  constructor
  · intro hnone
    by_contra haccept
    push Not at haccept
    obtain ⟨u, hdecode⟩ :=
      Option.ne_none_iff_exists.mp haccept.2
    let output := Challenge.Bls12381.ProofSupport.Codec.encodeG1
      (Challenge.Bls12381.ProofSupport.G1Affine.toWire
        (Challenge.Bls12381.ProofSupport.MapToG1.map
          (Challenge.Bls12381.ProofSupport.PrimeField.finEquiv u)))
    have hsuccess : spec input = some output :=
      spec_eq_some_iff.mpr ⟨u, haccept.1, hdecode.symm, rfl⟩
    exact hnone output hsuccess.symm
  · intro hrejected output heq
    obtain ⟨u, hsize, hdecode, _⟩ :=
      spec_eq_some_iff.mp heq.symm
    rcases hrejected with hwrongSize | hbadDecode
    · exact hwrongSize hsize
    · rw [hbadDecode] at hdecode
      contradiction

theorem spec_invalid_length {input : ByteArray}
    (hsize : input.size ≠ inputBytes) : spec input = none := by
  apply spec_eq_none_iff.mpr
  exact Or.inl hsize

theorem spec_success {input : ByteArray} {u : Crypto.Bls12381.Fp}
    (hsize : input.size = inputBytes)
    (hdecode : Challenge.Bls12381.ProofSupport.Codec.decodeFp input 0 = some u) :
    spec input = some (Challenge.Bls12381.ProofSupport.Codec.encodeG1
      (Challenge.Bls12381.ProofSupport.G1Affine.toWire
        (Challenge.Bls12381.ProofSupport.MapToG1.map
          (Challenge.Bls12381.ProofSupport.PrimeField.finEquiv u)))) := by
  apply spec_eq_some_iff.mpr
  exact ⟨u, hsize, hdecode, rfl⟩

def deployAddress : AccountAddress := AccountAddress.ofNat 0x8210

def executionConfig : PrecompileConfig :=
  { disabled := [Precompile.blsMapFpToG1Address] }

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

end Challenge.Bls12381MapFpToG1
