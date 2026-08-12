import Challenge.Bls12381G2Add.ProofSupport.Yul
import Challenge.EvmProof.Bytes

set_option warningAsError true

/-! # Concrete G2ADD source/target initial-state bridge -/

namespace Challenge.Bls12381G2Add.ProofSupport.Yul

open EvmSemantics EvmSemantics.EVM
open YulSemantics.EVM
open YulEvmCompiler

private def unconv (v : UInt256) : U256 :=
  BitVec.ofNat 256 v.toNat

private theorem conv_unconv (v : UInt256) : conv (unconv v) = v := by
  apply u256ext
  rw [conv_toNat, unconv, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt v.val.isLt

/-- The gas-free Yul state corresponding exactly to the challenge's concrete
top-level EVM frame. Its read-only world projections are taken from that
frame rather than postulated independently. -/
def sourceInitialState (code calldata : ByteArray) : EvmState :=
  let s := Challenge.Bls12381G2Add.initialState code calldata 0
  { EvmState.init with
    env := {
      EvmState.init.env with
      address := unconv s.executionEnv.address.toUInt256
      origin := unconv s.executionEnv.origin.toUInt256
      caller := unconv s.executionEnv.caller.toUInt256
      callvalue := unconv s.executionEnv.weiValue
      gasprice := unconv s.executionEnv.gasPrice
      selfBalance := unconv (s.accountMap s.executionEnv.address).balance
      createdThisTx := !(s.substate.originalAccountMap
        s.executionEnv.address).isContract
      static := !s.executionEnv.permitStateMutation
      coinbase := unconv s.executionEnv.header.coinbase.toUInt256
      timestamp := unconv s.executionEnv.header.timestamp
      number := unconv s.executionEnv.header.number
      prevrandao := unconv s.executionEnv.header.prevRandao
      gaslimit := unconv s.executionEnv.header.gasLimit
      chainid := unconv s.executionEnv.header.chainId
      basefee := unconv s.executionEnv.header.baseFeePerGas
      blobbasefee := unconv s.executionEnv.header.blobBaseFee
      calldata := calldata.toList
      code := code.toList
      keccakOf := targetKeccakOracle
      balanceOf := fun a => unconv
        (s.accountMap (AccountAddress.ofUInt256 (conv a))).balance
      extCodeOf := fun a =>
        (s.accountMap (AccountAddress.ofUInt256 (conv a))).code.toList
      extCodeHashOf := fun a => unconv
        (s.accountMap (AccountAddress.ofUInt256 (conv a))).codeHash
      nonceOf := fun a => unconv
        (s.accountMap (AccountAddress.ofUInt256 (conv a))).nonce
      storageOf := fun a k => unconv
        ((s.accountMap (AccountAddress.ofUInt256 (conv a))).storage.get (conv k))
      transientOf := fun a k => unconv
        ((s.accountMap (AccountAddress.ofUInt256 (conv a))).tstorage.get (conv k))
      blockHashOf := fun n => unconv (s.executionEnv.header.blockHash (conv n))
      blobHashOf := fun i => unconv
        (s.executionEnv.blobVersionedHashes[(conv i).toNat]?.getD 0) }
    storage := fun k => unconv
      ((s.accountMap s.executionEnv.address).storage.get (conv k))
    transient := fun k => unconv
      ((s.accountMap s.executionEnv.address).tstorage.get (conv k)) }

/-- The explicit source initial state satisfies every field of the compiler's
full machine-state correspondence with the concrete challenge frame. -/
theorem sourceInitialState_matches (code calldata : ByteArray) (gas : Nat) :
    StateMatch (sourceInitialState code calldata)
      (Challenge.Bls12381G2Add.initialState code calldata gas) := by
  constructor
  · exact MemMatch.init
  · intro k
    exact conv_unconv _
  · intro k
    exact conv_unconv _
  · exact Challenge.EvmProof.Bytes.memMatch_toList calldata
  · constructor
    · simp [sourceInitialState, Challenge.Bls12381G2Add.initialState,
        YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList]
    · exact targetKeccakOracle_agrees
    all_goals simp [sourceInitialState, Challenge.Bls12381G2Add.initialState,
      conv_unconv]
  · exact Challenge.EvmProof.Bytes.memMatch_toList code
  · simp [sourceInitialState, Challenge.Bls12381G2Add.initialState,
      YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList]
  · exact conv_unconv _
  · intro a
    exact conv_unconv _
  · rfl
  · exact MemMatch.init
  · rfl
  · constructor
    · intro a
      simpa [sourceInitialState, Challenge.Bls12381G2Add.initialState] using
        (Challenge.EvmProof.Bytes.memMatch_toList
          ((Challenge.Bls12381G2Add.initialState code calldata gas).accountMap
            (AccountAddress.ofUInt256 (conv a))).code)
    · intro a
      simp [sourceInitialState, Challenge.Bls12381G2Add.initialState,
        YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList]
    · intro a
      let account :=
        (Challenge.Bls12381G2Add.initialState code calldata gas).accountMap
          (AccountAddress.ofUInt256 (conv a))
      have hnonce : (unconv account.nonce).toNat = account.nonce.toNat := by
        rw [unconv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        exact account.nonce.val.isLt
      have hbalance : (unconv account.balance).toNat = account.balance.toNat := by
        rw [unconv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        exact account.balance.val.isLt
      change conv (if (unconv account.nonce).toNat = 0 ∧
          (unconv account.balance).toNat = 0 ∧ account.code.toList.length = 0
        then 0 else targetKeccakOracle account.code.toList) = account.codeHash
      rw [hnonce, hbalance]
      have hlength : account.code.toList.length = 0 ↔ account.code.size = 0 := by
        simp [YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList]
      simp only [hlength]
      cases he : account.isEmpty with
      | false =>
        have hnot : ¬(account.nonce.toNat = 0 ∧
            account.balance.toNat = 0 ∧ account.code.size = 0) := by
          intro h
          have : account.isEmpty = true := by
            simp [Account.isEmpty, h.1, h.2.1, h.2.2]
          rw [he] at this
          contradiction
        rw [if_neg hnot]
        simp [Account.codeHash, he, targetKeccakOracle_agrees, mkCode_toList]
      | true =>
        have hall : account.nonce.toNat = 0 ∧
            account.balance.toNat = 0 ∧ account.code.size = 0 := by
          have he' : (account.nonce.toNat = 0 ∧
              account.balance.toNat = 0) ∧
              account.code = ByteArray.empty := by
            simpa [Account.isEmpty, Bool.and_eq_true] using he
          exact ⟨he'.1.1, he'.1.2, by rw [he'.2]; rfl⟩
        rw [if_pos hall]
        simpa [Account.codeHash, he] using conv_zero
    · intro a
      exact conv_unconv _
    · intro a k
      exact conv_unconv _
    · intro a k
      exact conv_unconv _
  · exact .nil
  · exact .nil
  · rfl

end Challenge.Bls12381G2Add.ProofSupport.Yul
