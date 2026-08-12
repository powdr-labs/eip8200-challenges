import Challenge.Bls12381G1Add.Reference.Proofs.SourceStore

set_option warningAsError true

open YulSemantics YulSemantics.EVM

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

example (ptr hi lo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCompiledBlock]
      [("ptr", ptr), ("hi", hi), ("lo", lo)] yst
      (.call "\x007" [.var "ptr", .var "hi", .var "lo"]) =
    .ok (.vals [] (storeFpState yst ptr hi lo)) :=
  eval_storeFp ptr hi lo yst

example (ptr : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64
      [hoist Challenge.EvmProof.modexpExec.toDialect
        Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCompiledBlock]
      [("ptr", ptr)] yst (.call "\x008" [.var "ptr"]) =
    .ok (.vals [] (storeFpState yst ptr fpModulusHiValue fpModulusLoValue)) :=
  eval_storeModulus ptr yst

example (ptr hi lo : U256) (yst : EvmState) (address : Nat) :
    (storeFpState yst ptr hi lo).memory address =
      storeWord
        (storeWord yst.memory ptr.toNat (hi <<< 128))
        (ptr + BitVec.ofNat 256 16).toNat lo address :=
  storeFpState_memory ptr hi lo yst address

example (ptr hi lo : U256) (yst : EvmState)
    (hptr : ptr.toNat + 16 < 2 ^ 256)
    (hhi : hi.toNat < 2 ^ 128) :
    Challenge.EvmProof.Bytes.bytesNat
        (readBytes (storeFpState yst ptr hi lo).memory ptr.toNat 48) =
      hi.toNat * 2 ^ 256 + lo.toNat :=
  bytesNat_readBytes_storeFpState ptr hi lo yst hptr hhi

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.bytesNat_readBytes_storeFpState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bytesNat_readBytes_storeFpState

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.storeFpState_memory' depends on axioms: [propext] -/
#guard_msgs in
#print axioms storeFpState_memory

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_storeFp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_storeFp

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_storeModulus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_storeModulus

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
