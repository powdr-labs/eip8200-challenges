import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpInvExec
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpMulMemory
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpInvMemory

set_option warningAsError true

/-! Opaque scratch-memory preservation for the G2MSM scalar MODEXP helpers. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fpMulFinalState_readBytes_after_scratch (yst : EvmState)
    (ahi alo bhi blo : U256) (start size : Nat) (hstart : 1328 ≤ start) :
    readBytes (fpMulFinalState yst ahi alo bhi blo).memory start size =
      readBytes yst.memory start size :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpMulFinalState_readBytes_after_scratch
    yst ahi alo bhi blo start size hstart

theorem fpMulFinalState_loadWord_after_scratch (yst : EvmState)
    (ahi alo bhi blo : U256) (offset : Nat) (hstart : 1328 ≤ offset) :
    loadWord (fpMulFinalState yst ahi alo bhi blo).memory offset =
      loadWord yst.memory offset :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpMulFinalState_loadWord_after_scratch
    yst ahi alo bhi blo offset hstart

theorem fpInvFinalState_loadWord_before_scratch (yst : EvmState)
    (hi lo : U256) (offset : Nat) (hend : offset + 32 ≤ 1024) :
    loadWord (fpInvFinalState yst hi lo).memory offset =
      loadWord yst.memory offset :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpInvFinalState_loadWord_before_scratch
    yst hi lo offset hend

theorem fpInvFinalState_readBytes_after_scratch (yst : EvmState)
    (hi lo : U256) (start size : Nat) (hstart : 1328 ≤ start) :
    readBytes (fpInvFinalState yst hi lo).memory start size =
      readBytes yst.memory start size :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpInvFinalState_readBytes_after_scratch
    yst hi lo start size hstart

theorem fpInvFinalState_loadWord_after_scratch (yst : EvmState)
    (hi lo : U256) (offset : Nat) (hstart : 1328 ≤ offset) :
    loadWord (fpInvFinalState yst hi lo).memory offset =
      loadWord yst.memory offset :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpInvFinalState_loadWord_after_scratch
    yst hi lo offset hstart

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
