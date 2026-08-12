import Challenge.Bls12381G2Add.ProofSupport
import Challenge.Bls12381G2Add.ProofSupport.YulDialect
import Challenge.EvmProof.ProfiledCorrectness

set_option warningAsError true

/-!
# Profiled Yul boundary for G2ADD

The source model permits only successful native MODEXP calls. The target
profile pins Osaka's challenge configuration, in which MODEXP is enabled and
the incumbent G2ADD precompile is disabled.
-/

namespace Challenge.Bls12381G2Add.ProofSupport.Yul

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof

theorem initialState_frameOK {code calldata : ByteArray} {gas : Nat}
    (hsize : code.size < 2 ^ 256) :
    FrameOK code (initialState code calldata gas) where
  hcode := rfl
  codeSmall := hsize
  fork := rfl
  noPrecompile := deployAddress_not_precompile
  callStack := rfl
  running := rfl

theorem initialState_profile {code calldata : ByteArray} {gas : Nat} :
    CallerProfile executionConfig (initialState code calldata gas) where
  depth := by simp [initialState]
  precompileConfig := rfl

end Challenge.Bls12381G2Add.ProofSupport.Yul
