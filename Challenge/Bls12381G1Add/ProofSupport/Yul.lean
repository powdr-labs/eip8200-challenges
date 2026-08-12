import Challenge.Bls12381G1Add.ProofSupport
import Challenge.Bls12381G1Add.ProofSupport.YulDialect
import Challenge.EvmProof.ProfiledCorrectness

set_option warningAsError true

/-!
# Profiled Yul boundary for G1ADD

The source model allows only successful native MODEXP calls.  The target
profile pins Osaka's challenge configuration, in which MODEXP is enabled and
the incumbent G1ADD precompile is disabled.
-/

namespace Challenge.Bls12381G1Add.ProofSupport.Yul

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof

/-- The challenge initial state is a valid top-level frame for any frozen
runtime satisfying the ordinary code-size bound. -/
theorem initialState_frameOK {code calldata : ByteArray} {gas : Nat}
    (hsize : code.size < 2 ^ 256) :
    FrameOK code (initialState code calldata gas) where
  hcode := rfl
  codeSmall := hsize
  fork := rfl
  noPrecompile := deployAddress_not_precompile
  callStack := rfl
  running := rfl

/-- The challenge initial state supplies the target-only facts required by
successful native MODEXP realization. -/
theorem initialState_profile {code calldata : ByteArray} {gas : Nat} :
  CallerProfile executionConfig (initialState code calldata gas) where
  depth := by simp [initialState]
  precompileConfig := rfl

end Challenge.Bls12381G1Add.ProofSupport.Yul
