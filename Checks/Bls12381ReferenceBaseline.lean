import Challenge.Bls12381.Reference
import Challenge.Bls12381G1Add.Scorer
import Challenge.Bls12381G1Msm.Scorer
import Challenge.Bls12381G2Add.Scorer
import Challenge.Bls12381G2Msm.Scorer
import Challenge.Bls12381MapFpToG1.Scorer
import Challenge.Bls12381MapFp2ToG2.Scorer
import Challenge.Bls12381Pairing.Scorer
import EvmSemantics.Crypto.Sha256

set_option warningAsError true

namespace Checks.Bls12381ReferenceBaseline

open Challenge.Bls12381.Reference

example : artifacts.length = 7 := by
  native_decide

example : artifacts.map (fun artifact => artifact.runtimeBytecode.size) =
    [7289, 8903, 8082, 9314, 15608, 13502, 14788] := by
  native_decide

example : artifacts.all (fun artifact => artifact.runtimeBytecode.size = artifact.runtimeSize) := by
  native_decide

example : upstreamCommit = "a6da8572fee65cac4318b96fcf18f171d7587c21" := by
  native_decide

example : compilerVersion = "0.8.35+commit.47b9dedd" := by
  native_decide

example : forgeStdCommit = "0844d7e1fc5e60d77b68e469bff60265f236c398" := by
  native_decide

example : openzeppelinCommit = "fcbae5394ae8ad52d8e580a3477db99814b9d565" := by
  native_decide

example : generalLimitations.contains rejectionSemanticsLimitation := by
  native_decide

example : artifacts.map (fun artifact =>
    EvmSemantics.Crypto.Sha256.hash artifact.runtimeBytecode) =
    artifacts.map (fun artifact => EvmSemantics.Hex.hexToBytes artifact.runtimeSha256) := by
  native_decide

example :
    [ Challenge.Bls12381G1Add.Scorer.baselineArtifact.operation
    , Challenge.Bls12381G1Msm.Scorer.baselineArtifact.operation
    , Challenge.Bls12381G2Add.Scorer.baselineArtifact.operation
    , Challenge.Bls12381G2Msm.Scorer.baselineArtifact.operation
    , Challenge.Bls12381MapFpToG1.Scorer.baselineArtifact.operation
    , Challenge.Bls12381MapFp2ToG2.Scorer.baselineArtifact.operation
    , Challenge.Bls12381Pairing.Scorer.baselineArtifact.operation ] =
    ["G1ADD", "G1MSM", "G2ADD", "G2MSM", "MAP_FP_TO_G1", "MAP_FP2_TO_G2", "PAIRING"] := by
  native_decide

end Checks.Bls12381ReferenceBaseline
