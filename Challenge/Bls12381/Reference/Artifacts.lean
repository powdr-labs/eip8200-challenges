import Challenge.Bls12381.Reference.Provenance
import EvmSemantics.Data.Hex

set_option warningAsError true

/-!
# Frozen BLS12-381 Solidity baseline artifacts

The hexadecimal files contain deployed runtime bytecode rebuilt from the
pinned upstream Solidity commit. They are executable scorer candidates only:
none is certified, proved correct, or claimed to conform to EIP-2537.
-/

namespace Challenge.Bls12381.Reference

open EvmSemantics

structure BaselineArtifact where
  operation : String
  upstreamSource : String
  foundryOutput : String
  artifactPath : String
  runtimeSize : Nat
  runtimeSha256 : String
  runtimeHex : String

def BaselineArtifact.runtimeBytecode (artifact : BaselineArtifact) : ByteArray :=
  Hex.hexToBytes artifact.runtimeHex

def g1Add : BaselineArtifact where
  operation := "G1ADD"
  upstreamSource := "src/bls12381_g1add/G1AddDeployed.sol"
  foundryOutput := "out/G1AddDeployed.sol/G1AddDeployed.json"
  artifactPath := "Challenge/Bls12381/Reference/Artifacts/g1add.hex"
  runtimeSize := 7289
  runtimeSha256 := "d6cc935836e8d9d8fdd35c0996cc067597497c571b2319c8611a48148a3b5ab8"
  runtimeHex := (include_str "Artifacts/g1add.hex").trimAscii.copy

def g1Msm : BaselineArtifact where
  operation := "G1MSM"
  upstreamSource := "src/bls12381_g1msm/G1MsmDeployed.sol"
  foundryOutput := "out/G1MsmDeployed.sol/G1MsmDeployed.json"
  artifactPath := "Challenge/Bls12381/Reference/Artifacts/g1msm.hex"
  runtimeSize := 8903
  runtimeSha256 := "6dd7d069649a9361588dbeeb6b654e3184eb6fa09939e31d21ee9ae3323dbab0"
  runtimeHex := (include_str "Artifacts/g1msm.hex").trimAscii.copy

def g2Add : BaselineArtifact where
  operation := "G2ADD"
  upstreamSource := "src/bls12381_g2add/G2AddDeployed.sol"
  foundryOutput := "out/G2AddDeployed.sol/G2AddDeployed.json"
  artifactPath := "Challenge/Bls12381/Reference/Artifacts/g2add.hex"
  runtimeSize := 8082
  runtimeSha256 := "7dd357c7e60d1410f430d3cdd582de28cc6ae82d098e502c513051a09a4b6183"
  runtimeHex := (include_str "Artifacts/g2add.hex").trimAscii.copy

def g2Msm : BaselineArtifact where
  operation := "G2MSM"
  upstreamSource := "src/bls12381_g2msm/G2MsmDeployed.sol"
  foundryOutput := "out/G2MsmDeployed.sol/G2MsmDeployed.json"
  artifactPath := "Challenge/Bls12381/Reference/Artifacts/g2msm.hex"
  runtimeSize := 9314
  runtimeSha256 := "51e7efe0a1fd22cd1331ea6e4c8504656d83d8cf0df4def94bfbcf5b83607582"
  runtimeHex := (include_str "Artifacts/g2msm.hex").trimAscii.copy

def mapFpToG1 : BaselineArtifact where
  operation := "MAP_FP_TO_G1"
  upstreamSource := "src/bls12381_map_fp_to_g1/MapFpToG1Deployed.sol"
  foundryOutput := "out/MapFpToG1Deployed.sol/MapFpToG1Deployed.json"
  artifactPath := "Challenge/Bls12381/Reference/Artifacts/map_fp_to_g1.hex"
  runtimeSize := 15608
  runtimeSha256 := "535a624dab656a9993d611faafd46bf6b182c9dbc70d34f0e3f3eb17bd3850f2"
  runtimeHex := (include_str "Artifacts/map_fp_to_g1.hex").trimAscii.copy

def mapFp2ToG2 : BaselineArtifact where
  operation := "MAP_FP2_TO_G2"
  upstreamSource := "src/bls12381_map_fp_to_g2/MapFpToG2Deployed.sol"
  foundryOutput := "out/MapFpToG2Deployed.sol/MapFpToG2Deployed.json"
  artifactPath := "Challenge/Bls12381/Reference/Artifacts/map_fp2_to_g2.hex"
  runtimeSize := 13502
  runtimeSha256 := "4147307a2483c7d658fef667aaf616a012309a0c23f034d3d9458bc3becb51a1"
  runtimeHex := (include_str "Artifacts/map_fp2_to_g2.hex").trimAscii.copy

def pairing : BaselineArtifact where
  operation := "PAIRING"
  upstreamSource := "src/bls12381_pairing/PairingDeployed.sol"
  foundryOutput := "out/PairingDeployed.sol/PairingDeployed.json"
  artifactPath := "Challenge/Bls12381/Reference/Artifacts/pairing.hex"
  runtimeSize := 14788
  runtimeSha256 := "8baa8d30906be05778bd2739fdb40283b33b3b746a03d6e2394c2103e6f13b56"
  runtimeHex := (include_str "Artifacts/pairing.hex").trimAscii.copy

def artifacts : List BaselineArtifact :=
  [g1Add, g1Msm, g2Add, g2Msm, mapFpToG1, mapFp2ToG2, pairing]

end Challenge.Bls12381.Reference
