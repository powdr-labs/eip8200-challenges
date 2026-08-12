import Challenge.Bls12381G1Msm.Reference.Source
import Challenge.Bls12381G1Msm.Reference.FrozenBytecode
import EvmSemantics.Data.Hex

set_option warningAsError true

namespace Challenge.Bls12381G1Msm

open EvmSemantics

/-- Frozen output of
`lake exe yulc Challenge/Bls12381G1Msm/Reference/reference.yul`. -/
def referenceHex : String := (include_str "reference.hex").trimAscii.copy

/-- Source-hex decoding retained as an executable artifact regression. -/
def decodedReferenceBytecode : ByteArray := Hex.hexToBytes referenceHex

/-- Frozen 3,688-byte concrete runtime used by the G1MSM challenge. -/
def referenceBytecode : ByteArray := ByteArray.mk frozenReferenceBytes.toArray

end Challenge.Bls12381G1Msm
