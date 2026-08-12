import Challenge.Bls12381G2Msm.Reference.Source
import Challenge.Bls12381G2Msm.Reference.FrozenBytecode
import EvmSemantics.Data.Hex

set_option warningAsError true

namespace Challenge.Bls12381G2Msm

open EvmSemantics

/-- Frozen output of the proof-friendly direct compiler over the exact
normalized `reference.yul` block. -/
def referenceHex : String := (include_str "reference.hex").trimAscii.copy

/-- Source-hex decoding retained as an executable artifact regression. -/
def decodedReferenceBytecode : ByteArray := Hex.hexToBytes referenceHex

/-- Concrete runtime scored and proved by the G2MSM challenge. -/
def referenceBytecode : ByteArray := ByteArray.mk frozenReferenceBytes.toArray

def referenceBytecodeSize : Nat := 3264

end Challenge.Bls12381G2Msm

