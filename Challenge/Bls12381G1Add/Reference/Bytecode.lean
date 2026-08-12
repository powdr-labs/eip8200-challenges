import Challenge.Bls12381G1Add.Reference.Source
import Challenge.Bls12381G1Add.Reference.FrozenBytecode
import EvmSemantics.Data.Hex

set_option warningAsError true

namespace Challenge.Bls12381G1Add

open EvmSemantics

/-- Frozen output of `lake exe yulc Challenge/Bls12381G1Add/Reference/reference.yul`. -/
def referenceHex : String := (include_str "reference.hex").trimAscii.copy

/-- Source-hex decoding retained as an executable artifact regression. -/
def decodedReferenceBytecode : ByteArray := Hex.hexToBytes referenceHex

/-- Concrete runtime scored and proved by the G1ADD challenge.  The explicit
byte list keeps assembly equality reducible in the kernel. -/
def referenceBytecode : ByteArray := ByteArray.mk frozenReferenceBytes.toArray

end Challenge.Bls12381G1Add
