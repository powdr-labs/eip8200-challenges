import Challenge.EvmProof.Bytecode
import Challenge.Blake2f.Reference.Bytes
import EvmSemantics.Data.Hex
set_option warningAsError true
set_option maxRecDepth 10000

namespace Challenge.Blake2f

def referenceHex : String := (include_str "reference.hex").trimAscii.copy

def referenceBytecode : ByteArray := referenceBytes

@[simp] theorem referenceBytecode_size : referenceBytecode.size = 1169 := by
  exact referenceBytes_size

theorem referenceBytecode_roundtrip :
    Challenge.EvmProof.Bytecode.assemble
      (Challenge.EvmProof.Bytecode.disassemble referenceBytecode) = referenceBytecode :=
  Challenge.EvmProof.Bytecode.assemble_disassemble _

end Challenge.Blake2f
