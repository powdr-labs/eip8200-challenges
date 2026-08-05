import Challenge.EvmProof.Bytecode
import Challenge.Sha256.Reference.Bytes
import EvmSemantics.Data.Hex
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# The frozen raw-EVM SHA-256 artifact

`referenceBytecode` is the byte-for-byte output of:

```sh
lake exe yulc Challenge/Sha256/Reference/reference.yul
```

The compiler is used only to generate the artifact. direct-bytecode proofs target
these frozen bytes and reason through `EvmSemantics.EVM.Step`; they do not
appeal to compiler correctness.
-/

namespace Challenge.Sha256

open EvmSemantics
/-- The canonical hexadecimal form of the submitted artifact. -/
def referenceHex : String :=
  (include_str "reference.hex").trimAscii.copy

/-- The submitted SHA-256 bytecode. Its literal form is definitionally
reducible for direct `stepF` proofs; CI pins it to `reference.hex`. -/
def referenceBytecode : ByteArray := referenceBytes

@[simp] theorem referenceBytecode_size : referenceBytecode.size = 1699 := by
  simp [referenceBytecode]

/-- The artifact now opens with the first packed round-constant `PUSH32`
rather than an entry trampoline. -/
@[simp] theorem referenceBytecode_get_zero : referenceBytecode[0] = 0x7f := by
  change referenceBytes[0] = 0x7f
  exact referenceBytes_get_zero

/-- The generic direct-bytecode disassembler round-trips the frozen artifact. -/
theorem referenceBytecode_roundtrip :
    Challenge.EvmProof.Bytecode.assemble
      (Challenge.EvmProof.Bytecode.disassemble referenceBytecode) = referenceBytecode :=
  Challenge.EvmProof.Bytecode.assemble_disassemble _

end Challenge.Sha256
