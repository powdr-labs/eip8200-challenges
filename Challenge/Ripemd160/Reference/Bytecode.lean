import Challenge.EvmProof.Bytecode
import Challenge.Ripemd160.Reference.Bytes
import EvmSemantics.Data.Hex
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# The frozen raw-EVM RIPEMD-160 artifact

`referenceBytecode` is the byte-for-byte output of:

```sh
lake exe yulc Challenge/Ripemd160/Reference/reference.yul
```

Correctness proofs target these bytes directly; the compiler is used to
reproduce the artifact, not as an assumption in the bytecode proof.
-/

namespace Challenge.Ripemd160

open EvmSemantics

def referenceHex : String := (include_str "reference.hex").trimAscii.copy

def referenceBytecode : ByteArray := referenceBytes

@[simp] theorem referenceBytecode_size : referenceBytecode.size = 1689 := by
  simp [referenceBytecode]

/-- The artifact now opens with the first packed permutation table `PUSH31`
rather than an entry trampoline. -/
@[simp] theorem referenceBytecode_get_zero : referenceBytecode[0] = 0x7e := by
  change referenceBytes[0] = 0x7e
  exact referenceBytes_get_zero

theorem referenceBytecode_roundtrip :
    Challenge.EvmProof.Bytecode.assemble
      (Challenge.EvmProof.Bytecode.disassemble referenceBytecode) = referenceBytecode :=
  Challenge.EvmProof.Bytecode.assemble_disassemble _

end Challenge.Ripemd160
