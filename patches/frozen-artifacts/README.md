# Yul compiler frozen-artifact compatibility

The repository pins the current `powdr-labs/yul-compiler` revision, but the
compiler's normal backend selector chooses SSA output for the SHA-256 and
RIPEMD-160 reference sources. Those outputs differ from the bytecode frozen in
this repository:

| reference | classic/frozen | upstream selection |
|---|---:|---:|
| SHA-256 | 1524 bytes | 1699 bytes |
| RIPEMD-160 | 1671 bytes | 1689 bytes |

`yul-compiler-classic-artifacts.patch` changes only backend selection in
`YulParser/Compile.lean`. It keeps using the compiler's verified classic
backend and leaves its optimizer, compiler, assembler, and correctness proofs
unchanged. MODEXP and BLAKE2f also continue to reproduce their frozen artifacts
byte-for-byte.

Run `scripts/apply-frozen-artifact-compiler-patch.sh` after `lake update` or
a fresh dependency checkout. The helper applies the patch idempotently and
fails if a future compiler revision changes the relevant code, so an upstream
update cannot silently compile different artifacts.

This patch can be removed once the upstream compiler exposes a supported
classic-backend option, or when this repository deliberately migrates its
frozen artifacts and bytecode proofs to the SSA output.
