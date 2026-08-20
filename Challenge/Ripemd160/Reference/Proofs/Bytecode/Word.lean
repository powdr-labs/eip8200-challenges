import Challenge.EvmProof.Word
import Mathlib.Tactic.IntervalCases
set_option warningAsError true
/-!
# RIPEMD-160 operations as EVM word expressions

These expressions mirror the reference Yul helpers.  They form the reusable
word-level boundary for the direct bytecode proof: once the EVM operands are
known to be embedded 32-bit words, the lemmas below rewrite an opcode result
to the corresponding operation in `EvmSemantics.Crypto.Ripemd160`.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.Word

open EvmSemantics
open Challenge.EvmProof.Word

abbrev EWord := EvmSemantics.UInt256

def evmRotl32 (x : EWord) (n : Nat) : EWord :=
  mask32 (UInt256.shiftLeft x (UInt256.ofNat n) |||
    UInt256.shiftRight x (UInt256.ofNat (32 - n)))

def evmF (j : Nat) (x y z : EWord) : EWord :=
  match j with
  | 0 => (x ^^^ y) ^^^ z
  | 1 => (x &&& y) ||| (~~~x &&& z)
  | 2 => mask32 ((x ||| ~~~y) ^^^ z)
  | 3 => (x &&& z) ||| (y &&& ~~~z)
  | _ => mask32 (x ^^^ (y ||| ~~~z))

@[simp] theorem evmRotl32_ofUInt32 (x : UInt32) (n : Nat)
    (hn0 : 0 < n) (hn : n < 32) :
    evmRotl32 (ofUInt32 x) n =
      ofUInt32 (Crypto.Ripemd160.rotl32 x n) := by
  exact Challenge.EvmProof.Word.evm_rotl32 x n hn0 hn

private theorem notAnd_ofUInt32 (x z : UInt32) :
    (~~~ofUInt32 x) &&& ofUInt32 z =
      ofUInt32 (Crypto.Ripemd160.bnot32 x &&& z) := by
  rw [and_ofUInt32, toUInt32_not_ofUInt32]
  rfl

private theorem andNot_ofUInt32 (x z : UInt32) :
    ofUInt32 x &&& ~~~ofUInt32 z =
      ofUInt32 (x &&& Crypto.Ripemd160.bnot32 z) := by
  rw [word_and_comm, notAnd_ofUInt32, UInt32.and_comm]

@[simp] theorem evmF_ofUInt32 (j : Nat) (x y z : UInt32) (hj : j < 5) :
    evmF j (ofUInt32 x) (ofUInt32 y) (ofUInt32 z) =
      ofUInt32 (Crypto.Ripemd160.f j x y z) := by
  interval_cases j <;>
    grind [evmF, Crypto.Ripemd160.f, notAnd_ofUInt32, andNot_ofUInt32,
      mask32_xor, toUInt32_not_ofUInt32, Crypto.Ripemd160.bnot32,
      ofUInt32_xor, ofUInt32_or, ofUInt32_and, toUInt32_or,
      toUInt32_ofUInt32]

end Challenge.Ripemd160.Reference.Proofs.Bytecode.Word
