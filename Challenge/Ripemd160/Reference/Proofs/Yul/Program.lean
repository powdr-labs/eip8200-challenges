import Challenge.Ripemd160.ProofSupport.Yul
import Challenge.Ripemd160.Reference.Source
import YulSemantics.Syntax

set_option warningAsError true

/-!
# Auditable AST for the verified RIPEMD-160 Yul source

This is the proof-side representation of `Reference/reference.yul`. Keeping it as Yul concrete
syntax (rather than an expanded constructor term) makes procedure contracts readable and prevents
the runtime parser from being unfolded during every semantic proof.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Yul

open YulSemantics
open YulSemantics.EVM

def verifiedProgram : Block Op := yul% {
  function rotl(x, n) -> r {
    r := and(or(shl(n, x), shr(sub(32, n), x)), 0xffffffff)
  }
  function hAt(i) -> v { v := mload(add(0x20, mul(i, 32))) }
  function hSet(i, v) { mstore(add(0x20, mul(i, 32)), and(v, 0xffffffff)) }
  function stAt(base, i) -> v { v := mload(add(base, mul(i, 32))) }
  function stSet(base, i, v) { mstore(add(base, mul(i, 32)), and(v, 0xffffffff)) }
  function xAt(i) -> v { v := mload(add(0x2a0, mul(i, 32))) }
  function xSet(i, v) { mstore(add(0x2a0, mul(i, 32)), and(v, 0xffffffff)) }
  function tableAt(base, i) -> v {
    v := byte(mod(i, 32), mload(add(base, mul(div(i, 32), 32))))
  }
  function f(j, x, y, z) -> v {
    switch j
    case 0 { v := xor(xor(x, y), z) }
    case 1 { v := or(and(x, y), and(not(x), z)) }
    case 2 { v := and(xor(or(x, not(y)), z), 0xffffffff) }
    case 3 { v := or(and(x, z), and(y, not(z))) }
    default { v := and(xor(x, or(y, not(z))), 0xffffffff) }
  }
  function round(base, j, wordIndex, rotation, k) {
    let a := stAt(base, 0)
    let b := stAt(base, 1)
    let c := stAt(base, 2)
    let d := stAt(base, 3)
    let e := stAt(base, 4)
    let t := and(add(add(add(a, f(j, b, c, d)), xAt(wordIndex)), k), 0xffffffff)
    t := and(add(rotl(t, rotation), e), 0xffffffff)
    stSet(base, 0, e)
    stSet(base, 4, d)
    stSet(base, 3, rotl(c, 10))
    stSet(base, 2, b)
    stSet(base, 1, t)
  }
  function readLE32(off) -> v {
    let w := mload(off)
    v := or(or(byte(0, w), shl(8, byte(1, w))),
            or(shl(16, byte(2, w)), shl(24, byte(3, w))))
  }
  function initTables() {
    mstore(0x4a0, 0x000102030405060708090a0b0c0d0e0f07040d010a060f030c000905020e0b08)
    mstore(0x4c0, 0x030a0e04090f0801020700060d0b050c01090b0a00080c040d03070f0e050602)
    mstore(0x4e0, 0x04000509070c020a0e0103080b060f0d00000000000000000000000000000000)
    mstore(0x500, 0x050e070009020b040d060f08010a030c060b0307000d050a0e0f080c04090102)
    mstore(0x520, 0x0f050103070e06090b080c020a00040d08060401030b0f00050c020d09070a0e)
    mstore(0x540, 0x0c0f0a040105080706020d0e0003090b00000000000000000000000000000000)
    mstore(0x560, 0x0b0e0f0c050807090b0d0e0f060709080706080d0b09070f070c0f090b070d0c)
    mstore(0x580, 0x0b0d06070e090d0f0e080d06050c07050b0c0e0f0e0f0908090e05060806050c)
    mstore(0x5a0, 0x090f050b06080d0c050c0d0e0b08050600000000000000000000000000000000)
    mstore(0x5c0, 0x0809090b0d0f0f050707080b0e0e0c06090d0f070c08090b07070c07060f0d0b)
    mstore(0x5e0, 0x09070f0b0806060e0c0d050e0d0d07050f05080b0e0e060e06090c090c050f08)
    mstore(0x600, 0x08050c090c050e06080d06050f0d0b0b00000000000000000000000000000000)
    mstore(0x620, 0x00000000)
    mstore(0x640, 0x5a827999)
    mstore(0x660, 0x6ed9eba1)
    mstore(0x680, 0x8f1bbcdc)
    mstore(0x6a0, 0xa953fd4e)
    mstore(0x6c0, 0x50a28be6)
    mstore(0x6e0, 0x5c4dd124)
    mstore(0x700, 0x6d703ef3)
    mstore(0x720, 0x7a6d76e9)
    mstore(0x740, 0x00000000)
  }
  function initH() {
    hSet(0, 0x67452301)
    hSet(1, 0xefcdab89)
    hSet(2, 0x98badcfe)
    hSet(3, 0x10325476)
    hSet(4, 0xc3d2e1f0)
  }
  function pad() -> paddedLen {
    let n := calldatasize()
    paddedLen := mul(div(add(n, 72), 64), 64)
    calldatacopy(0x800, 0, n)
    mstore8(add(0x800, n), 0x80)
    let bitLen := mul(n, 8)
    let lenOff := add(0x800, sub(paddedLen, 8))
    for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
      mstore8(add(lenOff, i), and(shr(mul(8, i), bitLen), 0xff))
    }
  }
  function schedule(msgOff) {
    for { let i := 0 } lt(i, 16) { i := add(i, 1) } {
      xSet(i, readLE32(add(msgOff, mul(i, 4))))
    }
  }
  function compress(msgOff) {
    schedule(msgOff)
    mcopy(0x0c0, 0x020, 0x0a0)
    mcopy(0x160, 0x020, 0x0a0)
    mcopy(0x200, 0x020, 0x0a0)
    for { let i := 0 } lt(i, 80) { i := add(i, 1) } {
      let j := div(i, 16)
      round(0x0c0, j, tableAt(0x4a0, i), tableAt(0x560, i),
            mload(add(0x620, mul(j, 32))))
    }
    for { let i := 0 } lt(i, 80) { i := add(i, 1) } {
      let j := div(i, 16)
      round(0x160, sub(4, j), tableAt(0x500, i), tableAt(0x5c0, i),
            mload(add(0x6c0, mul(j, 32))))
    }
    let t := and(add(add(mload(0x220), mload(0x100)), mload(0x1c0)), 0xffffffff)
    hSet(1, and(add(add(mload(0x240), mload(0x120)), mload(0x1e0)), 0xffffffff))
    hSet(2, and(add(add(mload(0x260), mload(0x140)), mload(0x160)), 0xffffffff))
    hSet(3, and(add(add(mload(0x280), mload(0x0c0)), mload(0x180)), 0xffffffff))
    hSet(4, and(add(add(mload(0x200), mload(0x0e0)), mload(0x1a0)), 0xffffffff))
    hSet(0, t)
  }
  function writeLE32(off, w) {
    for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
      mstore8(add(off, i), and(shr(mul(8, i), w), 0xff))
    }
  }
  initTables()
  initH()
  let paddedLen := pad()
  for { let off := 0 } lt(off, paddedLen) { off := add(off, 64) } {
    compress(add(0x800, off))
  }
  mstore(0, 0)
  for { let i := 0 } lt(i, 5) { i := add(i, 1) } {
    writeLE32(add(12, mul(i, 4)), hAt(i))
  }
  return(0, 32)
}

def verifiedFunctions : FunEnv localDialect := [hoist localDialect verifiedProgram]

end Challenge.Ripemd160.Reference.Proofs.Yul
