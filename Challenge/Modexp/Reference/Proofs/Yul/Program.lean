import Challenge.Modexp.ProofSupport.Yul
import Challenge.Modexp.Reference.Source
import YulSemantics.Syntax

set_option warningAsError true

/-!
# Auditable AST for the verified MODEXP Yul source

This is the proof-side representation of `Reference/reference.yul`. Keeping it
as Yul concrete syntax makes the source proof readable and avoids unfolding
the runtime parser throughout the semantic development.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul

open YulSemantics
open YulSemantics.EVM
open Challenge.YulProof.ClosedEvm

def verifiedProgram : Block Op := yul% {
  function calldataByte(off) -> b {
    b := byte(0, calldataload(off))
  }

  function clearLimbs(ptr, n) {
    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
      mstore(add(ptr, mul(i, 32)), 0)
    }
  }

  function copyLimbs(dst, src, n) {
    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
      mstore(add(dst, mul(i, 32)), mload(add(src, mul(i, 32))))
    }
  }

  function addMaskedMod(dst, src, take, modulus, n) {
    let mask := sub(0, take)
    let carry := 0
    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
      let off := mul(i, 32)
      let x := mload(add(dst, off))
      let y := and(mload(add(src, off)), mask)
      let s := add(x, y)
      let carry1 := lt(s, x)
      let z := add(s, carry)
      let carry2 := lt(z, s)
      mstore(add(dst, off), z)
      carry := or(carry1, carry2)
    }

    let borrow := 0
    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
      let off := mul(i, 32)
      let x := mload(add(dst, off))
      let y := mload(add(modulus, off))
      let d := sub(x, y)
      let borrow1 := lt(x, y)
      let z := sub(d, borrow)
      let borrow2 := lt(d, borrow)
      mstore(add(0x1400, off), z)
      borrow := or(borrow1, borrow2)
    }

    let useSub := or(carry, iszero(borrow))
    let selectMask := sub(0, useSub)
    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
      let off := mul(i, 32)
      let sum := mload(add(dst, off))
      let reduced := mload(add(0x1400, off))
      mstore(add(dst, off),
        or(and(reduced, selectMask), and(sum, not(selectMask))))
    }
  }

  function mulModBig(a, b, out, modulus, n) {
    clearLimbs(out, n)
    copyLimbs(0x1000, a, n)
    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
      let w := mload(add(b, mul(i, 32)))
      for { let j := 0 } lt(j, 256) { j := add(j, 1) } {
        let bit := and(shr(j, w), 1)
        addMaskedMod(out, 0x1000, bit, modulus, n)
        addMaskedMod(0x1000, 0x1000, 1, modulus, n)
      }
    }
  }

  function loadBigEndian(off, len, dst) {
    for { let i := 0 } lt(i, len) { i := add(i, 1) } {
      let reverse := sub(sub(len, 1), i)
      let limb := div(reverse, 32)
      let shift := mul(mod(reverse, 32), 8)
      let dstAt := add(dst, mul(limb, 32))
      mstore(dstAt, or(mload(dstAt), shl(shift, calldataByte(add(off, i)))))
    }
  }

  function modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff) {
    let modulus := shr(mul(sub(32, modulusSize), 8), calldataload(modOff))
    if iszero(modulus) { return(0x1800, modulusSize) }

    let base := 0
    for { let i := 0 } lt(i, bsize) { i := add(i, 1) } {
      base := addmod(mulmod(base, 256, modulus),
        calldataByte(add(baseOff, i)), modulus)
    }

    let acc := mod(1, modulus)
    for { let i := 0 } lt(i, esize) { i := add(i, 1) } {
      let w := calldataByte(add(expOff, i))
      for { let j := 0 } lt(j, 8) { j := add(j, 1) } {
        let bit := and(shr(sub(7, j), w), 1)
        let square := mulmod(acc, acc, modulus)
        let product := mulmod(square, base, modulus)
        let mask := sub(0, bit)
        acc := xor(square, and(xor(square, product), mask))
      }
    }

    mstore(0x1800, shl(mul(sub(32, modulusSize), 8), acc))
    return(0x1800, modulusSize)
  }

  function modexpBig(bsize, esize, modulusSize, baseOff, expOff, modOff) {
    let n := div(add(modulusSize, 31), 32)
    clearLimbs(0x0000, n)
    clearLimbs(0x0400, n)
    clearLimbs(0x0800, n)
    clearLimbs(0x1800, n)
    loadBigEndian(modOff, modulusSize, 0x0000)

    let modulusOr := 0
    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
      modulusOr := or(modulusOr, mload(mul(i, 32)))
    }
    if iszero(modulusOr) { return(0x1800, modulusSize) }

    clearLimbs(0x0c00, n)
    mstore(0x0c00, 1)
    for { let i := 0 } lt(i, bsize) { i := add(i, 1) } {
      let w := calldataByte(add(baseOff, i))
      for { let j := 0 } lt(j, 8) { j := add(j, 1) } {
        addMaskedMod(0x0400, 0x0400, 1, 0x0000, n)
        addMaskedMod(0x0400, 0x0c00,
          and(shr(sub(7, j), w), 1), 0x0000, n)
      }
    }

    addMaskedMod(0x0800, 0x0c00, 1, 0x0000, n)

    for { let i := 0 } lt(i, esize) { i := add(i, 1) } {
      let w := calldataByte(add(expOff, i))
      for { let j := 0 } lt(j, 8) { j := add(j, 1) } {
        let bit := and(shr(sub(7, j), w), 1)

        mulModBig(0x0800, 0x0800, 0x0c00, 0x0000, n)
        copyLimbs(0x0800, 0x0c00, n)
        mulModBig(0x0800, 0x0400, 0x0c00, 0x0000, n)

        let mask := sub(0, bit)
        for { let k := 0 } lt(k, n) { k := add(k, 1) } {
          let off := mul(k, 32)
          let square := mload(add(0x0800, off))
          let product := mload(add(0x0c00, off))
          mstore(add(0x0800, off),
            xor(square, and(xor(square, product), mask)))
        }
      }
    }

    for { let i := 0 } lt(i, modulusSize) { i := add(i, 1) } {
      let reverse := sub(sub(modulusSize, 1), i)
      let limb := div(reverse, 32)
      let shift := mul(mod(reverse, 32), 8)
      mstore8(add(0x1800, i),
        and(shr(shift, mload(add(0x0800, mul(limb, 32)))), 0xff))
    }
    return(0x1800, modulusSize)
  }

  let bsize := calldataload(0)
  let esize := calldataload(32)
  let modulusSize := calldataload(64)

  if or(or(gt(bsize, 1024), gt(esize, 1024)), gt(modulusSize, 1024)) {
    invalid()
  }
  if iszero(modulusSize) { return(0, 0) }

  let baseOff := 96
  let expOff := add(baseOff, bsize)
  let modOff := add(expOff, esize)
  if iszero(gt(modulusSize, 32)) {
    modexpWord(bsize, esize, modulusSize, baseOff, expOff, modOff)
  }
  modexpBig(bsize, esize, modulusSize, baseOff, expOff, modOff)
}

def verifiedFunctions : FunEnv dialect := [hoist dialect verifiedProgram]

end Challenge.Modexp.Reference.Proofs.Yul
