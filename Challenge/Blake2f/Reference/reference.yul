// SPDX-License-Identifier: Apache-2.0
// A proof-friendly implementation of the EIP-152 BLAKE2b compression function.
//
// Memory layout (one 64-bit algorithm word per 32-byte EVM word):
//   0x000..0x0e0  h[0..7]
//   0x100..0x2e0  m[0..15]
//   0x300..0x4e0  v[0..15]
//   0x500..0x53f  64-byte little-endian result
{
    function loadLE64(off) -> word {
        let input := calldataload(off)
        for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
            word := or(word, shl(mul(8, i), byte(i, input)))
        }
    }

    function storeLE64(off, word) {
        for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
            mstore8(add(off, i), and(shr(mul(8, i), word), 0xff))
        }
    }

    function rotr64(x, n) -> z {
        z := and(or(shr(n, x), shl(sub(64, n), x)), 0xffffffffffffffff)
    }

    // One BLAKE2b G quarter-round. Arguments a..d are memory addresses of
    // words in v; the final arguments select two words from the sigma row.
    function mixG(a, b, c, d, round, xColumn, yColumn) {
        let row := mload(add(0x600, mul(32, mod(round, 10))))
        let x := mload(add(0x100, mul(32, byte(add(16, xColumn), row))))
        let y := mload(add(0x100, mul(32, byte(add(16, yColumn), row))))

        let va := and(add(add(mload(a), mload(b)), x), 0xffffffffffffffff)
        mstore(a, va)
        let vd := rotr64(xor(mload(d), va), 32)
        mstore(d, vd)
        let vc := and(add(mload(c), vd), 0xffffffffffffffff)
        mstore(c, vc)
        let vb := rotr64(xor(mload(b), vc), 24)
        mstore(b, vb)

        va := and(add(add(va, vb), y), 0xffffffffffffffff)
        mstore(a, va)
        vd := rotr64(xor(vd, va), 16)
        mstore(d, vd)
        vc := and(add(vc, vd), 0xffffffffffffffff)
        mstore(c, vc)
        vb := rotr64(xor(vb, vc), 63)
        mstore(b, vb)
    }

    if iszero(eq(calldatasize(), 213)) { invalid() }
    let finalFlag := byte(0, calldataload(212))
    if gt(finalFlag, 1) { invalid() }

    let rounds := shr(224, calldataload(0))

    // Decode h and m from their little-endian byte representation.
    for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
        mstore(mul(32, i), loadLE64(add(4, mul(8, i))))
    }
    for { let i := 0 } lt(i, 16) { i := add(i, 1) } {
        mstore(add(0x100, mul(32, i)), loadLE64(add(68, mul(8, i))))
    }

    // v := h || IV.
    for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
        mstore(add(0x300, mul(32, i)), mload(mul(32, i)))
    }
    mstore(0x400, 0x6a09e667f3bcc908)
    mstore(0x420, 0xbb67ae8584caa73b)
    mstore(0x440, 0x3c6ef372fe94f82b)
    mstore(0x460, 0xa54ff53a5f1d36f1)
    mstore(0x480, 0x510e527fade682d1)
    mstore(0x4a0, 0x9b05688c2b3e6c1f)
    mstore(0x4c0, 0x1f83d9abfb41bd6b)
    mstore(0x4e0, 0x5be0cd19137e2179)

    mstore(0x600, 0x000102030405060708090a0b0c0d0e0f)
    mstore(0x620, 0x0e0a0408090f0d06010c00020b070503)
    mstore(0x640, 0x0b080c0005020f0d0a0e030607010904)
    mstore(0x660, 0x070903010d0c0b0e0206050a04000f08)
    mstore(0x680, 0x0900050702040a0f0e010b0c0608030d)
    mstore(0x6a0, 0x020c060a000b0803040d07050f0e0109)
    mstore(0x6c0, 0x0c05010f0e0d040a000706030902080b)
    mstore(0x6e0, 0x0d0b070e0c01030905000f040806020a)
    mstore(0x700, 0x060f0e090b0300080c020d0701040a05)
    mstore(0x720, 0x0a020804070601050f0b090e030c0d00)

    mstore(0x480, xor(mload(0x480), loadLE64(196)))
    mstore(0x4a0, xor(mload(0x4a0), loadLE64(204)))
    if finalFlag {
        mstore(0x4c0, xor(mload(0x4c0), 0xffffffffffffffff))
    }

    for { let round := 0 } lt(round, rounds) { round := add(round, 1) } {
        mixG(0x300, 0x380, 0x400, 0x480, round, 0, 1)
        mixG(0x320, 0x3a0, 0x420, 0x4a0, round, 2, 3)
        mixG(0x340, 0x3c0, 0x440, 0x4c0, round, 4, 5)
        mixG(0x360, 0x3e0, 0x460, 0x4e0, round, 6, 7)
        mixG(0x300, 0x3a0, 0x440, 0x4e0, round, 8, 9)
        mixG(0x320, 0x3c0, 0x460, 0x480, round, 10, 11)
        mixG(0x340, 0x3e0, 0x400, 0x4a0, round, 12, 13)
        mixG(0x360, 0x380, 0x420, 0x4c0, round, 14, 15)
    }

    for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
        let word := xor(xor(mload(mul(32, i)), mload(add(0x300, mul(32, i)))),
            mload(add(0x400, mul(32, i))))
        storeLE64(add(0x500, mul(8, i)), word)
    }
    return(0x500, 64)
}
