"""Optimized SHA-256 EVM bytecode, v3 (W stored pre-doubled).

Design notes
============

**Rotation by doubling.**  For 32-bit x let X = x * (2^32 + 1), i.e. two
copies of x side by side in 64 bits.  Then for 0 <= n < 32 the low 32 bits of
X >> n are exactly rotr(x, n), and -- the extra observation over v1 -- for
32 <= n < 64 the value X >> n is exactly x >> (n - 32), with nothing above.
So *every* term of Sigma0/Sigma1/sigma0/sigma1, rotations and plain right
shifts alike, is a right shift of the single value X.  Each gadget is one MUL
plus three chained SHRs plus two XORs.

    Sigma0(a) = X>>2  ^ X>>13 ^ X>>22          (mod 2^32)
    Sigma1(e) = X>>6  ^ X>>11 ^ X>>25
    sigma0(x) = X>>7  ^ X>>18 ^ X>>35
    sigma1(x) = X>>17 ^ X>>19 ^ X>>42

**Lazy masking.**  Bits at position >= 32 are garbage that the next
`& 0xffffffff` discards, and ADD carries only upward, so no intermediate is
ever masked.  The only masks are on the two values that must be exactly 32
bits because they feed a doubling next round: the new a and the new e.

**Eight fixed stack slots.**  a..h live at eight fixed stack depths.  A round
overwrites exactly the two variables that die in it (h and d) and rotates the
*roles*, so there is no shuffling and the assignment is the identity again
after eight rounds.

**Constant memory.**  Blocks are read one at a time out of calldata with
CALLDATACOPY, which zero-extends past the end for free, so the padding needs
no message buffer: only a 96-byte staging area.  Memory use is 2432 bytes for
every input, which keeps the quadratic memory term out of the gas formula.

**Full unrolling.**  The 64 rounds and 48 schedule steps are unrolled inside a
single block subroutine, so every W offset and round constant is an immediate.
"""

from asm import Asm

MASK32 = 0xFFFFFFFF
MASK64 = 0xFFFFFFFFFFFFFFFF
DBL = 0x100000001          # 2^32 + 1

K = [
    0x428A2F98, 0x71374491, 0xB5C0FBCF, 0xE9B5DBA5, 0x3956C25B, 0x59F111F1,
    0x923F82A4, 0xAB1C5ED5, 0xD807AA98, 0x12835B01, 0x243185BE, 0x550C7DC3,
    0x72BE5D74, 0x80DEB1FE, 0x9BDC06A7, 0xC19BF174, 0xE49B69C1, 0xEFBE4786,
    0x0FC19DC6, 0x240CA1CC, 0x2DE92C6F, 0x4A7484AA, 0x5CB0A9DC, 0x76F988DA,
    0x983E5152, 0xA831C66D, 0xB00327C8, 0xBF597FC7, 0xC6E00BF3, 0xD5A79147,
    0x06CA6351, 0x14292967, 0x27B70A85, 0x2E1B2138, 0x4D2C6DFC, 0x53380D13,
    0x650A7354, 0x766A0ABB, 0x81C2C92E, 0x92722C85, 0xA2BFE8A1, 0xA81A664B,
    0xC24B8B70, 0xC76C51A3, 0xD192E819, 0xD6990624, 0xF40E3585, 0x106AA070,
    0x19A4C116, 0x1E376C08, 0x2748774C, 0x34B0BCB5, 0x391C0CB3, 0x4ED8AA4A,
    0x5B9CCA4F, 0x682E6FF3, 0x748F82EE, 0x78A5636F, 0x84C87814, 0x8CC70208,
    0x90BEFFFA, 0xA4506CEB, 0xBEF9A3F7, 0xC67178F2,
]

H0 = [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
      0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

# ---- memory map (constant, 2432 bytes) --------------------------------
OUT = 0x000          # digest word
HB = 0x020           # H[0..7], one 32-byte slot each      0x020 .. 0x11f
SCR = 0x120          # 64-byte block staging + 32 bytes of slack
WB = 0x180           # W[0..63], one 32-byte slot each     0x180 .. 0x97f
MEM_END = 0x980


def woff(t):
    return WB + 32 * t


class Gen:
    def __init__(self):
        self.a = Asm()
        self.slots = ["a", "b", "c", "d", "e", "f", "g", "h"]
        self.td = 0
        self.maxdepth = 0

    # --- stack bookkeeping ------------------------------------------
    def _note(self, depth):
        self.maxdepth = max(self.maxdepth, depth)

    def dup_state(self, role):
        n = self.td + self.slots.index(role) + 1
        self._note(n)
        self.a.dup(n)
        self.td += 1

    def store_state(self, role):
        n = self.td - 1 + self.slots.index(role) + 1
        self._note(n)
        self.a.swap(n)
        self.a.op("POP")
        self.td -= 1

    def push(self, v):
        self.a.push(v)
        self.td += 1

    def op(self, name, delta=0):
        self.a.op(name)
        self.td += delta

    def dup1(self):
        self.a.dup(1)
        self.td += 1

    # --- the one XOR-of-three-shifts gadget --------------------------
    def sigma_from_doubled(self, s0, s1, s2):
        """[X] -> [X>>s0 ^ X>>s1 ^ X>>s2], via chained shifts."""
        self.push(s0); self.op("SHR", -1)
        self.dup1(); self.push(s1 - s0); self.op("SHR", -1)
        self.dup1(); self.push(s2 - s1); self.op("SHR", -1)
        self.op("XOR", -1)
        self.op("XOR", -1)

    def big_sigma(self, role, shifts):
        self.dup_state(role)
        self.push(DBL); self.op("MUL", -1)
        self.sigma_from_doubled(*shifts)

    def small_sigma(self, offset, shifts):
        self.push(offset); self.op("MLOAD")
        self.sigma_from_doubled(*shifts)

    # --- one compression round ---------------------------------------
    def round(self, t):
        self.big_sigma("e", (6, 11, 25))                 # Sigma1(e)
        # ch = g ^ (e & (f ^ g))
        self.dup_state("f"); self.dup_state("g"); self.op("XOR", -1)
        self.dup_state("e"); self.op("AND", -1)
        self.dup_state("g"); self.op("XOR", -1)
        # t1 = Sigma1 + ch + h + K[t] + W[t]
        self.op("ADD", -1)
        self.dup_state("h"); self.op("ADD", -1)
        self.push(K[t]); self.op("ADD", -1)
        self.push(woff(t)); self.op("MLOAD"); self.op("ADD", -1)
        # new e = (d + t1) & MASK32, into the slot that held d
        self.dup1()
        self.dup_state("d"); self.op("ADD", -1)
        self.push(MASK32); self.op("AND", -1)
        self.store_state("d")
        self.big_sigma("a", (2, 13, 22))                 # Sigma0(a)
        # maj = (a & b) ^ (c & (a ^ b))
        self.dup_state("a"); self.dup_state("b"); self.op("AND", -1)
        self.dup_state("a"); self.dup_state("b"); self.op("XOR", -1)
        self.dup_state("c"); self.op("AND", -1)
        self.op("XOR", -1)
        # new a = (t1 + Sigma0 + maj) & MASK32, into the slot that held h
        self.op("ADD", -1)
        self.op("ADD", -1)
        self.push(MASK32); self.op("AND", -1)
        self.store_state("h")
        assert self.td == 0
        cyc = "abcdefgh"
        self.slots = [cyc[(cyc.index(r) + 1) % 8] for r in self.slots]

    def schedule_step(self, t):
        self.small_sigma(woff(t - 2), (17, 19, 42))      # sigma1(W[t-2])
        self.small_sigma(woff(t - 15), (7, 18, 35))      # sigma0(W[t-15])
        self.op("ADD", -1)
        self.push(woff(t - 7)); self.op("MLOAD"); self.op("ADD", -1)
        self.push(woff(t - 16)); self.op("MLOAD"); self.op("ADD", -1)
        self.push(MASK32); self.op("AND", -1)
        self.push(DBL); self.op("MUL", -1)
        self.push(woff(t)); self.op("MSTORE", -2)

    # --- the block subroutine ------------------------------------------
    def body(self):
        a = self.a
        a.label("body")                                  # [ret, ...]
        a.mark("W[0..15] from block")
        for j in range(16):
            a.push(SCR + 4 * j); a.op("MLOAD")
            a.push(224); a.op("SHR")
            a.push(DBL); a.op("MUL")
            a.push(woff(j)); a.op("MSTORE")
        a.mark("message schedule")
        for t in range(16, 64):
            self.schedule_step(t)
        a.mark("load state")
        for i in range(7, -1, -1):                       # push h..a, a on top
            a.push(HB + 32 * i); a.op("MLOAD")
        a.mark("64 rounds")
        for t in range(64):
            self.round(t)
        assert self.slots == list("abcdefgh")
        a.mark("H update + return")
        for i in range(8):                               # H[i] += state, top-down
            a.push(HB + 32 * i); a.op("MLOAD"); a.op("ADD")
            a.push(MASK32); a.op("AND")
            a.push(HB + 32 * i); a.op("MSTORE")
        a.op("JUMP")                                     # return

    # --- driver -------------------------------------------------------
    def program(self):
        a = self.a
        a.push_label("main"); a.op("JUMP")
        self.body()

        a.mark("driver")
        a.label("main")
        a.calldatasize()                                 # [n]
        for i, h in enumerate(H0):
            a.push(h); a.push(HB + 32 * i); a.op("MSTORE")
        a.dup(1); a.push(63); a.op("AND")                # [rem, n]
        a.dup(2); a.push(6); a.op("SHR"); a.push(6); a.op("SHL")
        #                                                  [end, rem, n]
        a.push(0)                                        # [off, end, rem, n]
        a.dup(2); a.op("ISZERO"); a.push_label("tail"); a.op("JUMPI")

        a.label("loop")                                  # full calldata blocks
        a.push(64); a.dup(2); a.push(SCR); a.op("CALLDATACOPY")
        a.push_label("r0"); a.push_label("body"); a.op("JUMP")
        a.label("r0")
        a.push(64); a.op("ADD")
        a.dup(2); a.dup(2); a.op("LT")
        a.push_label("loop"); a.op("JUMPI")

        a.label("tail")                                  # [off, end, rem, n]
        a.push(64); a.dup(2); a.push(SCR); a.op("CALLDATACOPY")
        a.push(0x80); a.dup(4); a.push(SCR); a.op("ADD"); a.op("MSTORE8")
        a.push(56); a.dup(4); a.op("LT")                 # rem < 56 ?
        a.push_label("length"); a.op("JUMPI")
        # rem >= 56: this block holds no length; run it, then an all-zero block
        a.push_label("r1"); a.push_label("body"); a.op("JUMP")
        a.label("r1")
        a.push(0); a.push(SCR); a.op("MSTORE")
        a.push(0); a.push(SCR + 32); a.op("MSTORE")

        a.label("length")                                # bit length at SCR+56
        a.dup(4); a.push(3); a.op("SHL")
        a.push(MASK64); a.op("AND")
        a.push(192); a.op("SHL")
        a.push(SCR + 56); a.op("MSTORE")
        a.push_label("r2"); a.push_label("body"); a.op("JUMP")
        a.label("r2")

        a.push(HB); a.op("MLOAD"); a.push(224); a.op("SHL")
        for i in range(1, 7):
            a.push(HB + 32 * i); a.op("MLOAD")
            a.push(224 - 32 * i); a.op("SHL"); a.op("OR")
        a.push(HB + 32 * 7); a.op("MLOAD"); a.op("OR")
        a.push(OUT); a.op("MSTORE")
        a.push(32); a.push(OUT); a.op("RETURN")
        return a.assemble()


def build():
    g = Gen()
    code = g.program()
    assert g.maxdepth <= 16, g.maxdepth
    return code, g.a.marks


def generate():
    g = Gen()
    code = g.program()
    assert g.maxdepth <= 16, g.maxdepth
    return code


if __name__ == "__main__":
    code = generate()
    print(len(code), "bytes")
