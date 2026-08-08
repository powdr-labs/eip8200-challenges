"""Minimal EVM interpreter with exact gas accounting for the opcode subset
used by the SHA-256 challenge artifacts.  Validated against the pinned Lean
semantics by reproducing the reference implementation's published gas."""

U256 = (1 << 256) - 1


class Halt(Exception):
    def __init__(self, kind, data=b""):
        self.kind = kind
        self.data = data


VERYLOW = 3
BASE = 2
LOW = 5
MID = 8
HIGH = 10

# name -> (opcode, gas, pops, pushes)
_SIMPLE = {
    "STOP": (0x00, 0, 0, 0),
    "ADD": (0x01, VERYLOW, 2, 1),
    "MUL": (0x02, LOW, 2, 1),
    "SUB": (0x03, VERYLOW, 2, 1),
    "DIV": (0x04, LOW, 2, 1),
    "MOD": (0x06, LOW, 2, 1),
    "ADDMOD": (0x08, MID, 3, 1),
    "MULMOD": (0x09, MID, 3, 1),
    "SIGNEXTEND": (0x0B, LOW, 2, 1),
    "LT": (0x10, VERYLOW, 2, 1),
    "GT": (0x11, VERYLOW, 2, 1),
    "SLT": (0x12, VERYLOW, 2, 1),
    "SGT": (0x13, VERYLOW, 2, 1),
    "EQ": (0x14, VERYLOW, 2, 1),
    "ISZERO": (0x15, VERYLOW, 1, 1),
    "AND": (0x16, VERYLOW, 2, 1),
    "OR": (0x17, VERYLOW, 2, 1),
    "XOR": (0x18, VERYLOW, 2, 1),
    "NOT": (0x19, VERYLOW, 1, 1),
    "BYTE": (0x1A, VERYLOW, 2, 1),
    "SHL": (0x1B, VERYLOW, 2, 1),
    "SHR": (0x1C, VERYLOW, 2, 1),
    "SAR": (0x1D, VERYLOW, 2, 1),
    "POP": (0x50, BASE, 1, 0),
    "MLOAD": (0x51, VERYLOW, 1, 1),
    "MSTORE": (0x52, VERYLOW, 2, 0),
    "MSTORE8": (0x53, VERYLOW, 2, 0),
    "JUMP": (0x56, MID, 1, 0),
    "JUMPI": (0x57, HIGH, 2, 0),
    "PC": (0x58, BASE, 0, 1),
    "MSIZE": (0x59, BASE, 0, 1),
    "GAS": (0x5A, BASE, 0, 1),
    "JUMPDEST": (0x5B, 1, 0, 0),
    "CALLDATASIZE": (0x36, BASE, 0, 1),
    "CALLDATALOAD": (0x35, VERYLOW, 1, 1),
    "CALLVALUE": (0x34, BASE, 0, 1),
    "CALLER": (0x33, BASE, 0, 1),
    "ADDRESS": (0x30, BASE, 0, 1),
    "RETURN": (0xF3, 0, 2, 0),
    "REVERT": (0xFD, 0, 2, 0),
    "INVALID": (0xFE, 0, 0, 0),
}

OPCODE_TO_NAME = {v[0]: k for k, v in _SIMPLE.items()}
for _n in range(1, 33):
    OPCODE_TO_NAME[0x5F + _n] = f"PUSH{_n}"
OPCODE_TO_NAME[0x5F] = "PUSH0"
for _n in range(1, 17):
    OPCODE_TO_NAME[0x7F + _n] = f"DUP{_n}"
    OPCODE_TO_NAME[0x8F + _n] = f"SWAP{_n}"
OPCODE_TO_NAME[0x37] = "CALLDATACOPY"
OPCODE_TO_NAME[0x39] = "CODECOPY"
OPCODE_TO_NAME[0x38] = "CODESIZE"
OPCODE_TO_NAME[0x5E] = "MCOPY"


def mem_cost(words):
    return 3 * words + (words * words) // 512


class EVM:
    def __init__(self, code, calldata, gas=3_000_000_000, trace=False):
        self.code = code
        self.calldata = calldata
        self.gas = gas
        self.start_gas = gas
        self.stack = []
        self.mem = bytearray()
        self.words = 0
        self.pc = 0
        self.trace = trace
        self.steps = 0
        self.jumpdests = self._scan()
        self.op_hist = {}
        self.pc_gas = {}

    def _scan(self):
        dests = set()
        i = 0
        while i < len(self.code):
            op = self.code[i]
            if op == 0x5B:
                dests.add(i)
            if 0x60 <= op <= 0x7F:
                i += op - 0x5F
            i += 1
        return dests

    def _charge(self, amount):
        self.gas -= amount
        if self.gas < 0:
            raise Halt("outofgas")

    def _expand(self, offset, size):
        if size == 0:
            return
        need = (offset + size + 31) // 32
        if need > self.words:
            self._charge(mem_cost(need) - mem_cost(self.words))
            self.words = need
            if len(self.mem) < need * 32:
                self.mem.extend(b"\x00" * (need * 32 - len(self.mem)))

    def push(self, v):
        self.stack.append(v & U256)

    def pop(self):
        return self.stack.pop()

    def run(self, max_steps=200_000_000):
        try:
            while self.steps < max_steps:
                pc0, g0 = self.pc, self.gas
                self.step()
                if self.trace:
                    self.pc_gas[pc0] = self.pc_gas.get(pc0, 0) + (g0 - self.gas)
                self.steps += 1
        except Halt as h:
            return h
        raise RuntimeError("step limit")

    def step(self):
        if self.pc >= len(self.code):
            raise Halt("stop")
        op = self.code[self.pc]
        _pc0, _g0 = self.pc, self.gas
        name = OPCODE_TO_NAME.get(op)
        if name is None:
            raise Halt("invalid-opcode-%02x" % op)
        if self.trace:
            self.op_hist[name] = self.op_hist.get(name, 0) + 1
        self.pc += 1

        if name.startswith("PUSH"):
            n = int(name[4:])
            self._charge(BASE if n == 0 else VERYLOW)
            val = int.from_bytes(self.code[self.pc:self.pc + n].ljust(n, b"\x00"), "big")
            self.pc += n
            self.push(val)
            return
        if name.startswith("DUP"):
            n = int(name[3:])
            self._charge(VERYLOW)
            self.push(self.stack[-n])
            return
        if name.startswith("SWAP"):
            n = int(name[4:])
            self._charge(VERYLOW)
            self.stack[-1], self.stack[-1 - n] = self.stack[-1 - n], self.stack[-1]
            return

        if name in ("CALLDATACOPY", "CODECOPY", "MCOPY"):
            if name == "MCOPY":
                dst, src, length = self.pop(), self.pop(), self.pop()
            else:
                dst, src, length = self.pop(), self.pop(), self.pop()
            self._charge(VERYLOW + 3 * ((length + 31) // 32))
            if name == "MCOPY":
                self._expand(max(dst, src), length)
                chunk = bytes(self.mem[src:src + length])
            else:
                self._expand(dst, length)
                source = self.calldata if name == "CALLDATACOPY" else self.code
                chunk = source[src:src + length].ljust(length, b"\x00")
            if length:
                self.mem[dst:dst + length] = chunk
            return
        if name == "CODESIZE":
            self._charge(BASE)
            self.push(len(self.code))
            return

        opcode, gas, pops, pushes = _SIMPLE[name]
        self._charge(gas)
        args = [self.pop() for _ in range(pops)]

        if name == "ADD":
            self.push(args[0] + args[1])
        elif name == "MUL":
            self.push(args[0] * args[1])
        elif name == "SUB":
            self.push(args[0] - args[1])
        elif name == "DIV":
            self.push(0 if args[1] == 0 else args[0] // args[1])
        elif name == "MOD":
            self.push(0 if args[1] == 0 else args[0] % args[1])
        elif name == "ADDMOD":
            self.push(0 if args[2] == 0 else (args[0] + args[1]) % args[2])
        elif name == "MULMOD":
            self.push(0 if args[2] == 0 else (args[0] * args[1]) % args[2])
        elif name == "LT":
            self.push(1 if args[0] < args[1] else 0)
        elif name == "GT":
            self.push(1 if args[0] > args[1] else 0)
        elif name == "EQ":
            self.push(1 if args[0] == args[1] else 0)
        elif name == "ISZERO":
            self.push(1 if args[0] == 0 else 0)
        elif name == "AND":
            self.push(args[0] & args[1])
        elif name == "OR":
            self.push(args[0] | args[1])
        elif name == "XOR":
            self.push(args[0] ^ args[1])
        elif name == "NOT":
            self.push(~args[0])
        elif name == "BYTE":
            i = args[0]
            self.push(0 if i >= 32 else (args[1] >> (8 * (31 - i))) & 0xFF)
        elif name == "SHL":
            self.push(0 if args[0] >= 256 else args[1] << args[0])
        elif name == "SHR":
            self.push(0 if args[0] >= 256 else args[1] >> args[0])
        elif name == "SIGNEXTEND":
            b, x = args
            if b >= 31:
                self.push(x)
            else:
                bit = 8 * b + 7
                mask = (1 << (bit + 1)) - 1
                self.push(x | (~mask) if (x >> bit) & 1 else x & mask)
        elif name == "POP":
            pass
        elif name == "MLOAD":
            self._expand(args[0], 32)
            self.push(int.from_bytes(self.mem[args[0]:args[0] + 32], "big"))
        elif name == "MSTORE":
            self._expand(args[0], 32)
            self.mem[args[0]:args[0] + 32] = args[1].to_bytes(32, "big")
        elif name == "MSTORE8":
            self._expand(args[0], 1)
            self.mem[args[0]] = args[1] & 0xFF
        elif name == "JUMP":
            if args[0] not in self.jumpdests:
                raise Halt("bad-jump")
            self.pc = args[0]
        elif name == "JUMPI":
            if args[1] != 0:
                if args[0] not in self.jumpdests:
                    raise Halt("bad-jump")
                self.pc = args[0]
        elif name == "JUMPDEST":
            pass
        elif name == "PC":
            self.push(self.pc - 1)
        elif name == "MSIZE":
            self.push(self.words * 32)
        elif name == "GAS":
            self.push(self.gas)
        elif name == "CALLDATASIZE":
            self.push(len(self.calldata))
        elif name == "CALLDATALOAD":
            off = args[0]
            self.push(int.from_bytes(self.calldata[off:off + 32].ljust(32, b"\x00"), "big")
                      if off < len(self.calldata) else 0)
        elif name in ("CALLVALUE", "CALLER", "ADDRESS"):
            self.push(0)
        elif name == "STOP":
            raise Halt("stop")
        elif name == "RETURN":
            self._expand(args[0], args[1])
            raise Halt("return", bytes(self.mem[args[0]:args[0] + args[1]]))
        elif name == "REVERT":
            self._expand(args[0], args[1])
            raise Halt("revert", bytes(self.mem[args[0]:args[0] + args[1]]))
        elif name == "INVALID":
            raise Halt("invalid")
        else:
            raise RuntimeError("unhandled " + name)


def execute(code, calldata, gas=3_000_000_000, trace=False):
    vm = EVM(code, calldata, gas, trace)
    h = vm.run()
    return h, vm.start_gas - vm.gas, vm
