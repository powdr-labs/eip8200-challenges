#!/usr/bin/env python3
"""Disassemble a frozen challenge artifact into (index, pc, instr) triples.

The Lean side represents instructions as `Instr.push width value` (width 0..32,
where width 0 is PUSH0) and `Instr.op <Operation>`; `op 0xNN` in the generated
lists is the opcode-driven form.  This mirrors that view so generated Lean and
this table cannot drift.
"""
import json
import sys

OPCODES = {
    0x00: "STOP", 0x01: "ADD", 0x02: "MUL", 0x03: "SUB", 0x04: "DIV",
    0x05: "SDIV", 0x06: "MOD", 0x07: "SMOD", 0x08: "ADDMOD", 0x09: "MULMOD",
    0x0a: "EXP", 0x0b: "SIGNEXTEND",
    0x10: "LT", 0x11: "GT", 0x12: "SLT", 0x13: "SGT", 0x14: "EQ",
    0x15: "ISZERO", 0x16: "AND", 0x17: "OR", 0x18: "XOR", 0x19: "NOT",
    0x1a: "BYTE", 0x1b: "SHL", 0x1c: "SHR", 0x1d: "SAR",
    0x20: "KECCAK256",
    0x30: "ADDRESS", 0x31: "BALANCE", 0x32: "ORIGIN", 0x33: "CALLER",
    0x34: "CALLVALUE", 0x35: "CALLDATALOAD", 0x36: "CALLDATASIZE",
    0x37: "CALLDATACOPY", 0x38: "CODESIZE", 0x39: "CODECOPY",
    0x3a: "GASPRICE", 0x3b: "EXTCODESIZE", 0x3c: "EXTCODECOPY",
    0x3d: "RETURNDATASIZE", 0x3e: "RETURNDATACOPY", 0x3f: "EXTCODEHASH",
    0x40: "BLOCKHASH", 0x41: "COINBASE", 0x42: "TIMESTAMP", 0x43: "NUMBER",
    0x44: "PREVRANDAO", 0x45: "GASLIMIT", 0x46: "CHAINID",
    0x47: "SELFBALANCE", 0x48: "BASEFEE", 0x49: "BLOBHASH",
    0x4a: "BLOBBASEFEE",
    0x50: "POP", 0x51: "MLOAD", 0x52: "MSTORE", 0x53: "MSTORE8",
    0x54: "SLOAD", 0x55: "SSTORE", 0x56: "JUMP", 0x57: "JUMPI",
    0x58: "PC", 0x59: "MSIZE", 0x5a: "GAS", 0x5b: "JUMPDEST",
    0x5c: "TLOAD", 0x5d: "TSTORE", 0x5e: "MCOPY",
    0xf0: "CREATE", 0xf1: "CALL", 0xf2: "CALLCODE", 0xf3: "RETURN",
    0xf4: "DELEGATECALL", 0xf5: "CREATE2", 0xfa: "STATICCALL",
    0xfd: "REVERT", 0xfe: "INVALID", 0xff: "SELFDESTRUCT",
}


def disassemble(code: bytes):
    """Yield dicts with index, pc, size and a Lean-shaped instruction view."""
    out = []
    pc = 0
    while pc < len(code):
        b = code[pc]
        if b == 0x5f:
            out.append(dict(pc=pc, size=1, kind="push", width=0, value=0))
            pc += 1
        elif 0x60 <= b <= 0x7f:
            width = b - 0x5f
            value = int.from_bytes(code[pc + 1:pc + 1 + width], "big")
            out.append(dict(pc=pc, size=1 + width, kind="push",
                            width=width, value=value))
            pc += 1 + width
        elif 0x80 <= b <= 0x8f:
            out.append(dict(pc=pc, size=1, kind="dup", idx=b - 0x80,
                            name=f"DUP{b - 0x7f}"))
            pc += 1
        elif 0x90 <= b <= 0x9f:
            out.append(dict(pc=pc, size=1, kind="swap", idx=b - 0x90,
                            name=f"SWAP{b - 0x8f}"))
            pc += 1
        elif 0xa0 <= b <= 0xa4:
            out.append(dict(pc=pc, size=1, kind="log", idx=b - 0xa0,
                            name=f"LOG{b - 0xa0}"))
            pc += 1
        else:
            out.append(dict(pc=pc, size=1, kind="op", opcode=b,
                            name=OPCODES.get(b, f"UNKNOWN_{b:02x}")))
            pc += 1
    for i, ins in enumerate(out):
        ins["index"] = i
    return out


def load(path):
    with open(path) as f:
        return bytes.fromhex("".join(f.read().split()))


def render(ins):
    if ins["kind"] == "push":
        return f"PUSH{ins['width']} 0x{ins['value']:x}"
    return ins["name"]


def main():
    path = sys.argv[1]
    code = load(path)
    table = disassemble(code)
    if "--json" in sys.argv:
        print(json.dumps(table))
        return
    print(f"# {path}: {len(code)} bytes, {len(table)} instructions")
    lo = 0
    hi = len(table)
    for a in sys.argv[2:]:
        if a.startswith("--range="):
            lo, hi = (int(x, 0) for x in a.split("=", 1)[1].split(":"))
    for ins in table[lo:hi]:
        print(f"{ins['index']:4d}  pc=0x{ins['pc']:04x} ({ins['pc']:4d})  "
              f"{render(ins)}")


if __name__ == "__main__":
    main()
