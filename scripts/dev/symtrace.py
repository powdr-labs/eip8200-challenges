#!/usr/bin/env python3
"""Symbolically execute a straight-line run of a frozen artifact.

The direct-bytecode proofs are symbolic-execution transcripts: a chain of
`State` definitions whose `pc` and `stack` fields record what the machine holds
after each instruction.  Re-deriving them against a re-scheduled backend means
re-running the block and reading off the new stack shapes, which is what this
does.

Expressions are trees; `lean()` renders them in the vocabulary the proof corpus
uses (`UInt256.ofNat`, `UInt256.shiftLeft`, `+`, `-`, `UInt256.land`, ...) so a
transcript can be pasted into a proof without hand-translation.
"""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from artifact import disassemble, load, render

# ---------------------------------------------------------------- expressions

class E:
    """A symbolic 256-bit value."""

    def __init__(self, kind, *args):
        self.kind = kind
        self.args = args

    def __repr__(self):
        return self.short()

    def short(self):
        k, a = self.kind, self.args
        if k == "lit":
            v = a[0]
            return hex(v) if v > 9 else str(v)
        if k == "sym":
            return a[0]
        if k in ("+", "-", "*"):
            return f"({a[0].short()} {k} {a[1].short()})"
        infix = {"shl": "<<", "shr": ">>", "and": "&", "or": "|", "xor": "^"}
        if k in infix:
            # EVM shifts take the shift amount on top: shl(shift, value)
            return f"({a[1].short()} {infix[k]} {a[0].short()})"
        return f"{k}({', '.join(x.short() for x in a)})"

    def lean(self):
        k, a = self.kind, self.args
        if k == "lit":
            v = a[0]
            return "⟨0⟩" if v == 0 else f"UInt256.ofNat {_natlit(v)}"
        if k == "sym":
            return a[0]
        if k == "+":
            return f"({a[0].lean()} + {a[1].lean()})"
        if k == "-":
            return f"({a[0].lean()} - {a[1].lean()})"
        if k == "*":
            return f"({a[0].lean()} * {a[1].lean()})"
        named = {
            "shl": "UInt256.shiftLeft", "shr": "UInt256.shiftRight",
            "and": "UInt256.land", "or": "UInt256.lor", "xor": "UInt256.xor",
            "not": "UInt256.lnot", "div": "UInt256.div", "mod": "UInt256.mod",
            "lt": "UInt256.lt", "gt": "UInt256.gt", "eq": "UInt256.eq",
            "iszero": "UInt256.isZero", "byte": "UInt256.byteAt",
            "sar": "UInt256.shiftRightArith", "sub": "-",
        }
        if k in ("shl", "shr", "sar"):
            # Lean's helpers take (value, shift); the EVM stack has shift on top
            return f"({named[k]} {a[1].lean()} {a[0].lean()})"
        if k in named:
            return f"({named[k]} {' '.join(x.lean() for x in a)})"
        return f"({k} {' '.join(x.lean() for x in a)})"


def _natlit(v):
    return hex(v) if v > 255 else str(v)


def lit(v):
    return E("lit", v)


def sym(name):
    return E("sym", name)


MASK = (1 << 256) - 1


def fold(kind, *args):
    """Constant-fold when every argument is a literal; the proofs carry folded
    constants (`UInt256.ofNat 0x800`), not unevaluated arithmetic."""
    if all(x.kind == "lit" for x in args):
        v = [x.args[0] for x in args]
        try:
            if kind == "+":
                return lit((v[0] + v[1]) & MASK)
            if kind == "-":
                return lit((v[0] - v[1]) & MASK)
            if kind == "*":
                return lit((v[0] * v[1]) & MASK)
            if kind == "shl":
                return lit((v[1] << v[0]) & MASK) if v[0] < 256 else lit(0)
            if kind == "shr":
                return lit(v[1] >> v[0]) if v[0] < 256 else lit(0)
            if kind == "and":
                return lit(v[0] & v[1])
            if kind == "or":
                return lit(v[0] | v[1])
            if kind == "xor":
                return lit(v[0] ^ v[1])
            if kind == "iszero":
                return lit(1 if v[0] == 0 else 0)
            if kind == "lt":
                return lit(1 if v[0] < v[1] else 0)
            if kind == "gt":
                return lit(1 if v[0] > v[1] else 0)
            if kind == "eq":
                return lit(1 if v[0] == v[1] else 0)
        except (IndexError, ValueError):
            pass
    return E(kind, *args)


# ------------------------------------------------------------------ execution

BINARY = {
    "ADD": "+", "SUB": "-", "MUL": "*", "DIV": "div", "MOD": "mod",
    "SHL": "shl", "SHR": "shr", "SAR": "sar", "AND": "and", "OR": "or",
    "XOR": "xor", "LT": "lt", "GT": "gt", "EQ": "eq", "BYTE": "byte",
    "SIGNEXTEND": "signextend", "SLT": "slt", "SGT": "sgt",
}
UNARY = {"ISZERO": "iszero", "NOT": "not"}
NULLARY = {
    "CALLDATASIZE": "calldatasize", "MSIZE": "msize", "GAS": "gas",
    "ADDRESS": "address", "CALLVALUE": "callvalue", "CALLER": "caller",
}
# (pops, pushes) for the effectful ops the reference programs actually use
EFFECT = {
    "MSTORE": (2, 0), "MSTORE8": (2, 0), "CALLDATACOPY": (3, 0),
    "MCOPY": (3, 0), "RETURN": (2, 0), "REVERT": (2, 0), "POP": (1, 0),
    "JUMP": (1, 0), "JUMPI": (2, 0), "JUMPDEST": (0, 0), "STOP": (0, 0),
    "MLOAD": (1, 1), "CALLDATALOAD": (1, 1), "KECCAK256": (2, 1),
}


class Halt(Exception):
    pass


def step(ins, stack, notes):
    """Apply one instruction to the symbolic stack; return the new stack."""
    k = ins["kind"]
    if k == "push":
        return [lit(ins["value"])] + stack
    if k == "dup":
        n = ins["idx"]
        return [stack[n]] + stack
    if k == "swap":
        n = ins["idx"] + 1
        s = list(stack)
        s[0], s[n] = s[n], s[0]
        return s
    name = ins["name"]
    if name in BINARY:
        a, b = stack[0], stack[1]
        return [fold(BINARY[name], a, b)] + stack[2:]
    if name in UNARY:
        return [fold(UNARY[name], stack[0])] + stack[1:]
    if name in NULLARY:
        return [sym(NULLARY[name])] + stack
    if name == "MSTORE":
        notes.append(f"mem[{stack[0].short()}] := {stack[1].short()} (32 bytes)")
        return stack[2:]
    if name == "MSTORE8":
        notes.append(f"mem[{stack[0].short()}] := {stack[1].short()} (1 byte)")
        return stack[2:]
    if name == "CALLDATACOPY":
        notes.append(f"mem[{stack[0].short()}..] := calldata[{stack[1].short()}"
                     f" +{stack[2].short()}]")
        return stack[3:]
    if name == "MCOPY":
        notes.append(f"mem[{stack[0].short()}..] := mem[{stack[1].short()}"
                     f" +{stack[2].short()}]")
        return stack[3:]
    if name == "MLOAD":
        return [E("mload", stack[0])] + stack[1:]
    if name == "CALLDATALOAD":
        return [E("calldataload", stack[0])] + stack[1:]
    if name == "POP":
        return stack[1:]
    if name == "JUMPDEST":
        return stack
    if name == "JUMP":
        notes.append(f"JUMP -> {stack[0].short()}")
        raise Halt()
    if name == "JUMPI":
        notes.append(f"JUMPI -> {stack[0].short()} if {stack[1].short()}")
        return stack[2:]
    if name in ("RETURN", "REVERT", "STOP", "INVALID"):
        notes.append(name)
        raise Halt()
    raise NotImplementedError(f"no symbolic rule for {name}")


def trace(table, start, stack, count=None, stop_at_jump=True, lean=False):
    """Print the transcript from `start`, `count` instructions (or to a jump)."""
    i = start
    end = start + count if count else len(table)
    while i < min(end, len(table)):
        ins = table[i]
        notes = []
        try:
            stack = step(ins, stack, notes)
        except Halt:
            print(f"{i:4d}  pc=0x{ins['pc']:04x}  {render(ins):<22} "
                  f"|| {'; '.join(notes)}")
            if stop_at_jump:
                return stack, i
            i += 1
            continue
        shown = ", ".join(x.lean() if lean else x.short() for x in stack)
        note = ("  || " + "; ".join(notes)) if notes else ""
        print(f"{i:4d}  pc=0x{ins['pc']:04x}  {render(ins):<22} "
              f"[{shown}]{note}")
        i += 1
    return stack, i


def main():
    path = sys.argv[1]
    start = int(sys.argv[2], 0)
    count = int(sys.argv[3], 0) if len(sys.argv) > 3 else None
    init = []
    lean = "--lean" in sys.argv
    for a in sys.argv[4:]:
        if a.startswith("--stack="):
            init = [sym(x.strip()) for x in a.split("=", 1)[1].split(",")
                    if x.strip()]
    table = disassemble(load(path))
    trace(table, start, init, count, lean=lean)


if __name__ == "__main__":
    main()
