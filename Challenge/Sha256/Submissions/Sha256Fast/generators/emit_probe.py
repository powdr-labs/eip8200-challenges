"""Shared disassembly and Lean rendering helpers for proof generators.

The original candidate's emitters import this module, but PR 20 accidentally
omitted it.  Keeping the renderer here makes generated instruction and
``Located`` certificates reproducible from the same bytecode generator.
"""

from asm import OPS


_NAMES = {opcode: name for name, opcode in OPS.items()}

_LEAN_OP = {
    "STOP": "Operation.StopArith (Operation.StopArithOps.STOP)",
    "ADD": "Operation.StopArith (Operation.StopArithOps.ADD)",
    "MUL": "Operation.StopArith (Operation.StopArithOps.MUL)",
    "SUB": "Operation.StopArith (Operation.StopArithOps.SUB)",
    "DIV": "Operation.StopArith (Operation.StopArithOps.DIV)",
    "MOD": "Operation.StopArith (Operation.StopArithOps.MOD)",
    "ADDMOD": "Operation.StopArith (Operation.StopArithOps.ADDMOD)",
    "MULMOD": "Operation.StopArith (Operation.StopArithOps.MULMOD)",
    "LT": "Operation.CompBit (Operation.CompareBitwiseOps.LT)",
    "GT": "Operation.CompBit (Operation.CompareBitwiseOps.GT)",
    "EQ": "Operation.CompBit (Operation.CompareBitwiseOps.EQ)",
    "ISZERO": "Operation.CompBit (Operation.CompareBitwiseOps.ISZERO)",
    "AND": "Operation.CompBit (Operation.CompareBitwiseOps.AND)",
    "OR": "Operation.CompBit (Operation.CompareBitwiseOps.OR)",
    "XOR": "Operation.CompBit (Operation.CompareBitwiseOps.XOR)",
    "NOT": "Operation.CompBit (Operation.CompareBitwiseOps.NOT)",
    "BYTE": "Operation.CompBit (Operation.CompareBitwiseOps.BYTE)",
    "SHL": "Operation.CompBit (Operation.CompareBitwiseOps.SHL)",
    "SHR": "Operation.CompBit (Operation.CompareBitwiseOps.SHR)",
    "CALLDATALOAD": "Operation.Env (Operation.EnvOps.CALLDATALOAD)",
    "CALLDATASIZE": "Operation.Env (Operation.EnvOps.CALLDATASIZE)",
    "CALLDATACOPY": "Operation.Env (Operation.EnvOps.CALLDATACOPY)",
    "POP": "Operation.StackMemFlow (Operation.StackMemFlowOps.POP)",
    "MLOAD": "Operation.StackMemFlow (Operation.StackMemFlowOps.MLOAD)",
    "MSTORE": "Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE)",
    "MSTORE8": "Operation.StackMemFlow (Operation.StackMemFlowOps.MSTORE8)",
    "JUMP": "Operation.StackMemFlow (Operation.StackMemFlowOps.JUMP)",
    "JUMPI": "Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPI)",
    "JUMPDEST": "Operation.StackMemFlow (Operation.StackMemFlowOps.JUMPDEST)",
    "MCOPY": "Operation.StackMemFlow (Operation.StackMemFlowOps.MCOPY)",
    "RETURN": "Operation.System (Operation.SystemOps.RETURN)",
    "INVALID": "Operation.System (Operation.SystemOps.INVALID)",
}


def disassemble(code):
    """Return ``(kind, payload, value)`` triples for the supported artifact."""
    result = []
    pc = 0
    while pc < len(code):
        opcode = code[pc]
        if opcode == 0x5F:
            result.append(("push", 0, 0))
            pc += 1
        elif 0x60 <= opcode <= 0x7F:
            width = opcode - 0x5F
            body = code[pc + 1:pc + 1 + width]
            if len(body) != width:
                raise ValueError(f"truncated PUSH at byte {pc}")
            result.append(("push", width, int.from_bytes(body, "big")))
            pc += width + 1
        elif 0x80 <= opcode <= 0x8F:
            result.append(("dup", opcode - 0x80, opcode))
            pc += 1
        elif 0x90 <= opcode <= 0x9F:
            result.append(("swap", opcode - 0x90, opcode))
            pc += 1
        elif opcode in _NAMES:
            result.append(("op", _NAMES[opcode], opcode))
            pc += 1
        else:
            raise ValueError(f"unsupported opcode 0x{opcode:02x} at byte {pc}")
    return result


def lean_instr(instruction):
    kind, payload, value = instruction
    if kind == "push":
        return (f"Instr.push ⟨{payload}, by decide⟩ "
                f"(UInt256.ofNat {value})")
    if kind == "dup":
        return f"Instr.op (Operation.Dup ⟨{payload}, by decide⟩)"
    if kind == "swap":
        return f"Instr.op (Operation.Swap ⟨{payload}, by decide⟩)"
    return f"Instr.op ({_LEAN_OP[payload]})"


def lean_located(index, instruction):
    rendered = lean_instr(instruction)
    if instruction[0] == "push":
        well_formed = "by decide"
    else:
        well_formed = "wfOp (by decide) trivial rfl"
    return f"⟨{index}, {rendered}, by rfl, {well_formed}⟩"
