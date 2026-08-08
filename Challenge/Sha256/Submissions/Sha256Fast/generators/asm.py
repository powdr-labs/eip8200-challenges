"""Tiny EVM assembler: fixed-width PUSH2 labels, two-pass resolution."""

OPS = {
    "STOP": 0x00, "ADD": 0x01, "MUL": 0x02, "SUB": 0x03, "DIV": 0x04,
    "MOD": 0x06, "ADDMOD": 0x08, "MULMOD": 0x09, "SIGNEXTEND": 0x0B,
    "LT": 0x10, "GT": 0x11, "SLT": 0x12, "SGT": 0x13, "EQ": 0x14,
    "ISZERO": 0x15, "AND": 0x16, "OR": 0x17, "XOR": 0x18, "NOT": 0x19,
    "BYTE": 0x1A, "SHL": 0x1B, "SHR": 0x1C, "SAR": 0x1D,
    "CALLDATALOAD": 0x35, "CALLDATASIZE": 0x36, "CALLDATACOPY": 0x37,
    "POP": 0x50, "MLOAD": 0x51, "MSTORE": 0x52, "MSTORE8": 0x53,
    "JUMP": 0x56, "JUMPI": 0x57, "PC": 0x58, "MSIZE": 0x59, "GAS": 0x5A,
    "JUMPDEST": 0x5B, "MCOPY": 0x5E,
    "RETURN": 0xF3, "REVERT": 0xFD, "INVALID": 0xFE,
}


class Asm:
    def __init__(self):
        self.items = []          # (kind, ...) stream
        self.labels = {}
        self.marks = []          # (name, byte offset)
        self._pos = 0

    def mark(self, name):
        self.marks.append((name, self._pos))
        return self

    # -- emission -----------------------------------------------------
    def op(self, name):
        self.items.append(("op", OPS[name]))
        self._pos += 1
        return self

    def __getattr__(self, name):
        upper = name.upper()
        if upper in OPS:
            return lambda: self.op(upper)
        raise AttributeError(name)

    def push(self, value, width=None):
        assert value >= 0
        if value == 0 and width is None:
            self.items.append(("op", 0x5F))
            self._pos += 1
            return self
        body = value.to_bytes(width, "big") if width else \
            value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")
        self.items.append(("op", 0x5F + len(body)))
        for b in body:
            self.items.append(("op", b))
        self._pos += 1 + len(body)
        return self

    def push_label(self, label):
        self.items.append(("pushlabel", label))
        self._pos += 3
        return self

    def label(self, name):
        self.items.append(("label", name))
        self.op("JUMPDEST")
        return self

    def dup(self, n):
        assert 1 <= n <= 16, f"DUP{n} out of range"
        return self.op_raw(0x7F + n)

    def swap(self, n):
        assert 1 <= n <= 16, f"SWAP{n} out of range"
        return self.op_raw(0x8F + n)

    def op_raw(self, byte):
        self.items.append(("op", byte))
        self._pos += 1
        return self

    # -- assembly -----------------------------------------------------
    def assemble(self):
        # pass 1: sizes (pushlabel is always PUSH2 = 3 bytes)
        pos = 0
        labels = {}
        for item in self.items:
            if item[0] == "op":
                pos += 1
            elif item[0] == "pushlabel":
                pos += 3
            elif item[0] == "label":
                labels[item[1]] = pos
        out = bytearray()
        for item in self.items:
            if item[0] == "op":
                out.append(item[1])
            elif item[0] == "pushlabel":
                out.append(0x61)
                out.extend(labels[item[1]].to_bytes(2, "big"))
        self.labels = labels
        return bytes(out)
