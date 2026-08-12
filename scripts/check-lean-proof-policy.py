#!/usr/bin/env python3
"""Conservatively reject forbidden spellings in scoped Lean sources.

This checker intentionally does *not* parse or tokenize Lean.  It scans raw
source so comments, docstrings, ordinary/raw/interpolated strings, character
literals, escaped identifiers, and operator adjacency cannot hide a banned
mechanism.  Consequently, comments and test strings in the checked scope must
be reworded rather than mention a forbidden spelling.

The existing soundness census uses `#print axioms`, so `axiom` is the one
exception to the unconditional-substring rule: every raw singular spelling is
rejected while the plural census spelling remains allowed.  `maxHeartbeats`
remains permitted only with a complete, nonzero Lean Nat literal.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


FORBIDDEN_SUBSTRINGS = (
    "sorryAx",
    "CertifiedArtifact",
    "native_decide",
    "sorry",
    "admit",
)

SINGULAR_AXIOM = re.compile(r"axiom(?!s)")

NAT_LITERAL = r"(?:0[xX][0-9a-fA-F_]+|0[bB][01_]+|0[oO][0-7_]+|[0-9][0-9_]*)"
HEARTBEAT_SETTING = re.compile(
    rf"maxHeartbeats\s+(?P<literal>{NAT_LITERAL})(?![A-Za-z0-9_])",
    re.MULTILINE,
)
HEARTBEAT_NAME = re.compile(r"maxHeartbeats")

BROAD_BLS_PROOF_SUPPORT_IMPORT = re.compile(
    r"^[ \t]*import[ \t]+Challenge\.Bls12381\.ProofSupport[ \t]*$",
    re.MULTILINE,
)
COMPLETED_BLS_ADD_TREES = frozenset(("Bls12381G1Add", "Bls12381G2Add"))
COMPLETED_BLS_ADD_CHECK_PREFIXES = ("Bls12381G1Add", "Bls12381G2Add")
COMPLETED_BLS_ADD_CHECK_IMPORT = re.compile(
    r"^[ \t]*import[ \t]+Checks\.Bls12381G[12]Add[A-Za-z0-9_.]*[ \t]*$",
    re.MULTILINE,
)


def source_line(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def nat_value(spelling: str) -> int:
    normalized = spelling.replace("_", "")
    lowered = normalized.lower()
    if lowered.startswith("0x"):
        return int(normalized[2:], 16)
    if lowered.startswith("0b"):
        return int(normalized[2:], 2)
    if lowered.startswith("0o"):
        return int(normalized[2:], 8)
    return int(normalized, 10)


def violations(source: str, path: Path | None = None) -> list[tuple[int, str]]:
    findings: list[tuple[int, str]] = []

    for spelling in FORBIDDEN_SUBSTRINGS:
        start = 0
        while (offset := source.find(spelling, start)) >= 0:
            findings.append(
                (source_line(source, offset), f"forbidden raw spelling: {spelling}")
            )
            start = offset + len(spelling)

    for match in SINGULAR_AXIOM.finditer(source):
        findings.append(
            (source_line(source, match.start()), "forbidden axiom declaration")
        )

    for name_match in HEARTBEAT_NAME.finditer(source):
        setting_match = HEARTBEAT_SETTING.match(source, name_match.start())
        if setting_match is None:
            findings.append(
                (
                    source_line(source, name_match.start()),
                    "forbidden unparseable maxHeartbeats setting",
                )
            )
        elif nat_value(setting_match.group("literal")) == 0:
            findings.append(
                (
                    source_line(source, name_match.start()),
                    "forbidden unlimited maxHeartbeats setting",
                )
            )

    if path is not None and COMPLETED_BLS_ADD_TREES.intersection(path.parts):
        for match in BROAD_BLS_PROOF_SUPPORT_IMPORT.finditer(source):
            findings.append(
                (
                    source_line(source, match.start()),
                    "forbidden broad BLS proof-support import",
                )
            )

    if path is not None and "Checks" in path.parts and path.name.startswith(
        COMPLETED_BLS_ADD_CHECK_PREFIXES
    ):
        for match in COMPLETED_BLS_ADD_CHECK_IMPORT.finditer(source):
            findings.append(
                (
                    source_line(source, match.start()),
                    "forbidden completed-ADD check-to-check import",
                )
            )

    return sorted(findings)


def lean_files(arguments: list[str]) -> list[Path]:
    files: set[Path] = set()
    for argument in arguments:
        path = Path(argument)
        if path.is_dir():
            files.update(candidate for candidate in path.rglob("*.lean") if candidate.is_file())
        elif path.is_file() and path.suffix == ".lean":
            files.add(path)
        else:
            raise ValueError(f"not a Lean file or directory: {argument}")
    return sorted(files)


def main() -> int:
    if len(sys.argv) < 2:
        print(f"usage: {Path(sys.argv[0]).name} PATH [PATH ...]", file=sys.stderr)
        return 2

    try:
        files = lean_files(sys.argv[1:])
    except ValueError as error:
        print(error, file=sys.stderr)
        return 2

    rejected = False
    for path in files:
        for line, message in violations(path.read_text(encoding="utf-8"), path):
            print(f"{path}:{line}: {message}", file=sys.stderr)
            rejected = True
    return 1 if rejected else 0


if __name__ == "__main__":
    raise SystemExit(main())
