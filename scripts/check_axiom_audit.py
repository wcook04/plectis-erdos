#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check fresh Lean #print axioms output against the Comparator axiom budget.

This validates reported transitive dependencies, not statement meaning or the
authenticity of an arbitrary log. CI must first re-elaborate the audit sources.
Lean 4.29 native evaluators introduce dedicated axioms, so a blacklist of old
compiler-trust names cannot enforce the budget.
"""
from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path

from lean_source import lean_code_without_comments_and_strings, qualified_declaration_lines

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})
ENTRY = re.compile(
    r"(?m)^[ \t]*(?:[^\n]+:\d+:\d+: info: )?'(?P<name>[^\n]+)' "
    r"(?:(?P<none>does not depend on any axioms)|depends on axioms: "
    r"\[(?P<axioms>[^\[\]]*)\])[ \t]*$"
)
MARKER = re.compile(r"(?:depends on axioms|does not depend on any axioms)")
PRINT_AXIOMS = re.compile(r"^[ \t]*#print[ \t]+axioms[ \t]+([A-Za-z_][\w'.]*)[ \t]*$")


def expected_declarations(sources: list[Path]) -> set[str]:
    """Resolve the literal commands in the audit owners with the existing lexer.

    These sources use simple #print axioms commands inside namespace/section
    scopes. Refuse unsupported commands rather than silently reduce coverage.
    This is lexical source identity, not Lean name elaboration.
    """
    expected = set()
    for source in sources:
        lines = lean_code_without_comments_and_strings(source.read_text(encoding="utf-8")).splitlines()
        projected = []
        command_lines = set()
        for index, line in enumerate(lines, 1):
            command = PRINT_AXIOMS.fullmatch(line)
            if command:
                projected.append(f"theorem {command.group(1)} : True := by trivial")
                command_lines.add(index)
            elif re.search(r"#print\b", line):
                raise ValueError(f"unsupported audit command in {source}:{index}")
            else:
                projected.append(line if re.match(r"\s*(?:namespace|section|noncomputable section|end)\b", line) else "")
        found = qualified_declaration_lines("\n".join(projected))
        if not command_lines or {line for positions in found.values() for line in positions} != command_lines:
            raise ValueError(f"audit source has no complete resolvable command roster: {source}")
        for name, positions in found.items():
            if len(positions) != 1 or name in expected:
                raise ValueError(f"duplicate audited declaration {name}")
            expected.add(name)
    return expected


def permitted_axioms(config: dict) -> frozenset[str]:
    """Use the existing config while refusing a widened or malformed budget."""
    names = config.get("permitted_axioms")
    if (not isinstance(names, list) or not all(isinstance(n, str) for n in names)
            or len(names) != len(set(names)) or frozenset(names) != ALLOWED_AXIOMS):
        raise ValueError("permitted_axioms must be exactly propext, Quot.sound, Classical.choice")
    return frozenset(names)


def audit_errors(text: str, allowed: frozenset[str], expected: set[str] | None = None) -> tuple[int, list[str]]:
    entries = list(ENTRY.finditer(text))
    errors = []
    if not entries:
        errors.append("axiom audit produced no declaration reports")
    names = Counter(entry.group("name") for entry in entries)
    for name, count in names.items():
        if count != 1:
            errors.append(f"duplicate declaration report: {name}")
    if expected is not None:
        for name in sorted(expected - names.keys()):
            errors.append(f"missing declaration report: {name}")
        for name in sorted(names.keys() - expected):
            errors.append(f"unexpected declaration report: {name}")
    for marker in MARKER.finditer(text):
        if not any(entry.start() <= marker.start() < entry.end() for entry in entries):
            errors.append("malformed axiom report: " + text[marker.start():].splitlines()[0])
    for entry in entries:
        if entry.group("none"):
            continue
        names = [name.strip() for name in entry.group("axioms").split(",")]
        if not all(names):
            errors.append(f"{entry.group('name')}: malformed axiom list")
            continue
        for name in names:
            if name not in allowed:
                errors.append(f"{entry.group('name')}: forbidden axiom {name}")
    return len(entries), errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path, help="fresh output from Lean audit sources")
    parser.add_argument("--config", type=Path, default=ROOT / "verification/comparator.json")
    parser.add_argument("--audit-source", type=Path, action="append",
                        help="require exactly the declarations printed by this source; repeat for every audit owner")
    args = parser.parse_args(argv)
    try:
        config = json.loads(args.config.read_text(encoding="utf-8"))
        if not isinstance(config, dict):
            raise ValueError("Comparator config must be a JSON object")
        allowed = permitted_axioms(config)
        expected = expected_declarations(args.audit_source) if args.audit_source else None
        count, errors = audit_errors(args.log.read_text(encoding="utf-8"), allowed, expected)
    except (OSError, ValueError) as exc:
        print(f"axiom audit: FAIL {exc}")
        return 1
    for error in errors:
        print(f"axiom audit: FAIL {error}")
    if errors:
        return 1
    print(f"axiom audit: PASS {count} declaration reports within the permitted budget")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
