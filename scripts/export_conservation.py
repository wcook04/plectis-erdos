#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Conservation law for a private-to-public export.

A private-to-public export that mirrors the source tree onto the target
deletes every declaration the target holds and the source does not.  The audit
found three real specimens that such an export would have removed, all of them
mathematics that exists only in the release candidate:

* the `Erdos243/ReciprocalTailRigidity` realisation bridge lines,
* `Erdos249/LcmJumpKillFromDiagonal.lean`,
* the `ExternalVerification257Strong` package.

The rule is a conservation law, not a policy: a reconciled export is the union
of what the source carries and what the target already carries.  Anything the
target loses has to be named and justified, never silently dropped.

The law is written here as a pure function over sets of `(module,
declaration)` pairs so the real exporter can call it before it writes, and so
the test can exercise it without a Lean toolchain or a private checkout.

A name is not a theorem.  An export can carry every `(module, declaration)`
pair across and still change what a declaration says, because the exporter
rewrites imports, relocates solution modules, and projects namespaces.  So the
law has a second half: each declaration also carries a statement digest taken
from its declaration header, and a declaration whose name survives while its
digest moves is reported by name.  The digest is lexical.  It classifies a
declaration for review; it is not the Lean environment and it is not proof
authority.

`statement_digests` deliberately reproduces the exporter-side fingerprint in
`tools/meta/factory/build_plectis_lean_release_topology.py`
(`_declaration_header_fingerprints`) line for line, so the private exporter and
this public statement of the law cannot drift apart silently.  The agreement
itself is asserted in `test_export_conservation.py`.

Stdlib only, no Lean, no network.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Mapping

from lean_declaration_index import qualified_declarations

# One declaration, addressed the way an export addresses it.
Declaration = tuple[str, str]


@dataclass(frozen=True)
class ExportPlan:
    """What a reconciled export would leave on the target."""

    source_only: frozenset[Declaration]
    target_only: frozenset[Declaration]
    shared: frozenset[Declaration]
    reconciled: frozenset[Declaration]


@dataclass
class ConservationReport:
    """The verdict, plus the declarations that motivated it."""

    conserved: bool
    deleted: frozenset[Declaration] = field(default_factory=frozenset)
    added: frozenset[Declaration] = field(default_factory=frozenset)

    def describe(self) -> list[str]:
        lines = []
        for module, name in sorted(self.deleted):
            lines.append(f"export would delete target-only declaration {module}:{name}")
        return lines


def plan_export(
    source: Iterable[Declaration], target: Iterable[Declaration]
) -> ExportPlan:
    """Reconcile two declaration sets: the export is their union."""
    source_set = frozenset(source)
    target_set = frozenset(target)
    return ExportPlan(
        source_only=source_set - target_set,
        target_only=target_set - source_set,
        shared=source_set & target_set,
        reconciled=source_set | target_set,
    )


def check_conservation(
    source: Iterable[Declaration],
    target: Iterable[Declaration],
    result: Iterable[Declaration],
) -> ConservationReport:
    """Does `result` preserve every declaration present only in `target`?

    This is the check an exporter runs against its own proposed output.  A
    mirror export fails it exactly on the declarations the target owns alone.
    """
    target_set = frozenset(target)
    source_set = frozenset(source)
    result_set = frozenset(result)
    deleted = (target_set - result_set) | (source_set - result_set)
    added = result_set - (source_set | target_set)
    return ConservationReport(
        conserved=not deleted and not added,
        deleted=frozenset(deleted),
        added=frozenset(added),
    )


def mirror_export(
    source: Iterable[Declaration], target: Iterable[Declaration]
) -> frozenset[Declaration]:
    """The export that caused the failure: the target becomes the source."""
    del target
    return frozenset(source)


def reconciled_export(
    source: Iterable[Declaration], target: Iterable[Declaration]
) -> frozenset[Declaration]:
    """The export that satisfies the conservation law."""
    return plan_export(source, target).reconciled


def declarations_of_tree(root: Path, modules: Iterable[str]) -> set[Declaration]:
    """Read `(module, declaration)` pairs out of real Lean sources."""
    found: set[Declaration] = set()
    for module in modules:
        path = root / module
        for name in qualified_declarations(path):
            found.add((module, name))
    return found


# --- the second half of the law: a name is not a theorem ---------------------

# Kept identical to `_declaration_header_fingerprints` in the private exporter
# `tools/meta/factory/build_plectis_lean_release_topology.py`.
DECLARATION_HEADER_PATTERN = re.compile(
    r"^\s*(?:protected\s+|private\s+)?"
    r"(?:theorem|lemma|def|abbrev|opaque|axiom|class|structure|inductive)\s+"
    r"([A-Za-z0-9_'.]+)(.*)$"
)


def statement_digest(header: str) -> str:
    """Digest one declaration header, whitespace-normalised.

    This is a lexical statement fingerprint, not the elaborated type.  It moves
    when a hypothesis, a binder, or the quantified domain in the header moves,
    which is the change class a name-only check cannot see.
    """
    normalised = re.sub(r"\s+", " ", header).strip()
    return "sha256:" + hashlib.sha256(normalised.encode("utf-8")).hexdigest()


def statement_digests(text: str) -> dict[str, str]:
    """Map every declaration named in one Lean source to its header digest."""
    digests: dict[str, str] = {}
    for line in text.splitlines():
        match = DECLARATION_HEADER_PATTERN.match(line)
        if match:
            digests[match.group(1)] = statement_digest(match.group(0))
    return digests


def statements_of_tree(
    root: Path, modules: Iterable[str]
) -> dict[Declaration, str]:
    """Read `(module, declaration) -> statement digest` out of real sources."""
    found: dict[Declaration, str] = {}
    for module in modules:
        path = root / module
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for name, digest in statement_digests(text).items():
            found[(module, name)] = digest
    return found


@dataclass
class StatementReport:
    """Which declarations kept their name and lost their statement."""

    conserved: bool
    absent: frozenset[Declaration] = field(default_factory=frozenset)
    restated: frozenset[Declaration] = field(default_factory=frozenset)

    def describe(self) -> list[str]:
        lines = [
            f"export drops source declaration {module}:{name}"
            for module, name in sorted(self.absent)
        ]
        lines.extend(
            f"export keeps the name {module}:{name} and changes its statement"
            for module, name in sorted(self.restated)
        )
        return lines


def check_statement_conservation(
    source: Mapping[Declaration, str],
    result: Mapping[Declaration, str],
) -> StatementReport:
    """Every source declaration must reach the output saying the same thing.

    Two failures, kept apart because they need different repairs: a declaration
    the export never wrote, and a declaration the export wrote under its old
    name with a new statement.  The second is the one a `(module, name)` set
    comparison reports as conserved.
    """
    absent = {key for key in source if key not in result}
    restated = {
        key
        for key, digest in source.items()
        if key in result and result[key] != digest
    }
    return StatementReport(
        conserved=not absent and not restated,
        absent=frozenset(absent),
        restated=frozenset(restated),
    )
