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

Stdlib only, no Lean, no network.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

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
