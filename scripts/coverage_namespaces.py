#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Three separate coverage questions about one declaration, kept separate.

The second audit wave found private-frontier associations being counted as
public coverage.  That happens when one boolean stands in for three different
questions:

1. is the declaration present in the candidate source at all;
2. is it bound by a row in the public claim register;
3. is it exposed by a reader surface, meaning named in `docs/RESULTS.md` or in
   a paper source.

A declaration can answer yes to the first and no to the other two, and that is
the ordinary state of a strong result nobody has published yet.  Collapsing
the three into "covered" is what let a frontier ledger row, which is private
working state, be reported as public coverage.

The register vocabulary is closed.  An association carrying an unrecognised
register raises rather than defaulting to public, because defaulting to
public is the failure this module exists to prevent.

Stdlib only, no Lean, no network.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Iterable, Mapping

# The one register whose rows are a public claim on the mathematics.
PUBLIC_CLAIM_REGISTER = "docs/claims.json"

# Registers that carry working associations only.  A row here is a note to the
# programme, never a claim to a reader.
PRIVATE_FRONTIER_REGISTERS = frozenset(
    {
        "docs/semantic/frontier.json",
        "private_frontier",
        "claim_frontier_ledger",
        "launch_selection_v1.json",
        "private_tree_note",
    }
)

KNOWN_REGISTERS = frozenset({PUBLIC_CLAIM_REGISTER}) | PRIVATE_FRONTIER_REGISTERS


class UnknownRegister(ValueError):
    """Raised when an association names a register the vocabulary does not hold."""


@dataclass(frozen=True)
class Association:
    """One (declaration, row) binding, tagged with the register it came from."""

    declaration: str
    row_id: str
    register: str


@dataclass(frozen=True)
class Coverage:
    """The three questions, answered separately and never merged."""

    declaration: str
    present_in_candidate_source: bool
    bound_by_public_claim_row: bool
    exposed_by_reader_surface: bool

    @property
    def public_claim_row(self) -> bool:
        """Alias used by the audit vocabulary."""
        return self.bound_by_public_claim_row

    @property
    def buried(self) -> bool:
        """Present in the source and reachable from no public surface at all."""
        return self.present_in_candidate_source and not (
            self.bound_by_public_claim_row or self.exposed_by_reader_surface
        )


def check_register(register: str) -> str:
    """Reject an unrecognised register instead of treating it as public."""
    if register not in KNOWN_REGISTERS:
        raise UnknownRegister(
            f"association register is not in the closed vocabulary: {register!r}"
        )
    return register


def is_public_register(register: str) -> bool:
    """Only the public claim register can bind a public claim row."""
    return check_register(register) == PUBLIC_CLAIM_REGISTER


def name_spellings(declaration: str) -> set[str]:
    """Every namespace suffix a source or surface may use for one declaration."""
    parts = declaration.split(".")
    return {".".join(parts[cut:]) for cut in range(len(parts))}


def _mentions(text: str, declaration: str) -> bool:
    for spelling in name_spellings(declaration):
        pattern = re.compile(
            r"(?<![A-Za-z0-9_.'])" + re.escape(spelling) + r"(?![A-Za-z0-9_.'])"
        )
        if pattern.search(text):
            return True
    return False


def classify(
    declaration: str,
    *,
    candidate_declarations: Iterable[str],
    associations: Iterable[Association],
    reader_surfaces: Mapping[str, str],
) -> Coverage:
    """Answer the three coverage questions for one declaration."""
    present = any(
        name_spellings(candidate) & name_spellings(declaration)
        for candidate in candidate_declarations
    )
    bound = False
    for association in associations:
        if not (name_spellings(association.declaration) & name_spellings(declaration)):
            continue
        if is_public_register(association.register):
            bound = True
    exposed = any(
        _mentions(text, declaration) for text in reader_surfaces.values()
    )
    return Coverage(
        declaration=declaration,
        present_in_candidate_source=present,
        bound_by_public_claim_row=bound,
        exposed_by_reader_surface=exposed,
    )


def public_claim_rows_only(
    associations: Iterable[Association],
) -> list[Association]:
    """Drop every association that is not a public claim row."""
    return [
        association
        for association in associations
        if is_public_register(association.register)
    ]
