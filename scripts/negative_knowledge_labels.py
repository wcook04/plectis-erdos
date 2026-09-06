#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Negative knowledge needs a label and evidence, not an adjective.

Saying a route is closed, dead, or impossible is a mathematical claim.  It is
also the claim most likely to be made in passing, and a route written off in
passing is a result nobody can check and nobody can reopen.  The audits found
strong results buried behind exactly this kind of sentence.

So the vocabulary is closed and each term carries a different obligation:

* `proved_class_obstruction` - a theorem rules out a whole class of attacks;
* `counterexample_to_proposal` - one explicit object refutes one proposal;
* `target_equivalent_reformulation` - the route is equivalent to the target,
  so it is circular rather than closed;
* `conditional_reduction` - the route survives, conditional on an unproved
  hypothesis;
* `empirical_deprioritisation` - a search or a receipt says the route looks
  unpromising, which is a decision and never a proof.

A surface using closure language for a route must carry one of these labels
with evidence.  `empirical_deprioritisation` in particular is the label that
stops a search result from being reported as a proof.

Stdlib only, no Lean, no network.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

NEGATIVE_KNOWLEDGE_LABELS = frozenset(
    {
        "proved_class_obstruction",
        "counterexample_to_proposal",
        "target_equivalent_reformulation",
        "conditional_reduction",
        "empirical_deprioritisation",
    }
)

# Labels whose evidence is a decision rather than a proof.  Naming them keeps
# a deprioritisation from being read as an obstruction.
NON_PROOF_LABELS = frozenset({"empirical_deprioritisation"})

CLOSURE_WORDS = ("closed", "dead", "impossible")

# Closure language is only a route claim when it is applied to a route.  The
# corpus uses "closed" constantly in its ordinary mathematical senses (a closed
# cylinder, a closed form, a closed proposition), and flagging those would bury
# the real cases under noise.
ROUTE_WORDS = (
    "route",
    "approach",
    "mechanism",
    "lane",
    "programme",
    "program",
    "attack",
    "strategy",
    "avenue",
    "direction",
    "line of attack",
    "method",
)

_CLOSURE_PATTERN = re.compile(
    r"(?<![A-Za-z])(" + "|".join(CLOSURE_WORDS) + r")(?![A-Za-z])",
    re.IGNORECASE,
)
_ROUTE_PATTERN = re.compile(
    r"(?<![A-Za-z])(" + "|".join(ROUTE_WORDS) + r")s?(?![A-Za-z])",
    re.IGNORECASE,
)


class UnknownLabel(ValueError):
    """Raised when a negative-knowledge label is outside the closed vocabulary."""


@dataclass(frozen=True)
class ClosureUse:
    """One place where a surface calls a route closed, dead, or impossible."""

    surface: str
    line: int
    word: str
    text: str


@dataclass(frozen=True)
class LabelledRoute:
    """A route write-off, as it should be recorded."""

    route_id: str
    statement: str
    label: str | None = None
    evidence: str | None = None


def check_label(label: str) -> str:
    """Reject a label outside the closed vocabulary."""
    if label not in NEGATIVE_KNOWLEDGE_LABELS:
        raise UnknownLabel(
            f"negative-knowledge label is not in the vocabulary: {label!r}"
        )
    return label


def uses_closure_language(text: str) -> str | None:
    """Return the closure word a sentence applies to a route, if any."""
    for sentence in re.split(r"(?<=[.;!?])\s+", text):
        closure = _CLOSURE_PATTERN.search(sentence)
        if closure and _ROUTE_PATTERN.search(sentence):
            return closure.group(1).lower()
    return None


def audit_routes(routes: Iterable[LabelledRoute]) -> list[str]:
    """Every route written off in closure language needs a label and evidence."""
    errors: list[str] = []
    for route in routes:
        word = uses_closure_language(route.statement)
        if word is None:
            continue
        if route.label is None:
            errors.append(
                f"{route.route_id}: calls a route {word!r} with no "
                "negative-knowledge label"
            )
            continue
        try:
            check_label(route.label)
        except UnknownLabel as error:
            errors.append(f"{route.route_id}: {error}")
            continue
        if not (route.evidence or "").strip():
            errors.append(
                f"{route.route_id}: label {route.label} carries no evidence"
            )
    return errors


def scan_text(surface: str, text: str) -> list[ClosureUse]:
    """Report every line where a surface applies closure language to a route."""
    uses: list[ClosureUse] = []
    for number, line in enumerate(text.splitlines(), start=1):
        word = uses_closure_language(line)
        if word is None:
            continue
        uses.append(
            ClosureUse(
                surface=surface,
                line=number,
                word=word,
                text=line.strip()[:280],
            )
        )
    return uses


def scan_surfaces(paths: dict[str, Path]) -> list[ClosureUse]:
    """Scan real reader surfaces, reporting rather than judging."""
    uses: list[ClosureUse] = []
    for surface, path in paths.items():
        if not path.is_file():
            continue
        uses.extend(scan_text(surface, path.read_text(errors="replace")))
    return uses
