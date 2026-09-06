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

Detection is contextual, because three ordinary sentences look like closure
claims to a word match and are not:

* a sentence saying a route is **not** closed is the opposite of a write-off,
  and counting it is how a surviving route gets filed as a dead one;
* a sentence **quoting** an informal closure in order to say it is informal is
  reporting somebody else's claim while stating its limit;
* a declaration name such as `depth29_cutoff26_promotion_impossible` is an
  identifier, not prose.

None of the three carries a labelling obligation.  What remains after they are
removed is bound to the dispositions the repository already records, so a route
the frontier ledger has already disposed is not reported as unlabelled twice.

Stdlib only, no Lean, no network.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Mapping, Sequence

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

# The boundary excludes `_` and digits so a declaration name carrying a closure
# word, such as `depth29_cutoff26_promotion_impossible`, is an identifier rather
# than a sentence about a route.
_CLOSURE_PATTERN = re.compile(
    r"(?<![A-Za-z0-9_])(" + "|".join(CLOSURE_WORDS) + r")(?![A-Za-z0-9_])",
    re.IGNORECASE,
)
_ROUTE_PATTERN = re.compile(
    r"(?<![A-Za-z0-9_])(" + "|".join(ROUTE_WORDS) + r")s?(?![A-Za-z0-9_])",
    re.IGNORECASE,
)

# Words that reverse the closure claim when they govern the closure word.
NEGATION_WORDS = (
    "not",
    "never",
    "nor",
    "hardly",
    "far from",
    "no longer",
    "isn't",
    "is n't",
    "cannot",
)
_NEGATION_PATTERN = re.compile(
    r"(?<![A-Za-z0-9_])(" + "|".join(re.escape(word) for word in NEGATION_WORDS) + r")(?![A-Za-z0-9_])",
    re.IGNORECASE,
)

# A closure word reached inside single quotes or backticks is being reported,
# not asserted.  Double quotes are excluded because the surfaces include JSON,
# where every string value sits inside them.
_QUOTED_SPAN_PATTERN = re.compile(r"'[^']{0,400}'|`[^`]{0,400}`")

# Phrases that say the quoted closure is somebody's informal claim, or that
# name its limit.  A quotation plus one of these is a report about a claim.
LIMIT_PHRASES = (
    "informal",
    "not formalised",
    "not formalized",
    "no declaration",
    "not proved",
    "unproved",
    "does not establish",
    "not formalised content",
)
_LIMIT_PATTERN = re.compile(
    "|".join(re.escape(phrase) for phrase in LIMIT_PHRASES), re.IGNORECASE
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


def _quoted_spans(sentence: str) -> list[tuple[int, int]]:
    return [match.span() for match in _QUOTED_SPAN_PATTERN.finditer(sentence)]


def _is_negated(sentence: str, position: int) -> bool:
    """Does a negation govern the closure word at `position`?

    The window is the clause the closure word sits in, which is what "the
    route is NOT closed" needs and what "the route is closed, and nothing else
    is" must not pick up.
    """
    clause_start = max(
        (sentence.rfind(mark, 0, position) for mark in (",", ";", ":", " so ", " because ")),
        default=-1,
    )
    return bool(_NEGATION_PATTERN.search(sentence[clause_start + 1 : position]))


def sentence_closure_word(sentence: str) -> str | None:
    """Return the closure word this sentence asserts of a route, if any."""
    if not _ROUTE_PATTERN.search(sentence):
        return None
    spans = _quoted_spans(sentence)
    limits = bool(_LIMIT_PATTERN.search(sentence))
    for closure in _CLOSURE_PATTERN.finditer(sentence):
        start = closure.start()
        if limits and any(begin <= start < end for begin, end in spans):
            # A quoted closure inside a sentence that states its limit is a
            # report about a claim, not a claim.
            continue
        if _is_negated(sentence, start):
            continue
        return closure.group(1).lower()
    return None


def uses_closure_language(text: str) -> str | None:
    """Return the closure word a passage applies to a route, if any."""
    for sentence in re.split(r"(?<=[.;!?])\s+", text):
        word = sentence_closure_word(sentence)
        if word is not None:
            return word
    return None


# --- reviewed route dispositions ---------------------------------------------

# Where the repository already disposes of a route, and under which label. The
# mapping is stated, not inferred: each source says what kind of disposition it
# records, and nothing outside these sources is treated as a disposition.
FRONTIER_DISPOSITION_SOURCES = (
    ("bare_equivalences", "node", "target_equivalent_reformulation"),
    ("excluded_from_nonrecurring_with_reason", "node", "empirical_deprioritisation"),
    ("open_antecedents", "id", "conditional_reduction"),
)

# The one claim status whose taxonomy entry names a negative-knowledge label
# directly: an exact implication whose remaining hypothesis is open.
CLAIM_STATUS_DISPOSITIONS = {"conditional reduction": "conditional_reduction"}


def route_dispositions(
    frontier: Mapping[str, object], claims: Mapping[str, object]
) -> dict[str, str]:
    """Every route id the repository has already disposed, with its label."""
    dispositions: dict[str, str] = {}
    for section, key, label in FRONTIER_DISPOSITION_SOURCES:
        rows = frontier.get(section)
        if not isinstance(rows, list):
            continue
        for row in rows:
            if not isinstance(row, dict):
                continue
            route_id = str(row.get(key, "")).strip()
            if route_id:
                dispositions.setdefault(route_id, check_label(label))
    claim_rows = claims.get("claims")
    if isinstance(claim_rows, list):
        for claim in claim_rows:
            if not isinstance(claim, dict):
                continue
            label = CLAIM_STATUS_DISPOSITIONS.get(str(claim.get("status", "")))
            claim_id = str(claim.get("id", "")).strip()
            if label and claim_id:
                dispositions.setdefault(claim_id, check_label(label))
    return dispositions


def disposition_for(text: str, dispositions: Mapping[str, str]) -> tuple[str, str] | None:
    """Return the disposed route id this line names, and its label."""
    best: tuple[str, str] | None = None
    for route_id, label in dispositions.items():
        if len(route_id) < 8 or route_id not in text:
            continue
        if best is None or len(route_id) > len(best[0]):
            best = (route_id, label)
    return best


def split_by_disposition(
    uses: Sequence["ClosureUse"], dispositions: Mapping[str, str]
) -> tuple[list[dict], list["ClosureUse"]]:
    """Separate closure uses the ledger already disposes from the residual."""
    disposed: list[dict] = []
    residual: list[ClosureUse] = []
    for use in uses:
        match = disposition_for(use.text, dispositions)
        if match is None:
            residual.append(use)
            continue
        route_id, label = match
        disposed.append(
            {
                "surface": use.surface,
                "line": use.line,
                "word": use.word,
                "route_id": route_id,
                "label": label,
            }
        )
    return disposed, residual


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
