#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""The research record: rounds, returns and outputs, and what each still owes.

The record is one append-only journal, ``docs/research-commons/record/journal.jsonl``,
committed with the repository. Each line is one canonical JSON object with the
fields ``sequence`` (from 0), ``previous`` (the ``event_sha`` of the prior line,
or 64 zeros), ``kind``, ``subject``, ``detail``, ``recorded_at`` (UTC, ISO-8601
with ``Z``) and ``event_sha``, the sha256 of the canonical body without
``event_sha``. ``verify`` checks the chain, the sequence, every hash, the
canonical form of every line, a torn final line (an explicit error, never a
silent truncation), each kind's schema, and the references between events.

Event kinds:

* ``round_opened``: a packet sent for research, with its declared consumers.
* ``return_received``: custody of one returned file (bytes, hash, the private
  intake that holds it, and an optional public copy in this repository).
* ``review_recorded``: a reviewer's disposition of a return. A later review of
  the same return invalidates the consumer dispositions recorded before it.
* ``component_disposed``: what happened to one component of a return (taken,
  adapted, rejected, deferred) and where it landed. This is the coverage ledger.
* ``output_declared``: a result the programme owes (a Lean declaration, a pull
  request, a paper section, a record row or a tool) with the milestones it needs.
* ``milestone_reported``: a milestone that cannot be computed from the checkout,
  with its evidence and evidence class.
* ``consumer_disposed``: what a declared consumer did with a return or output;
  a deferral names an owner and a re-entry trigger.
* ``round_sealed``: no further arrivals are expected for a round.

Milestones that the checkout can answer are computed, never reported:
``lean_on_main`` (the declaration is listed in ``docs/declaration_atlas.json``
and its module is a compiled target, see ``compiled_modules``),
``short_paper_linked`` and ``long_record_linked`` (a row of
``docs/paper_lean_coverage.json`` for a short or long paper names it),
``claim_registered`` (``docs/claims.json`` lists it), ``comparator_listed`` (a
Comparator configuration under ``verification/`` names it or its wrapper) and
``pr_merged`` (the merge commit is an ancestor of HEAD). Each computed milestone
reads ``done``, ``missing`` or ``unknown`` with the evidence it used.

The atlas is a navigation projection of the Lean source at the formal-source
pin (it says ``projection_not_authority``). A listing there shows the name
exists in that source; it does not show that any CI job compiled the module.
The evidence class of ``lean_on_main`` is therefore ``declaration_atlas_at_pin``,
and the milestone is done only when the module is also in
``compiled_modules(root)``: the modules the default build roots and the
coverage-build targets reach through the import graph in ``docs/claims.json``.
A module that is listed but not reached reads ``missing`` with
``compiled_target: false``.

The journal records custody and decisions. It confers no mathematical
authority: that stays with the Lean kernel at the formal-source pin, with the
evidence class each entry states. Appending is refused when ``CI`` is set.
Standard library only.
"""

from __future__ import annotations

import argparse
import datetime as dt
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Callable, Iterator

sys.path.insert(0, str(Path(__file__).resolve().parent))
import coverage_build_targets  # noqa: E402
import relation_registry as registry  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
JOURNAL_PATH = "docs/research-commons/record/journal.jsonl"
COVERAGE_PATH = "docs/paper_lean_coverage.json"
CLAIMS_PATH = "docs/claims.json"
VERIFICATION_DIR = "verification"
ZERO = "0" * 64
EVENT_FIELDS = ("sequence", "previous", "kind", "subject", "detail", "recorded_at", "event_sha")

DECLARATION_MILESTONES = ("lean_on_main", "short_paper_linked", "long_record_linked",
                          "claim_registered", "comparator_listed")
COMPUTED_MILESTONES = DECLARATION_MILESTONES + ("pr_merged",)
MILESTONE_EVIDENCE = {
    "lean_on_main": "declaration_atlas_at_pin",
    "short_paper_linked": "paper_coverage_projection",
    "long_record_linked": "paper_coverage_projection",
    "claim_registered": "claim_registry_entry",
    "comparator_listed": "comparator_config_entry",
    "pr_merged": "git_ancestry",
}
REVIEW_DISPOSITIONS = ("admitted_for_integration", "repair_required", "rejected_retained",
                       "duplicate", "superseded")
CLOSED_WITHOUT_INTEGRATION = frozenset({"rejected_retained", "duplicate", "superseded"})
COMPONENT_DECISIONS = ("taken", "adapted", "rejected", "deferred")
OUTPUT_KINDS = ("lean_declaration", "pull_request", "paper_section", "record_row", "tool")
CONSUMER_STATUSES = ("updated", "verified_unchanged", "not_applicable", "deferred")
# A reported milestone can never carry the class of a computed checkout fact.
REPORTED_EVIDENCE_CLASSES = ("authored_review", "reported", "external_receipt", "ci_receipt",
                             "kernel_probe_verdict")
LOCATOR_FIELDS = frozenset({"declaration", "module", "pr", "merge_commit", "path"})
CUSTODY_STORE = "type_b_return_intake"

IDENT = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.:/#+-]{0,199}\Z")
MILESTONE_NAME = re.compile(r"[a-z][a-z0-9_]{0,63}\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
COMMIT = re.compile(r"[0-9a-f]{7,40}\Z")
TIMESTAMP = re.compile(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d{1,6})?Z\Z")
PRIVATE_PATH = re.compile(r"(?:^|[\s\"'(=:])(?:/Users/|/home/|/private/|/tmp/|/var/|/root/|~/|[A-Za-z]:\\)")


class RecordError(ValueError):
    """The journal is malformed, or an append would make it so."""


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False)


def event_hash(body: dict[str, Any]) -> str:
    return hashlib.sha256(canonical(body).encode("utf-8")).hexdigest()


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# --------------------------------------------------------------------------
# Field checkers. Each returns an error string or None.
# --------------------------------------------------------------------------

Checker = Callable[[Any], "str | None"]


def c_ident(value: Any) -> str | None:
    return None if isinstance(value, str) and IDENT.match(value) else f"must be an identifier matching {IDENT.pattern}"


def c_text(value: Any) -> str | None:
    return None if isinstance(value, str) and value.strip() else "must be a non-empty string"


def c_sha(value: Any) -> str | None:
    return None if isinstance(value, str) and SHA256.match(value) else "must be 64 lowercase hex digits"


def c_commit(value: Any) -> str | None:
    return None if isinstance(value, str) and COMMIT.match(value) else "must be a 7-40 digit lowercase hex commit"


def c_count(value: Any) -> str | None:
    ok = isinstance(value, int) and not isinstance(value, bool) and value >= 0
    return None if ok else "must be a non-negative integer"


def c_problem(value: Any) -> str | None:
    ok = value is None or (isinstance(value, int) and not isinstance(value, bool) and value > 0)
    return None if ok else "must be a positive integer or null"


def c_enum(options: tuple[str, ...]) -> Checker:
    return lambda value: None if value in options else f"must be one of {list(options)}"


def c_optional(inner: Checker) -> Checker:
    return lambda value: None if value is None else inner(value)


def c_list(inner: Checker, nonempty: bool = False) -> Checker:
    def check(value: Any) -> str | None:
        if not isinstance(value, list):
            return "must be a list"
        if nonempty and not value:
            return "must be a non-empty list"
        if len({canonical(v) for v in value}) != len(value):
            return "must not repeat entries"
        for item in value:
            error = inner(item)
            if error:
                return f"entry {item!r} {error}"
        return None
    return check


def c_repo_path(value: Any) -> str | None:
    if not isinstance(value, str) or not value.strip():
        return "must be a non-empty repository-relative path"
    parts = Path(value).parts
    if value.startswith(("/", "~")) or ".." in parts or "\\" in value:
        return "must be a repository-relative path without '..'"
    return None


def c_custody(value: Any) -> str | None:
    if not isinstance(value, dict) or set(value) != {"store", "batch_id", "return_id"}:
        return "must be {store, batch_id, return_id}"
    if value["store"] != CUSTODY_STORE:
        return f"store must be {CUSTODY_STORE!r}"
    return c_ident(value["batch_id"]) or c_ident(value["return_id"])


def c_reentry(value: Any) -> str | None:
    if value is None:
        return None
    if not isinstance(value, dict) or set(value) != {"owner", "trigger"}:
        return "must be {owner, trigger} or null"
    return c_text(value["owner"]) or c_text(value["trigger"])


def c_locator(value: Any) -> str | None:
    if not isinstance(value, dict) or not value:
        return "must be a non-empty object"
    extra = set(value) - LOCATOR_FIELDS
    if extra:
        return f"has unknown fields {sorted(extra)}"
    for key, item in value.items():
        if key == "pr":
            error = None if isinstance(item, int) and not isinstance(item, bool) and item > 0 else "must be a positive integer"
        elif key == "merge_commit":
            error = c_commit(item)
        elif key == "path":
            error = c_repo_path(item)
        else:
            error = c_text(item)
        if error:
            return f"field {key} {error}"
    return None


# kind -> (subject field, required fields, optional fields)
KINDS: dict[str, tuple[str, dict[str, Checker], dict[str, Checker]]] = {
    "round_opened": ("round_id", {
        "round_id": c_ident, "packet_id": c_ident, "packet_manifest_sha256": c_sha,
        "source_commit": c_commit, "ask": c_text, "consumers": c_list(c_ident, nonempty=True),
        "expected_returns": c_optional(c_count)}, {}),
    "return_received": ("return_id", {
        "return_id": c_ident, "round_id": c_ident, "sha256": c_sha, "bytes": c_count,
        "media_type": c_text, "custody": c_custody, "public_copy": c_optional(c_repo_path)}, {}),
    "review_recorded": ("return_id", {
        "return_id": c_ident, "disposition": c_enum(REVIEW_DISPOSITIONS), "rationale": c_text,
        "reviewer": c_text}, {}),
    "component_disposed": ("return_id", {
        "return_id": c_ident, "component": c_text, "decision": c_enum(COMPONENT_DECISIONS),
        "reason": c_text, "landed_as": c_list(c_text)}, {}),
    "output_declared": ("output_id", {
        "output_id": c_ident, "kind": c_enum(OUTPUT_KINDS), "locator": c_locator,
        "problem": c_problem, "produced_by": c_list(c_ident),
        "required": c_list(lambda v: None if isinstance(v, str) and MILESTONE_NAME.match(v)
                           else "must be a milestone name", nonempty=True)}, {}),
    "milestone_reported": ("output_id", {
        "output_id": c_ident, "milestone": c_text, "evidence": c_text,
        "evidence_class": c_enum(REPORTED_EVIDENCE_CLASSES)}, {}),
    "consumer_disposed": ("subject_id", {
        "subject_id": c_ident, "consumer": c_ident, "status": c_enum(CONSUMER_STATUSES),
        "reason": c_text, "evidence": c_list(c_text)}, {"reentry": c_reentry}),
    "round_sealed": ("round_id", {"round_id": c_ident}, {}),
}


def _strings(value: Any) -> Iterator[str]:
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for key, item in value.items():
            yield key
            yield from _strings(item)
    elif isinstance(value, list):
        for item in value:
            yield from _strings(item)


def detail_errors(kind: str, subject: Any, detail: Any) -> list[str]:
    """Kind-specific schema errors of one event, independent of other events."""
    if kind not in KINDS:
        return [f"unknown kind {kind!r}; expected one of {sorted(KINDS)}"]
    subject_field, required, optional = KINDS[kind]
    if not isinstance(detail, dict):
        return ["detail must be an object"]
    errors = []
    missing = set(required) - set(detail)
    extra = set(detail) - set(required) - set(optional)
    if missing:
        errors.append(f"detail is missing {sorted(missing)}")
    if extra:
        errors.append(f"detail has unknown fields {sorted(extra)}")
    for name, checker in list(required.items()) + list(optional.items()):
        if name in detail:
            error = checker(detail[name])
            if error:
                errors.append(f"detail.{name} {error}")
    if detail.get(subject_field) != subject:
        errors.append(f"subject must equal detail.{subject_field}")
    for text in _strings(detail):
        if PRIVATE_PATH.search(text):
            errors.append(f"detail contains a private absolute path: {text[:80]!r}")
            break
    if kind == "component_disposed" and not errors:
        if detail["decision"] in {"taken", "adapted"} and not detail["landed_as"]:
            errors.append("a taken or adapted component must name where it landed")
        if detail["decision"] in {"rejected", "deferred"} and detail["landed_as"]:
            errors.append("a rejected or deferred component has not landed anywhere")
    if kind == "output_declared" and not errors:
        required_names = detail["required"]
        locator = detail["locator"]
        if any(m in DECLARATION_MILESTONES for m in required_names) and "declaration" not in locator:
            errors.append("declaration milestones need locator.declaration")
        if "pr_merged" in required_names and "merge_commit" not in locator:
            errors.append("pr_merged needs locator.merge_commit")
    if kind == "milestone_reported" and detail.get("milestone") in COMPUTED_MILESTONES:
        errors.append(f"{detail['milestone']} is computed from the checkout and cannot be reported")
    if kind == "consumer_disposed" and not errors:
        status = detail["status"]
        if status in {"updated", "verified_unchanged"} and not detail["evidence"]:
            errors.append(f"status {status} needs evidence")
        if status == "deferred" and not detail.get("reentry"):
            errors.append("a deferral needs reentry {owner, trigger}")
        if status != "deferred" and detail.get("reentry") is not None:
            errors.append("reentry belongs only to a deferral")
    return errors


# --------------------------------------------------------------------------
# Reading and verifying the journal.
# --------------------------------------------------------------------------

def read_events(path: Path) -> list[dict[str, Any]]:
    """Parse and structurally verify the journal: lines, canonical form, sequence, chain, hashes."""
    if not path.exists():
        return []
    raw = path.read_bytes()
    if not raw:
        return []
    if not raw.endswith(b"\n"):
        raise RecordError("torn final line: the journal does not end with a newline; "
                          "recover explicitly, never by silent truncation")
    events: list[dict[str, Any]] = []
    previous = ZERO
    for number, line in enumerate(raw.split(b"\n")[:-1]):
        where = f"line {number + 1}"
        if not line:
            raise RecordError(f"{where}: empty line")
        try:
            text = line.decode("utf-8")
            event = json.loads(text)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise RecordError(f"{where}: not valid JSON: {exc}") from exc
        if not isinstance(event, dict) or set(event) != set(EVENT_FIELDS):
            raise RecordError(f"{where}: fields must be exactly {list(EVENT_FIELDS)}")
        if canonical(event) != text:
            raise RecordError(f"{where}: not in canonical form")
        if event["sequence"] != number:
            raise RecordError(f"{where}: sequence {event['sequence']!r}, expected {number}")
        if event["previous"] != previous:
            raise RecordError(f"{where}: previous does not match the prior event_sha")
        body = {k: v for k, v in event.items() if k != "event_sha"}
        if event_hash(body) != event["event_sha"]:
            raise RecordError(f"{where}: event_sha does not match the canonical body")
        previous = event["event_sha"]
        events.append(event)
    return events


class Replay:
    """Fold events into state, collecting schema and reference errors."""

    def __init__(self, root: Path | None = None):
        self.root = root
        self.rounds: dict[str, dict[str, Any]] = {}
        self.returns: dict[str, dict[str, Any]] = {}
        self.outputs: dict[str, dict[str, Any]] = {}
        self.errors: list[str] = []
        self.last_time: str | None = None
        self.count = 0

    def apply(self, event: dict[str, Any]) -> list[str]:
        where = f"event {event.get('sequence')} ({event.get('kind')})"
        errors = [f"{where}: {e}" for e in self._check(event)]
        self.errors.extend(errors)
        self.count += 1
        return errors

    def _check(self, event: dict[str, Any]) -> list[str]:
        kind, subject, detail = event.get("kind"), event.get("subject"), event.get("detail")
        recorded = event.get("recorded_at")
        errors = []
        if not isinstance(recorded, str) or not TIMESTAMP.match(recorded):
            errors.append("recorded_at must be ISO-8601 UTC ending in Z")
        else:
            try:
                dt.datetime.strptime(recorded[:19], "%Y-%m-%dT%H:%M:%S")
            except ValueError:
                errors.append("recorded_at is not a valid date and time")
            if self.last_time is not None and recorded < self.last_time:
                errors.append("recorded_at goes backwards")
            self.last_time = recorded if not errors else self.last_time
        schema = detail_errors(kind, subject, detail)
        if schema:
            return errors + schema
        handler = getattr(self, "_on_" + kind)
        return errors + handler(event["sequence"], detail)

    def _on_round_opened(self, seq: int, d: dict) -> list[str]:
        if d["round_id"] in self.rounds:
            return [f"round {d['round_id']} is already open"]
        self.rounds[d["round_id"]] = {"detail": d, "sealed": False, "returns": [], "opened": seq}
        return []

    def _on_return_received(self, seq: int, d: dict) -> list[str]:
        errors = []
        round_ = self.rounds.get(d["round_id"])
        if round_ is None:
            errors.append(f"round {d['round_id']} was never opened")
        elif round_["sealed"]:
            errors.append(f"round {d['round_id']} is sealed")
        if d["return_id"] in self.returns or d["return_id"] in self.rounds:
            errors.append(f"identifier {d['return_id']} is already used")
        if d["public_copy"] and self.root is not None:
            copy = self.root / d["public_copy"]
            if not copy.is_file():
                errors.append(f"public copy {d['public_copy']} is missing")
            else:
                data = copy.read_bytes()
                if hashlib.sha256(data).hexdigest() != d["sha256"] or len(data) != d["bytes"]:
                    errors.append(f"public copy {d['public_copy']} does not match the recorded hash and size")
        if errors:
            return errors
        round_["returns"].append(d["return_id"])
        self.returns[d["return_id"]] = {"detail": d, "reviews": [], "components": {},
                                        "consumers": {}, "invalidated": []}
        return []

    def _on_review_recorded(self, seq: int, d: dict) -> list[str]:
        state = self.returns.get(d["return_id"])
        if state is None:
            return [f"return {d['return_id']} was never received"]
        # A new review invalidates consumer dispositions recorded under the earlier one.
        state["invalidated"].extend(sorted(state["consumers"]))
        state["consumers"] = {}
        state["reviews"].append(dict(d, sequence=seq))
        return []

    def _on_component_disposed(self, seq: int, d: dict) -> list[str]:
        state = self.returns.get(d["return_id"])
        if state is None:
            return [f"return {d['return_id']} was never received"]
        if not state["reviews"]:
            return [f"return {d['return_id']} must be reviewed before its components are disposed"]
        state["components"][d["component"]] = dict(d, sequence=seq)
        return []

    def _on_output_declared(self, seq: int, d: dict) -> list[str]:
        errors = []
        if d["output_id"] in self.outputs:
            errors.append(f"output {d['output_id']} is already declared; declare a new output id")
        for producer in d["produced_by"]:
            if producer not in self.rounds and producer not in self.returns:
                errors.append(f"producer {producer} is neither a round nor a return")
        if errors:
            return errors
        self.outputs[d["output_id"]] = {"detail": d, "reported": {}, "consumers": {}, "declared": seq}
        return []

    def _on_milestone_reported(self, seq: int, d: dict) -> list[str]:
        state = self.outputs.get(d["output_id"])
        if state is None:
            return [f"output {d['output_id']} was never declared"]
        if d["milestone"] not in state["detail"]["required"]:
            return [f"milestone {d['milestone']} is not required by output {d['output_id']}"]
        state["reported"][d["milestone"]] = dict(d, sequence=seq)
        return []

    def _on_consumer_disposed(self, seq: int, d: dict) -> list[str]:
        subject = d["subject_id"]
        if subject in self.returns:
            state = self.returns[subject]
            if not state["reviews"]:
                return [f"return {subject} must be reviewed before a consumer disposes of it"]
            consumers = self.rounds[state["detail"]["round_id"]]["detail"]["consumers"]
            if d["consumer"] not in consumers:
                return [f"consumer {d['consumer']} was not declared for round {state['detail']['round_id']}"]
            state["consumers"][d["consumer"]] = dict(d, sequence=seq)
            return []
        if subject in self.outputs:
            self.outputs[subject]["consumers"][d["consumer"]] = dict(d, sequence=seq)
            return []
        return [f"subject {subject} is neither a received return nor a declared output"]

    def _on_round_sealed(self, seq: int, d: dict) -> list[str]:
        round_ = self.rounds.get(d["round_id"])
        if round_ is None:
            return [f"round {d['round_id']} was never opened"]
        if round_["sealed"]:
            return [f"round {d['round_id']} is already sealed"]
        round_["sealed"] = True
        return []


def journal_path(root: Path) -> Path:
    return Path(root) / JOURNAL_PATH


def replay(root: Path) -> tuple[list[dict[str, Any]], Replay]:
    events = read_events(journal_path(root))
    state = Replay(Path(root))
    for event in events:
        state.apply(event)
    return events, state


def verify(root: Path) -> dict[str, Any]:
    try:
        events, state = replay(root)
    except RecordError as exc:
        return {"ok": False, "events": None, "head": None, "errors": [str(exc)]}
    return {"ok": not state.errors, "events": len(events),
            "head": events[-1]["event_sha"] if events else ZERO, "errors": state.errors,
            "kinds": dict(sorted(_count(e["kind"] for e in events).items()))}


def _count(values) -> dict[str, int]:
    counts: dict[str, int] = defaultdict(int)
    for v in values:
        counts[v] += 1
    return counts


@contextmanager
def _locked(directory: Path) -> Iterator[None]:
    fd = os.open(directory, os.O_RDONLY)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX)
        yield
    finally:
        fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def append(root: Path, kind: str, subject: str, detail: dict[str, Any],
           recorded_at: str | None = None) -> dict[str, Any]:
    """Validate and append one event; atomic replace under a directory lock."""
    if "CI" in os.environ:
        raise RecordError("appending is refused when CI is set: the record is written by a maintainer, "
                          "then committed and verified")
    path = journal_path(root)
    path.parent.mkdir(parents=True, exist_ok=True)
    with _locked(path.parent):
        events = read_events(path)
        state = Replay(Path(root))
        for event in events:
            state.apply(event)
        if state.errors:
            raise RecordError("the journal does not verify; repair it before appending: "
                              + "; ".join(state.errors[:5]))
        body = {"sequence": len(events), "previous": events[-1]["event_sha"] if events else ZERO,
                "kind": kind, "subject": subject, "detail": detail,
                "recorded_at": recorded_at or utc_now()}
        event = dict(body, event_sha=event_hash(body))
        errors = state.apply(event)
        if errors:
            raise RecordError("; ".join(errors))
        prior = path.read_bytes() if path.exists() else b""
        data = prior + canonical(event).encode("utf-8") + b"\n"
        fd, tmp = tempfile.mkstemp(prefix=".journal-", dir=path.parent)
        try:
            with os.fdopen(fd, "wb") as stream:
                stream.write(data)
                stream.flush()
                os.fsync(stream.fileno())
            os.chmod(tmp, 0o644)
            os.replace(tmp, path)
            dfd = os.open(path.parent, os.O_RDONLY)
            try:
                os.fsync(dfd)
            finally:
                os.close(dfd)
        finally:
            if os.path.exists(tmp):
                os.unlink(tmp)
    return event


# --------------------------------------------------------------------------
# Computed milestones.
# --------------------------------------------------------------------------

COVERAGE_WORKFLOW_PATH = ".github/workflows/lean-coverage-build.yml"
LEAN_IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_'.]+)", re.MULTILINE)


module_id = registry.module_id  # ``lean/A/B.lean``, ``A/B.lean`` or ``A.B`` -> ``A.B``


def compiled_modules(root: Path) -> frozenset[str] | None:
    """The module ids a CI job compiles, or None when that cannot be read.

    The seeds are the default build roots (``module_graph.root`` and
    ``module_graph.additional_roots`` of ``docs/claims.json``, as module ids)
    and the coverage-build targets that ``scripts/coverage_build_targets.py``
    reads from the coverage workflow. The set is everything they reach through
    the ``imports`` edges of ``module_graph.nodes``. The root files are not
    nodes of that graph, so their imports are read from their Lean source.
    """
    root = Path(root)
    claims_path = root / CLAIMS_PATH
    workflow = root / COVERAGE_WORKFLOW_PATH
    if not claims_path.is_file() or not workflow.is_file():
        return None
    try:
        graph = json.loads(claims_path.read_text(encoding="utf-8"))["machine_readable_paper"]["module_graph"]
        nodes = {node["id"]: list(node.get("imports", [])) for node in graph["nodes"]}
        root_paths = [graph["root"], *graph.get("additional_roots", [])]
    except (OSError, ValueError, KeyError, TypeError):
        return None
    try:
        targets = coverage_build_targets.targets(workflow)
    except SystemExit:
        return None
    seeds: list[str] = []
    for path in root_paths:
        mid = module_id(path)
        if mid is None:
            return None
        source = root / registry.normalise_module(path)
        if mid not in nodes:
            if not source.is_file():
                return None
            nodes[mid] = LEAN_IMPORT.findall(source.read_text(encoding="utf-8"))
        seeds.append(mid)
    seeds.extend(targets)
    reached: set[str] = set()
    frontier = list(seeds)
    while frontier:
        current = frontier.pop()
        if current in reached or current not in nodes:
            continue
        reached.add(current)
        frontier.extend(nodes[current])
    return frozenset(reached)


def _milestone(state: str, evidence: Any, milestone: str) -> dict[str, Any]:
    return {"state": state, "source": "computed", "evidence": evidence,
            "evidence_class": MILESTONE_EVIDENCE[milestone]}


class Checkout:
    """Read-only answers about the checkout at ``root``; files are loaded once."""

    def __init__(self, root: Path):
        self.root = Path(root)
        self.source = registry.LeanSource(self.root)
        self._atlas: registry.Atlas | None = None
        self._cache: dict[str, Any] = {}

    def _json(self, relative: str) -> Any:
        if relative not in self._cache:
            path = self.root / relative
            self._cache[relative] = json.loads(path.read_text(encoding="utf-8")) if path.is_file() else None
        return self._cache[relative]

    @property
    def atlas(self) -> registry.Atlas:
        if self._atlas is None:
            self._atlas = registry.Atlas.load(self.root, self.source)
        return self._atlas

    @property
    def compiled(self) -> frozenset[str] | None:
        if "compiled_modules" not in self._cache:
            self._cache["compiled_modules"] = compiled_modules(self.root)
        return self._cache["compiled_modules"]

    def compiled_target(self, module: str | None) -> bool | None:
        compiled = self.compiled
        mid = module_id(module)
        if compiled is None or mid is None:
            return None
        return mid in compiled

    def resolve(self, declaration: str, module: str | None = None) -> dict[str, Any]:
        """Full name, short name and module of a declaration, as far as the checkout tells."""
        key = f"resolve:{declaration}:{module}"
        if key not in self._cache:
            self._cache[key] = self._resolve(declaration, module)
        return self._cache[key]

    def _resolve(self, declaration: str, module: str | None) -> dict[str, Any]:
        module_path = registry.normalise_module(module)
        found = self.atlas.resolve(declaration, module_path)
        full = declaration if "." in declaration else None
        if found["state"] == "found":
            row = found["row"]
            module_path = row["module"]
            if full is None or not found.get("namespace_checked"):
                for decl in self.source.declarations(module_path) or []:
                    if decl["short"] == row["name"] and (full is None or decl["full"] == full):
                        full = decl["full"]
                        break
        elif full is None and module_path:
            for decl in self.source.declarations(module_path) or []:
                if decl["short"] == declaration:
                    full = decl["full"]
                    break
        return {"declaration": declaration, "full_name": full, "short_name": declaration.split(".")[-1],
                "module": module_path, "atlas": found}

    def lean_on_main(self, ref: dict[str, Any]) -> dict[str, Any]:
        found = ref["atlas"]
        if found["state"] == "no_atlas":
            return _milestone("unknown", "docs/declaration_atlas.json is absent", "lean_on_main")
        if found["state"] == "found":
            row = found["row"]
            compiled = self.compiled_target(row.get("module"))
            evidence = {"atlas_id": row.get("id"), "module": row.get("module"), "line": row.get("line"),
                        "atlas_fingerprint": self.atlas.fingerprint, "compiled_target": compiled}
            if compiled is None:
                evidence["reason"] = COMPILED_UNKNOWN
                return _milestone("unknown", evidence, "lean_on_main")
            if not compiled:
                evidence["reason"] = LISTED_NOT_COMPILED
                return _milestone("missing", evidence, "lean_on_main")
            return _milestone("done", evidence, "lean_on_main")
        if found["state"] == "ambiguous":
            return _milestone("unknown", {"ambiguous": found["candidates"]}, "lean_on_main")
        return _milestone("missing", {"searched": ATLAS_NOTE, "module": ref["module"],
                                      "compiled_target": self.compiled_target(ref["module"])},
                          "lean_on_main")

    @staticmethod
    def _names_match(ref: dict[str, Any], name: str, module: str | None) -> bool:
        """A full-name match anywhere, or a namespace-relative match inside the same module."""
        full, short = ref["full_name"], ref["short_name"]
        if full and name == full:
            return True
        if not module or not ref["module"] or registry.normalise_module(module) != ref["module"]:
            return False
        if full:
            return full.endswith("." + name)
        return name == short or name.endswith("." + short)

    def paper_linked(self, ref: dict[str, Any], side: str, milestone: str) -> dict[str, Any]:
        coverage = self._json(COVERAGE_PATH)
        if coverage is None:
            return _milestone("unknown", f"{COVERAGE_PATH} is absent", milestone)
        sides = {p.get("paper_id"): p.get("side") for p in coverage.get("papers", [])}
        rows = []
        for row in coverage.get("rows", []):
            paper_side = sides.get(row.get("paper_id"), row.get("side"))
            if paper_side != side:
                continue
            for decl in (row.get("lean") or {}).get("declarations", []):
                if self._names_match(ref, decl.get("name", ""), decl.get("file")):
                    rows.append(row.get("id"))
                    break
        if rows:
            return _milestone("done", {"rows": sorted(rows)[:10], "row_count": len(rows),
                                       "lean_pin": coverage.get("lean_pin")}, milestone)
        return _milestone("missing", {"searched": f"{COVERAGE_PATH} rows of {side} papers",
                                      "lean_pin": coverage.get("lean_pin")}, milestone)

    def claim_registered(self, ref: dict[str, Any]) -> dict[str, Any]:
        claims = self._json(CLAIMS_PATH)
        if claims is None:
            return _milestone("unknown", f"{CLAIMS_PATH} is absent", "claim_registered")
        hits = []
        for claim in claims.get("claims", []):
            for decl in claim.get("declarations", []) or []:
                if self._names_match(ref, decl.get("name", ""), decl.get("module")):
                    hits.append({"claim": claim.get("id")})
                    break
        packet = claims.get("external_verification_packet") or {}
        for result in packet.get("main_results", []):
            if ref["full_name"] and ref["full_name"] in (result.get("original_declaration"),
                                                         result.get("wrapper_declaration")):
                hits.append({"main_result": result.get("id")})
        if hits:
            return _milestone("done", {"entries": hits}, "claim_registered")
        return _milestone("missing", {"searched": f"{CLAIMS_PATH} claims[].declarations and "
                                                  "external_verification_packet.main_results"},
                          "claim_registered")

    def comparator_listed(self, ref: dict[str, Any]) -> dict[str, Any]:
        base = self.root / VERIFICATION_DIR
        if not base.is_dir():
            return _milestone("unknown", f"{VERIFICATION_DIR}/ is absent", "comparator_listed")
        if not ref["full_name"]:
            return _milestone("unknown", "the full declaration name could not be resolved", "comparator_listed")
        names = {ref["full_name"]}
        claims = self._json(CLAIMS_PATH) or {}
        for result in (claims.get("external_verification_packet") or {}).get("main_results", []):
            if result.get("original_declaration") == ref["full_name"] and result.get("wrapper_declaration"):
                names.add(result["wrapper_declaration"])
        hits = []
        for path in sorted(base.glob("*.json")):
            # Negative configurations exist to be rejected; a name there queues nothing.
            if "negative" in path.name:
                continue
            try:
                config = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                continue
            listed = config.get("theorem_names") if isinstance(config, dict) else None
            if not isinstance(listed, list):
                continue
            for name in sorted(names & set(listed)):
                hits.append({"config": path.relative_to(self.root).as_posix(), "name": name,
                             "via_wrapper": name != ref["full_name"]})
        if hits:
            return _milestone("done", {"entries": hits}, "comparator_listed")
        return _milestone("missing", {"searched": f"{VERIFICATION_DIR}/*.json theorem_names",
                                      "names": sorted(names)}, "comparator_listed")

    def pr_merged(self, locator: dict[str, Any]) -> dict[str, Any]:
        commit = locator.get("merge_commit")
        if not isinstance(commit, str) or not COMMIT.match(commit):
            return _milestone("unknown", "no valid locator.merge_commit", "pr_merged")
        try:
            result = subprocess.run(["git", "-C", str(self.root), "merge-base", "--is-ancestor", commit, "HEAD"],
                                    capture_output=True, text=True, timeout=60, check=False)
        except (OSError, subprocess.SubprocessError) as exc:
            return _milestone("unknown", f"git unavailable: {exc}", "pr_merged")
        evidence = {"merge_commit": commit, "against": "HEAD"}
        if result.returncode == 0:
            return _milestone("done", evidence, "pr_merged")
        if result.returncode == 1:
            return _milestone("missing", evidence, "pr_merged")
        return _milestone("unknown", dict(evidence, git=result.stderr.strip()[:200]), "pr_merged")

    def declaration_milestones(self, declaration: str, module: str | None = None,
                               names: tuple[str, ...] = DECLARATION_MILESTONES) -> dict[str, Any]:
        ref = self.resolve(declaration, module)
        out: dict[str, Any] = {}
        for name in names:
            if name == "lean_on_main":
                out[name] = self.lean_on_main(ref)
            elif name == "short_paper_linked":
                out[name] = self.paper_linked(ref, "short", name)
            elif name == "long_record_linked":
                out[name] = self.paper_linked(ref, "long", name)
            elif name == "claim_registered":
                out[name] = self.claim_registered(ref)
            elif name == "comparator_listed":
                out[name] = self.comparator_listed(ref)
        public_ref = {k: v for k, v in ref.items() if k != "atlas"}
        public_ref["atlas_state"] = ref["atlas"]["state"]
        return {"declaration": public_ref, "milestones": out}

    def compute(self, milestone: str, locator: dict[str, Any]) -> dict[str, Any]:
        if milestone == "pr_merged":
            return self.pr_merged(locator)
        if "declaration" not in locator:
            return _milestone("unknown", "no locator.declaration", milestone)
        return self.declaration_milestones(locator["declaration"], locator.get("module"),
                                           (milestone,))["milestones"][milestone]


ATLAS_NOTE = "docs/declaration_atlas.json declarations"
LISTED_NOT_COMPILED = ("listed in the declaration atlas, but no default build root or coverage-build "
                       "target reaches its module")
COMPILED_UNKNOWN = ("the compiled module set could not be read (docs/claims.json module_graph or "
                    f"{COVERAGE_WORKFLOW_PATH})")


# --------------------------------------------------------------------------
# Status projection.
# --------------------------------------------------------------------------

def status(root: Path, round_id: str | None = None, checkout: Checkout | None = None) -> dict[str, Any]:
    root = Path(root)
    events, state = replay(root)
    checkout = checkout or Checkout(root)

    outputs: dict[str, dict[str, Any]] = {}
    for oid, o in state.outputs.items():
        d = o["detail"]
        milestones = {}
        for name in d["required"]:
            if name in COMPUTED_MILESTONES:
                milestones[name] = checkout.compute(name, d["locator"])
            elif name in o["reported"]:
                r = o["reported"][name]
                milestones[name] = {"state": "done", "source": "reported", "evidence": r["evidence"],
                                    "evidence_class": r["evidence_class"]}
            else:
                milestones[name] = {"state": "missing", "source": "reported", "evidence": None,
                                    "evidence_class": None}
        missing = [m for m in d["required"] if milestones[m]["state"] == "missing"]
        unknown = [m for m in d["required"] if milestones[m]["state"] == "unknown"]
        outputs[oid] = {"kind": d["kind"], "locator": d["locator"], "problem": d["problem"],
                        "produced_by": d["produced_by"], "required": d["required"],
                        "milestones": milestones, "missing": missing, "unknown": unknown,
                        "complete": not missing and not unknown,
                        "consumers": {c: _consumer_view(v) for c, v in sorted(o["consumers"].items())}}

    produced: dict[str, list[str]] = defaultdict(list)
    for oid, o in outputs.items():
        for producer in o["produced_by"]:
            produced[producer].append(oid)

    returns: dict[str, dict[str, Any]] = {}
    deferred: list[dict[str, Any]] = []
    for rid, r in state.returns.items():
        d = r["detail"]
        review = r["reviews"][-1] if r["reviews"] else None
        consumers_declared = state.rounds[d["round_id"]]["detail"]["consumers"]
        components = {c: {"decision": v["decision"], "reason": v["reason"], "landed_as": v["landed_as"]}
                      for c, v in sorted(r["components"].items())}
        decisions = dict(sorted(_count(v["decision"] for v in r["components"].values()).items()))
        missing_consumers = sorted(set(consumers_declared) - set(r["consumers"]))
        deferred_consumers = sorted(c for c, v in r["consumers"].items() if v["status"] == "deferred")
        own_outputs = sorted(produced.get(rid, []))
        incomplete_outputs = [o for o in own_outputs if not outputs[o]["complete"]]
        outstanding: list[str] = []
        if review is None:
            phase = "custodied"
            outstanding.append("review_pending")
        elif review["disposition"] == "repair_required":
            phase = "repair_required"
            outstanding.append("repair_required")
        elif review["disposition"] in CLOSED_WITHOUT_INTEGRATION:
            phase = "closed_without_integration"
        else:
            outstanding.extend(f"consumer_missing:{c}" for c in missing_consumers)
            if not r["components"]:
                outstanding.append("component_ledger_empty")
            outstanding.extend(f"output_incomplete:{o}" for o in incomplete_outputs)
            phase = ("dispositions_incomplete" if missing_consumers or not r["components"] else
                     "outputs_incomplete" if incomplete_outputs else
                     "suspended_with_reentry" if deferred_consumers else "complete")
        for c in deferred_consumers:
            v = r["consumers"][c]
            deferred.append({"subject_id": rid, "consumer": c, "owner": v["reentry"]["owner"],
                             "trigger": v["reentry"]["trigger"], "reason": v["reason"]})
        for c, v in sorted(r["components"].items()):
            if v["decision"] == "deferred":
                deferred.append({"subject_id": rid, "component": c, "owner": None, "trigger": None,
                                 "reason": v["reason"]})
        returns[rid] = {
            "round_id": d["round_id"], "sha256": d["sha256"], "bytes": d["bytes"],
            "media_type": d["media_type"], "custody": d["custody"], "public_copy": d["public_copy"],
            "review": None if review is None else {k: review[k] for k in ("disposition", "rationale", "reviewer")},
            "reviews_recorded": len(r["reviews"]),
            "dispositions_invalidated_by_later_review": r["invalidated"],
            "components": components, "component_decisions": decisions,
            "consumers": {c: _consumer_view(v) for c, v in sorted(r["consumers"].items())},
            "missing_consumers": missing_consumers if review and review["disposition"] == "admitted_for_integration" else [],
            "outputs": own_outputs, "phase": phase, "outstanding": outstanding,
        }
    for oid, o in outputs.items():
        for c, v in o["consumers"].items():
            if v["status"] == "deferred":
                deferred.append({"subject_id": oid, "consumer": c, "owner": v["reentry"]["owner"],
                                 "trigger": v["reentry"]["trigger"], "reason": v["reason"]})

    rounds: dict[str, dict[str, Any]] = {}
    for key, r in state.rounds.items():
        d = r["detail"]
        arrivals = len(r["returns"])
        expected = d["expected_returns"]
        owed_returns = sorted(x for x in r["returns"] if returns[x]["outstanding"])
        own_outputs = sorted(set(produced.get(key, [])))
        incomplete = [o for o in own_outputs if not outputs[o]["complete"]]
        outstanding = []
        if not r["sealed"]:
            outstanding.append("unsealed")
        if expected is not None and arrivals != expected:
            outstanding.append(f"arrivals:{arrivals}_of_{expected}")
        outstanding.extend(f"return:{x}" for x in owed_returns)
        outstanding.extend(f"output_incomplete:{o}" for o in incomplete)
        rounds[key] = {"packet_id": d["packet_id"], "packet_manifest_sha256": d["packet_manifest_sha256"],
                       "source_commit": d["source_commit"], "ask": d["ask"], "consumers": d["consumers"],
                       "expected_returns": expected, "arrivals": arrivals, "sealed": r["sealed"],
                       "returns": sorted(r["returns"]), "outputs": own_outputs,
                       "outstanding": outstanding, "complete": not outstanding}

    orphans = {
        "outputs_without_producer": sorted(o for o, v in outputs.items() if not v["produced_by"]),
        "admitted_returns_without_landing": sorted(
            rid for rid, r in returns.items()
            if r["review"] and r["review"]["disposition"] == "admitted_for_integration"
            and not r["outputs"]
            and not any(c["decision"] in {"taken", "adapted"} for c in r["components"].values())),
    }

    if round_id is not None:
        if round_id not in rounds:
            raise RecordError(f"unknown round {round_id!r}")
        keep_returns = set(rounds[round_id]["returns"])
        keep_outputs = {o for o, v in outputs.items()
                        if round_id in v["produced_by"] or keep_returns & set(v["produced_by"])}
        rounds = {round_id: rounds[round_id]}
        returns = {k: v for k, v in returns.items() if k in keep_returns}
        outputs = {k: v for k, v in outputs.items() if k in keep_outputs}
        deferred = [x for x in deferred if x["subject_id"] in keep_returns | keep_outputs]
        orphans = {k: [x for x in v if x in keep_returns | keep_outputs] for k, v in orphans.items()}

    head = events[-1]["event_sha"] if events else ZERO
    return {
        "schema": "plectis-research-record-status/1",
        "journal": {"path": JOURNAL_PATH, "events": len(events), "head": head,
                    "errors": state.errors},
        "rounds": dict(sorted(rounds.items())),
        "returns": dict(sorted(returns.items())),
        "outputs": dict(sorted(outputs.items())),
        "deferred": sorted(deferred, key=lambda x: (x["subject_id"], x.get("consumer") or x.get("component"))),
        "orphans": orphans,
        "evidence_boundary": ("Computed milestones read the checkout; each states its evidence class. "
                              "lean_on_main needs a declaration_atlas_at_pin listing and a compiled "
                              "target: the atlas is a navigation projection and a listing alone does not "
                              "show the module was compiled. Reported milestones, reviews and "
                              "dispositions are recorded decisions and confer no kernel authority."),
    }


def _consumer_view(v: dict[str, Any]) -> dict[str, Any]:
    return {"status": v["status"], "reason": v["reason"], "evidence": v["evidence"],
            "reentry": v.get("reentry")}


def render_markdown(report: dict[str, Any]) -> str:
    lines = ["# Research record status", ""]
    j = report["journal"]
    lines.append(f"Journal `{j['path']}`: {j['events']} events, head `{j['head'][:12]}`.")
    if j["errors"]:
        lines.append(f"Journal errors: {len(j['errors'])}.")
    lines.append("")
    lines.append("## Rounds")
    lines.append("")
    if not report["rounds"]:
        lines.append("No rounds recorded.")
    for rid, r in report["rounds"].items():
        state = "complete" if r["complete"] else "owes " + ", ".join(r["outstanding"])
        noun = "arrival" if r["arrivals"] == 1 else "arrivals"
        lines.append(f"- `{rid}` (packet `{r['packet_id']}`, {r['arrivals']} {noun}, "
                     f"{'sealed' if r['sealed'] else 'open'}): {state}")
    lines += ["", "## Returns", ""]
    if not report["returns"]:
        lines.append("No returns recorded.")
    for rid, r in report["returns"].items():
        review = r["review"]["disposition"] if r["review"] else "not reviewed"
        owed = ", ".join(r["outstanding"]) or "nothing"
        lines.append(f"- `{rid}` in `{r['round_id']}`: {review}; phase {r['phase']}; owes {owed}")
    lines += ["", "## Outputs", ""]
    if not report["outputs"]:
        lines += ["No outputs declared.", ""]
    for oid, o in report["outputs"].items():
        lines.append(f"### `{oid}`")
        lines.append("")
        where = o["locator"].get("declaration") or o["locator"].get("path") or o["locator"].get("pr")
        lines.append(f"Kind {o['kind']}, locator `{where}`.")
        lines.append("")
        for name in o["required"]:
            m = o["milestones"][name]
            lines.append(f"- {name}: {m['state']} ({m['source']}, {m['evidence_class'] or 'no evidence'})")
        lines.append("")
        lines.append("Still missing: " + (", ".join(o["missing"]) or "none") +
                     ("; unknown: " + ", ".join(o["unknown"]) if o["unknown"] else "") + ".")
        lines.append("")
    lines += ["## Deferred", ""]
    if not report["deferred"]:
        lines.append("Nothing deferred.")
    for x in report["deferred"]:
        item = x.get("consumer") or x.get("component")
        lines.append(f"- `{x['subject_id']}` / {item}: owner {x['owner']}, trigger {x['trigger']}")
    lines += ["", "## Orphans", ""]
    for key, values in report["orphans"].items():
        lines.append(f"- {key}: " + (", ".join(f"`{v}`" for v in values) or "none"))
    lines += ["", report["evidence_boundary"], ""]
    return "\n".join(lines)


# --------------------------------------------------------------------------
# CLI.
# --------------------------------------------------------------------------

def _print_json(value: Any) -> None:
    sys.stdout.write(json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="The research record of rounds, returns and outputs, and what each still owes. "
                    "Computed milestones read the checkout and state their evidence class; lean_on_main "
                    "needs an atlas listing and a compiled target. The journal itself confers no kernel "
                    "authority.")
    parser.add_argument("--root", type=Path, default=ROOT, help="checkout root (default: this repository)")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("verify", help="check the journal chain, hashes, schema and references")
    p = sub.add_parser("status", help="project rounds, returns, outputs, deferrals and orphans")
    p.add_argument("--format", choices=("json", "md"), default="json")
    p.add_argument("--round", dest="round_id", default=None)
    p = sub.add_parser("milestones", help="computed milestones for one declaration")
    p.add_argument("--declaration", required=True)
    p.add_argument("--module", default=None)
    p = sub.add_parser("append", help="append one event (refused when CI is set)")
    p.add_argument("kind", choices=sorted(KINDS))
    p.add_argument("--subject", required=True)
    p.add_argument("--detail-json", required=True)
    p.add_argument("--recorded-at", default=None, help="UTC time ending in Z (default: now)")
    args = parser.parse_args(argv)
    try:
        if args.command == "verify":
            report = verify(args.root)
            _print_json(report)
            return 0 if report["ok"] else 1
        if args.command == "status":
            report = status(args.root, args.round_id)
            if args.format == "md":
                sys.stdout.write(render_markdown(report))
            else:
                _print_json(report)
            return 0 if not report["journal"]["errors"] else 1
        if args.command == "milestones":
            result = Checkout(args.root).declaration_milestones(args.declaration, args.module)
            result["missing"] = [k for k, v in result["milestones"].items() if v["state"] == "missing"]
            result["unknown"] = [k for k, v in result["milestones"].items() if v["state"] == "unknown"]
            _print_json(result)
            return 0
        try:
            detail = json.loads(args.detail_json)
        except json.JSONDecodeError as exc:
            raise RecordError(f"--detail-json is not valid JSON: {exc}") from exc
        _print_json(append(args.root, args.kind, args.subject, detail, args.recorded_at))
        return 0
    except RecordError as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
