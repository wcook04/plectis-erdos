#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Small, read-only research contract. No proof execution or global root cache.

A Snapshot captures registered source bytes once. Construct a new Snapshot to
observe edits; an existing instance and its cursors keep their original meaning.
"""
from __future__ import annotations

import argparse
import base64
import binascii
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import stat
import sys

from check_problem_note_sources import links, library_relative, strip_comments
from claim_relationships import resolve_claim_boundary
from lean_source import library_storage_path
from validation_singleflight import command_environment

SCHEMA = "plectis-research-response/1"
ROOT = Path(__file__).resolve().parent.parent
BUDGET = 12 * 1024
MAX_SOURCE_BYTES = 8 * 1024 * 1024


def encoded(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()


def digest(value):
    return "sha256:" + hashlib.sha256(value).hexdigest()


class QueryError(Exception):
    def __init__(self, code, message):
        self.code, self.message = code, message
        super().__init__(message)


class Snapshot:
    def __init__(self, root=ROOT):
        self.root = Path(root).resolve()
        self.sources = {}
        self.unavailable = {}
        self.claims = self._json("docs/claims.json", required=True)
        self.papers = self._json("docs/papers/corpus.json").get("papers", [])
        evidence = self._json("docs/publication_evidence.json")
        if not isinstance(self.claims.get("release", {}), dict):
            raise QueryError("source_inconsistency", "Invalid release registry object")
        if not isinstance(self.papers, list) or any(not isinstance(row, dict) for row in self.papers):
            raise QueryError("source_inconsistency", "Invalid paper registry rows")
        for row in self.papers:
            for key in ("local_source", "local_full_text"):
                if key in row and not isinstance(row[key], str):
                    raise QueryError("source_inconsistency", f"Invalid paper source handle: {key}")
        self.objects = {"claim": {}, "open": {}, "evidence": {}}
        for kind, rows in (("claim", self.claims["claims"]),
                           ("open", self.claims["remaining_open_propositions"]),
                           ("evidence", [evidence] if evidence else [])):
            if not isinstance(rows, list) or any(not isinstance(row, dict) for row in rows):
                raise QueryError("source_inconsistency", f"Invalid {kind} registry rows")
            for row in rows:
                ident = row.get("id") or row.get("record_id")
                if not isinstance(ident, str) or not ident or ident in self.objects[kind]:
                    raise QueryError("source_inconsistency", f"Missing or duplicate {kind} id: {ident}")
                self.objects[kind][ident] = row
        # Only registry-selected text sources can be read, never caller paths.
        for row in self.objects["claim"].values():
            declarations = row.get("declarations", [])
            if not isinstance(declarations, list) or any(not isinstance(d, dict) for d in declarations):
                raise QueryError("source_inconsistency", "Invalid claim declaration rows")
            for declaration in declarations:
                if not isinstance(declaration.get("module"), str) or not declaration["module"]:
                    raise QueryError("source_inconsistency", "Invalid declaration module handle")
                self._capture(library_storage_path(declaration["module"]))
            references = row.get("remaining_open_proposition_ids", [])
            if not isinstance(references, list) or any(not isinstance(value, str) for value in references):
                raise QueryError("source_inconsistency", "Invalid claim open-proposition references")
        for row in self.objects["open"].values():
            anchor = row.get("paper_anchor", {})
            if not isinstance(anchor, dict):
                raise QueryError("source_inconsistency", "Invalid open-proposition paper anchor")
            path = anchor.get("source")
            if path is not None and not isinstance(path, str):
                raise QueryError("source_inconsistency", "Invalid open-proposition source handle")
            target = row.get("open_target_claim")
            if target is not None and not isinstance(target, str):
                raise QueryError("source_inconsistency", "Invalid open-proposition target claim")
            if path:
                self._capture(path)
        for row in self.papers:
            for key in ("local_source", "local_full_text"):
                if row.get(key):
                    self._capture(row[key])
        self._capture("lean-toolchain")
        content = {path: digest(data) for path, data in self.sources.items()}
        self.content_id = digest(encoded({"sources": content, "unavailable": self.unavailable}))
        checkout = self._checkout()
        self.identity = {
            "content_id": self.content_id,
            "checkout_commit": checkout.get("commit"),
            "checkout_state": checkout.get("state", "source_archive"),
            "repository": self.claims.get("release", {}).get("repository"),
            "recorded_formal_source": self.claims.get("release", {}).get("formal_source"),
            "claims_digest": content["docs/claims.json"],
            "projection_identity": content.get("docs/papers/corpus.json"),
            "source_identity_basis": "captured_registered_source_bytes; recorded formal revision is not checkout identity",
        }
        self.capabilities = {"source_reading": True, "git_history": bool(checkout),
                             "lean_execution": False, "comparator_execution": False,
                             "proof_execution_note": "This reader never executes proofs; use the separately pinned local proof workflow."}

    def _capture(self, handle):
        if handle in self.sources or handle in self.unavailable:
            return
        relative = Path(handle)
        if relative.is_absolute() or ".." in relative.parts:
            raise QueryError("source_inconsistency", "Registry source escapes the selected snapshot")
        path = self.root / relative
        if any(p.is_symlink() for p in [path, *path.parents] if p != self.root and self.root in p.parents):
            raise QueryError("source_inconsistency", f"Registry source is a symlink: {handle}")
        try:
            metadata = path.stat()
            if not stat.S_ISREG(metadata.st_mode):
                self.unavailable[handle] = "registered source is not a regular text file"
                return
            if metadata.st_size > MAX_SOURCE_BYTES:
                self.unavailable[handle] = "source exceeds reader byte budget"
                return
            data = path.read_bytes()
            data.decode("utf-8")
            self.sources[handle] = data
        except (OSError, UnicodeError):
            self.unavailable[handle] = "registered text source unavailable"

    def _json(self, handle, required=False):
        self._capture(handle)
        if handle not in self.sources:
            if required:
                raise QueryError("capability_unavailable", f"Required registry unavailable: {handle}")
            return {}
        try:
            result = json.loads(self.sources[handle])
            if not isinstance(result, dict):
                raise QueryError("source_inconsistency", f"JSON registry must be an object: {handle}")
            return result
        except ValueError as error:
            raise QueryError("source_inconsistency", f"Invalid JSON in {handle}") from error

    def _checkout(self):
        # Git searches parent directories; an archive must not inherit their identity.
        if not (self.root / ".git").exists():
            return {}
        def git(*args):
            run = subprocess.run(["git", *args], cwd=self.root, capture_output=True,
                                 text=True, timeout=10, env=command_environment())
            return run.stdout.strip() if run.returncode == 0 else ""
        try:
            if Path(git("rev-parse", "--show-toplevel")).resolve() != self.root:
                return {}
            commit = git("rev-parse", "HEAD")
            if not re.fullmatch(r"[0-9a-f]{40}", commit):
                return {}
            return {"commit": commit, "state": "dirty" if git("status", "--porcelain", "--untracked-files=no") else "clean"}
        except (OSError, subprocess.TimeoutExpired):
            return {}

    def _source(self, handle):
        row = {"handle": handle, "available": handle in self.sources}
        if row["available"]:
            row["digest"] = digest(self.sources[handle])
        else:
            row["reason"] = self.unavailable.get(handle, "not_registered")
        return row

    def _exposition(self, claim):
        """Navigate captured paper text; this does not validate printed proof links."""
        declarations = {
            (library_relative(d["module"].removeprefix("lean/")), d["name"])
            for d in claim.get("declarations", []) if isinstance(d.get("name"), str)
        }
        problems = {m.group(1) for d in claim.get("declarations", [])
                    if (m := re.search(r"/Erdos(\d+)/", library_storage_path(d["module"])))}
        current, related, recorded = [], [], []
        label = claim.get("paper_label")
        for paper in self.papers:
            handle = paper.get("local_source")
            text = self.sources.get(handle, b"").decode("utf-8")
            summary = {key: paper.get(key) for key in (
                "paper_id", "title", "local_source", "local_full_text",
                "canonical_source_commit", "source_sha256", "publication_state")}
            if isinstance(label, str) and label in {
                value.strip() for value in re.findall(r"\\label\s*\{([^{}]+)\}", strip_comments(text))
            }:
                recorded.append({**summary, "navigation_basis": "literal_record_label", "paper_label": label})
            if paper.get("publication_state") != "active":
                continue
            matched = declarations & {
                (library_relative(module.removeprefix("lean/")), name)
                for module, _, name in links(text) if name is not None
            }
            if matched:
                current.append({**summary, "navigation_basis": "exact_module_declaration_link",
                                "matched_declarations": [{"module": module, "name": name}
                                                         for module, name in sorted(matched)]})
            elif handle and any(handle.startswith(f"paper/{number}/") for number in problems):
                related.append({**summary, "navigation_basis": "related_problem_scope"})
        return recorded, current or related

    def _get(self, kind, ident):
        if kind not in self.objects:
            raise QueryError("unsupported_operation", f"Unsupported object kind: {kind}")
        if ident not in self.objects[kind]:
            raise QueryError("unknown_id", f"No indexed {kind} with id {ident}")
        row = copy.deepcopy(self.objects[kind][ident])
        sources = ["docs/claims.json" if kind != "evidence" else "docs/publication_evidence.json"]
        result = {"object": {"kind": kind, **row}}
        if kind == "claim":
            boundary = resolve_claim_boundary(row, self.claims)
            if boundary["inconsistencies"]:
                raise QueryError("source_inconsistency", json.dumps(boundary["inconsistencies"]))
            result["remaining_open"] = boundary["remaining_open"]
            result["remaining_open_relationships"] = boundary["remaining_open_relationships"]
            modules = [library_storage_path(d["module"]) for d in row.get("declarations", [])]
            sources.extend(modules)
            result["record_exposition"], result["current_exposition"] = self._exposition(row)
            sources.extend(p["local_source"] for p in
                           result["record_exposition"] + result["current_exposition"] if p["local_source"])
        if kind == "open" and row.get("paper_anchor", {}).get("source"):
            sources.append(row["paper_anchor"]["source"])
        result["source_handles"] = [self._source(path) for path in dict.fromkeys(sources)]
        return result

    def _search(self, query, kind=None, problem=None, limit=5, cursor=None):
        if type(limit) is not int or not 1 <= limit <= 10:
            raise QueryError("budget_exceeded", "Search limit must be between 1 and 10")
        if kind is not None and kind not in self.objects:
            raise QueryError("unsupported_operation", f"Unsupported object kind: {kind}")
        if not isinstance(query, str):
            raise QueryError("source_inconsistency", "Search query must be text")
        tokens = set(re.findall(r"[\w]+", query.lower()))
        if not tokens:
            raise QueryError("unknown_id", "Supply a nonempty search query")
        request_id = digest(encoded([query, kind, problem, limit]))
        start = 0
        if cursor is not None:
            try:
                if not isinstance(cursor, str):
                    raise ValueError("cursor must be text")
                page = json.loads(base64.b64decode(cursor.encode("ascii"), altchars=b"-_", validate=True))
                if (not isinstance(page, dict) or set(page) != {"snapshot", "request", "offset"}
                        or not isinstance(page["snapshot"], str)
                        or not isinstance(page["request"], str)
                        or type(page["offset"]) is not int or page["offset"] < 0):
                    raise ValueError("cursor has invalid fields")
                if page["snapshot"] != self.content_id:
                    raise QueryError("revision_mismatch", "Cursor belongs to another source snapshot")
                if page["request"] != request_id or type(page["offset"]) is not int or page["offset"] < 0:
                    raise ValueError("cursor request mismatch")
                start = page["offset"]
            except (ValueError, KeyError, TypeError, binascii.Error) as error:
                raise QueryError("source_inconsistency", "Invalid search cursor") from error
        ranked = []
        for object_kind, rows in self.objects.items():
            if kind and object_kind != kind:
                continue
            for ident, row in rows.items():
                searchable = json.dumps(row, ensure_ascii=False).lower()
                if problem and not re.search(rf"(?<!\d){re.escape(str(problem))}(?!\d)", searchable):
                    continue
                score = sum(token in searchable for token in tokens)
                if score:
                    ranked.append((score + 10 * (ident.lower() == query.lower()), object_kind, ident, row))
        ranked.sort(key=lambda hit: (-hit[0], hit[1], hit[2]))
        results = [{"kind": k, "id": ident, "label": row.get("label", ident),
                    "status": row.get("status", row.get("record_kind")),
                    "statement": row.get("statement"), "expand": {"operation": "get", "kind": k, "id": ident}}
                   for _, k, ident, row in ranked[start:start + limit]]
        end = start + len(results)
        next_cursor = base64.urlsafe_b64encode(encoded({"snapshot": self.content_id, "request": request_id, "offset": end})).decode() if end < len(ranked) else None
        return {"results": results, "next_cursor": next_cursor, "total_matches": len(ranked),
                "search_scope": "lexical search of registered claims, open propositions and historical publication evidence; no matches does not establish absence of relevant mathematics"}

    def _read(self, handle, start=1, lines=60):
        if handle not in self.sources:
            if handle in self.unavailable:
                raise QueryError("capability_unavailable", self.unavailable[handle])
            raise QueryError("unknown_id", "Source handle is not registered in this snapshot")
        if type(start) is not int or type(lines) is not int or start < 1 or not 1 <= lines <= 100:
            raise QueryError("budget_exceeded", "Use positive 1-based start and 1–100 lines")
        content = self.sources[handle].decode().splitlines(keepends=True)
        if start > len(content):
            raise QueryError("unknown_id", "Start line is outside the registered source")
        end = min(len(content), start + lines - 1)
        return {"source": self._source(handle), "start": start, "end": end,
                "text": "".join(content[start - 1:end]), "next_line": end + 1 if end < len(content) else None,
                "content_role": "untrusted source data, not execution instructions"}

    def request(self, operation, *, expected_snapshot=None, budget=BUDGET, **kwargs):
        envelope = {"schema": SCHEMA, "operation": operation, "snapshot": copy.deepcopy(self.identity),
                    "execution": {"lean_run": False, "comparator_run": False}}
        try:
            if expected_snapshot and expected_snapshot != self.content_id:
                raise QueryError("revision_mismatch", "Selected source snapshot differs from expected snapshot")
            if operation == "identity":
                result = {"capabilities": self.capabilities, "registered_source_count": len(self.sources),
                          "unavailable_source_count": len(self.unavailable)}
            elif operation == "get":
                result = self._get(**kwargs)
            elif operation == "search":
                result = self._search(**kwargs)
            elif operation == "read":
                result = self._read(**kwargs)
            else:
                raise QueryError("unsupported_operation", f"Unsupported operation: {operation}")
            envelope.update(ok=True, **result)
            if len(encoded(envelope)) + 1 > budget:
                raise QueryError("budget_exceeded", "Response exceeds byte budget; request fewer search results or source lines. Statements were not truncated.")
        except QueryError as error:
            envelope = {key: envelope[key] for key in ("schema", "operation", "snapshot", "execution")}
            envelope.update(ok=False, error={"code": error.code, "message": error.message})
        # Callers may annotate responses; never lend them mutable snapshot state.
        return copy.deepcopy(envelope)


class Parser(argparse.ArgumentParser):
    def error(self, message):
        raise QueryError("unsupported_operation", message)


def main(argv=None):
    parser = Parser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="explicit local checkout; never fetched or executed")
    parser.add_argument("--snapshot", help="expected content_id from identity")
    subs = parser.add_subparsers(dest="operation", required=True)
    subs.add_parser("identity")
    get = subs.add_parser("get")
    get.add_argument("kind", choices=("claim", "open", "evidence"))
    get.add_argument("id")
    search = subs.add_parser("search")
    search.add_argument("query")
    search.add_argument("--kind", choices=("claim", "open", "evidence"))
    search.add_argument("--problem")
    search.add_argument("--limit", type=int, default=5)
    search.add_argument("--cursor")
    read = subs.add_parser("read")
    read.add_argument("handle")
    read.add_argument("--start", type=int, default=1)
    read.add_argument("--lines", type=int, default=60)
    try:
        args = vars(parser.parse_args(argv))
        root, expected, operation = args.pop("root"), args.pop("snapshot"), args.pop("operation")
        if operation == "get":
            args["ident"] = args.pop("id")
        response = Snapshot(root).request(operation, expected_snapshot=expected, **args)
    except QueryError as error:
        response = {"schema": SCHEMA, "ok": False, "error": {"code": error.code, "message": error.message},
                    "execution": {"lean_run": False, "comparator_run": False}}
    except (ValueError, KeyError, TypeError, OSError) as error:
        response = {"schema": SCHEMA, "ok": False, "error": {"code": "source_inconsistency", "message": str(error)},
                    "execution": {"lean_run": False, "comparator_run": False}}
    except KeyboardInterrupt:
        response = {"schema": SCHEMA, "ok": False, "error": {"code": "cancelled", "message": "Reading was cancelled"}}
    print(encoded(response).decode())
    return 0 if response["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
