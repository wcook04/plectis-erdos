#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Source-bound corpus queries and the complete registered-claim projection.

A disposable, source-bound SQLite read model. This is NOT another claim registry,
proof engine or research journal. Native owners remain authoritative. In
particular, existing relation-row endpoint text is never an inference edge.

Python >= 3.10; standard library plus the repository's existing owners.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import importlib
import json
import os
from pathlib import Path
import re
import sqlite3
import sys
import tempfile
from typing import Any

SCHEMA = "plectis-corpus-substrate/1"
DEFAULT_DB = ".lake/research/corpus_substrate.sqlite"
OWNER = {
    "claim": "docs/claims.json",
    "problem": "docs/problems.json",
    "declaration": "docs/declaration_atlas.json",
    "dependency": "docs/lean_dependency_index.json",
    "paper_result": "docs/paper_lean_coverage.json",
    "relation": "docs/research-commons/record/relations.json",
    "contrast": "docs/research-commons/record/contrasts.json",
    "event": "docs/research-commons/record/journal.jsonl",
    "route": "research/experiments/replay_worlds/routes.json",
}
BOUNDARY = (
    "Generated navigation over pinned owner bytes, not a new mathematical authority. "
    "Status strings are owner-reported, compilation is not replayed here, dependencies "
    "are not implications, and unbound relation text is excluded from inference."
)
INPUT_DIRS = ("lean", "paper", "scripts", "docs", "research", "verification", "computations", ".github/workflows")
INPUT_SUFFIXES = {".lean", ".py", ".json", ".jsonl", ".gz", ".md", ".tex", ".bib", ".toml", ".yml", ".yaml", ".txt", ".sh"}
GENERATED_FILES = {"docs/reference/CORPUS_REGISTER.md"}
INPUT_FILES = ("lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json", "AGENTS.md", "README.md")


class SubstrateError(ValueError):
    pass


def canonical(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False)


def digest(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def _pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise SubstrateError(f"duplicate JSON key: {k}")
        out[k] = v
    return out


def decode(data: bytes) -> Any:
    def reject(token: str) -> None:
        raise SubstrateError(f"non-finite JSON number: {token}")
    return json.loads(data, object_pairs_hook=_pairs, parse_constant=reject)


def safe_file(root: Path, relative: str) -> Path:
    part = Path(relative)
    if part.is_absolute() or ".." in part.parts:
        raise SubstrateError(f"unsafe source path: {relative}")
    root = root.resolve()
    current = root
    for component in part.parts:
        current = current / component
        if current.is_symlink():
            raise SubstrateError(f"symlink source: {relative}")
    if not current.is_file():
        raise SubstrateError(f"missing regular source: {relative}")
    return current


def input_paths(root: Path) -> list[str]:
    """Coarse initial invalidation frontier; generated SQLite stays outside it.

    Omit no existing input on permission errors. Exclude .lake and nested .git
    intentionally. This enumerates supported source families, not a live Git tree.
    """
    paths = set()
    for folder in INPUT_DIRS:
        base = root / folder
        if not base.exists():
            continue
        if base.is_symlink():
            raise SubstrateError(f"symlink source directory: {folder}")
        def onerror(exc: OSError) -> None:
            raise exc
        for directory, dirs, names in os.walk(base, onerror=onerror, followlinks=False):
            dirs[:] = sorted(d for d in dirs if d not in {".lake", ".git", "__pycache__"})
            for d in dirs:
                if (Path(directory) / d).is_symlink():
                    raise SubstrateError(f"symlink source directory: {directory}/{d}")
            for name in names:
                p = Path(directory) / name
                if p.suffix in INPUT_SUFFIXES:
                    rel = p.relative_to(root).as_posix()
                    safe_file(root, rel)
                    if rel not in GENERATED_FILES:
                        paths.add(rel)
    for rel in INPUT_FILES:
        if (root / rel).exists() or (root / rel).is_symlink():
            safe_file(root, rel)
            paths.add(rel)
    for rel in OWNER.values():
        safe_file(root, rel)  # Missing owner must not silently become an empty table.
        paths.add(rel)
    return sorted(paths)


def snapshot(root: Path) -> dict[str, dict[str, Any]]:
    result = {}
    for rel in input_paths(root):
        raw = safe_file(root, rel).read_bytes()
        result[rel] = {"sha256": digest(raw), "bytes": len(raw)}
    return result


class NativeOwners:
    """Reuse native namespace resolution, target closure, contrast and journal owners."""
    def __init__(self, root: Path, atlas_payload: dict[str, Any]):
        self.root = root
        scripts = (root / "scripts").resolve()
        sys.path.insert(0, str(scripts))
        try:
            self.rr = importlib.import_module("relation_registry")
            self.cr = importlib.import_module("contrast_ledger")
            self.record = importlib.import_module("research_record")
            for mod in (self.rr, self.cr, self.record):
                if Path(mod.__file__).resolve().parent != scripts:
                    raise SubstrateError("native owner imported from a different checkout")
            self.source = self.rr.LeanSource(root)
            self.atlas = self.rr.Atlas(atlas_payload, self.source)
            self.compiled = self.rr.compiled_modules(root)
        finally:
            sys.path.pop(0)

    def resolve(self, name: str, module: str | None) -> dict[str, Any]:
        result = self.atlas.resolve(name, self.rr.normalise_module(module))
        # A unique lexical/namespace match is navigation evidence, NOT formal identity.
        return {k: v for k, v in result.items() if k != "row"} | {
            "atlas_id": result.get("row", {}).get("id"),
            "identity_evidence": "native_source_resolver_not_kernel_unification",
        }

    def attest(self, row: dict[str, Any]) -> dict[str, Any]:
        return self.rr.attest(row, self.atlas, self.source, self.compiled)

    def triggered(self, rows: list[dict[str, Any]], number: int) -> list[dict[str, Any]]:
        return self.cr.triggered(rows, problem=number)

    def events(self, path: Path) -> list[dict[str, Any]]:
        if path.resolve() != self.record.journal_path(self.root).resolve():
            raise SubstrateError("journal path differs from the native owner")
        events, state = self.record.replay(self.root)
        if state.errors:
            raise SubstrateError("native journal rejected: " + "; ".join(state.errors[:5]))
        return events


def quarantined_relation(row: dict[str, Any], observation: dict[str, Any]) -> dict[str, Any]:
    """No caller-supplied Boolean or digest can bypass missing typed replay.

    Keep the native report for diagnosis. Even native state='attested' binds only
    what that checker checks; it does not bind the row's Γ/left/right expressions.
    """
    return {
        "owner_row": row,
        "native_certificate_observation": observation,
        "endpoint_binding": "not_established_by_existing_checker",
        "inference_eligible": False,
        "reason": "requires kernel-derived context and endpoint bindings plus pinned replay",
    }


SQL = """
CREATE TABLE meta(key TEXT PRIMARY KEY, value TEXT NOT NULL);
CREATE TABLE source(path TEXT PRIMARY KEY, sha256 TEXT NOT NULL, bytes INTEGER NOT NULL);
CREATE TABLE node(kind TEXT NOT NULL, id TEXT NOT NULL, payload TEXT NOT NULL,
                  source TEXT NOT NULL, pointer TEXT NOT NULL, PRIMARY KEY(kind,id));
CREATE TABLE link(kind TEXT NOT NULL, sk TEXT NOT NULL, sid TEXT NOT NULL,
                  dk TEXT NOT NULL, did TEXT NOT NULL, detail TEXT NOT NULL);
CREATE TABLE membership(problem TEXT NOT NULL, kind TEXT NOT NULL, id TEXT NOT NULL,
                        basis TEXT NOT NULL, PRIMARY KEY(problem,kind,id,basis));
CREATE INDEX links_src ON link(sk,sid,kind);
CREATE INDEX links_dst ON link(dk,did,kind);
CREATE INDEX members ON membership(problem,kind,id);
"""


def build(root: Path, destination: Path, *, hooks: Any = None) -> dict[str, Any]:
    """Build from owners. 'hooks' is only a unit-test injection seam, not a CLI option."""
    root = root.resolve()
    before = snapshot(root)
    documents = {k: decode(safe_file(root, p).read_bytes()) for k, p in OWNER.items() if k != "event"}
    native = hooks or NativeOwners(root, documents["declaration"])
    # Journal verification happens at the original owner, with its exact chain rules.
    events = native.events(safe_file(root, OWNER["event"]))
    destination = destination.absolute()
    if destination.is_symlink():
        raise SubstrateError("output is a symlink")
    if destination.suffix != ".sqlite":
        raise SubstrateError("derived output must use .sqlite outside the source input set")
    if destination.resolve().is_relative_to(root):
        rel = destination.resolve().relative_to(root).as_posix()
        if rel in before:
            raise SubstrateError("output would overwrite a source")
    destination.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix="substrate-", suffix=".sqlite", dir=destination.parent)
    os.close(fd)
    db = sqlite3.connect(temporary)
    counts: collections.Counter[str] = collections.Counter()
    try:
        db.executescript(SQL)
        db.executemany("INSERT INTO source VALUES(?,?,?)", ((p, v["sha256"], v["bytes"]) for p, v in before.items()))
        def node(kind: str, ident: str, row: Any, owner: str, pointer: str) -> None:
            if not isinstance(ident, str) or not ident:
                raise SubstrateError(f"missing identifier for {kind}:{pointer}")
            try:
                db.execute("INSERT INTO node VALUES(?,?,?,?,?)", (kind, ident, canonical(row), OWNER[owner], pointer))
            except sqlite3.IntegrityError as exc:
                raise SubstrateError(f"duplicate {kind} identifier: {ident}") from exc
            counts[kind] += 1
        def link(kind: str, sk: str, sid: str, dk: str, did: str, detail: Any) -> None:
            db.execute("INSERT INTO link VALUES(?,?,?,?,?,?)", (kind, sk, sid, dk, did, canonical(detail)))
        def member(problem: str, kind: str, ident: str, basis: str) -> None:
            db.execute("INSERT OR IGNORE INTO membership VALUES(?,?,?,?)", (problem, kind, ident, basis))
        claims = documents["claim"]["claims"]
        opens = documents["claim"]["remaining_open_propositions"]
        problem_for_target: dict[str, str] = {}
        module_membership: dict[str, set[str]] = collections.defaultdict(set)
        for i, row in enumerate(documents["problem"]["problems"]):
            p = str(row["erdos_number"])
            node("problem", p, row, "problem", f"/problems/{i}")
            for module in row.get("modules", []):
                if module.get("path"):
                    module_membership[module["path"]].add(p)
            registration = row["claim_registration"]
            target = registration.get("programme_claim_id")
            if target:
                problem_for_target[target] = p
                member(p, "claim", target, "programme_claim_id")
            for cid in registration.get("registered_claim_ids", []):
                member(p, "claim", cid, "problems.registered_claim_ids")
        for i, row in enumerate(opens):
            node("obligation", row["id"], row, "claim", f"/remaining_open_propositions/{i}")
            target = row.get("open_target_claim")
            if target in problem_for_target:
                member(problem_for_target[target], "obligation", row["id"], "open_target_claim")
            if target:
                link("registered_obligation_of", "obligation", row["id"], "claim", target,
                     {"not_exhaustive_of_all_mathematical_obligations": True})
        open_by_id = {r["id"]: r for r in opens}
        for i, row in enumerate(documents["declaration"]["declarations"]):
            node("declaration", row["id"], row, "declaration", f"/declarations/{i}")
        resolutions: list[dict[str, Any]] = []
        def declaration_link(kind: str, ident: str, ref: dict[str, Any]) -> str | None:
            resolution = native.resolve(ref["name"], ref.get("file") or ref.get("module"))
            resolutions.append({"kind": kind, "id": ident, "reference": ref, "resolution": resolution})
            if resolution.get("state") == "found" and resolution.get("atlas_id"):
                target = resolution["atlas_id"]
                link("source_declaration_reference", kind, ident, "declaration", target, resolution)
                return target
            link("unresolved_declaration_reference", kind, ident, "unresolved", ref["name"], resolution)
            return None
        for i, row in enumerate(claims):
            node("claim", row["id"], row, "claim", f"/claims/{i}")
            for oid in row.get("remaining_open_proposition_ids") or []:
                if oid not in open_by_id:
                    raise SubstrateError(f"{row['id']}: missing registered obligation {oid}")
                link("mentions_registered_obligation", "claim", row["id"], "obligation", oid, {})
                target = open_by_id[oid].get("open_target_claim")
                if target in problem_for_target:
                    member(problem_for_target[target], "claim", row["id"], "remaining_open_proposition_ids")
            for ref in row.get("declarations") or []:
                declaration_link("claim", row["id"], ref)
                module = ref.get("module", "")
                if module.endswith(".lean"):
                    path = module if module.startswith("lean/") else "lean/" + module
                    for p in module_membership.get(path, set()):
                        member(p, "claim", row["id"], "explicit_problem_module_membership_not_goal_entailment")
        for i, row in enumerate(documents["paper_result"]["rows"]):
            node("paper_result", row["id"], row, "paper_result", f"/rows/{i}")
            if row.get("problem") is not None:
                member(str(row["problem"]), "paper_result", row["id"], "paper_lean_coverage.problem")
            for ref in row.get("lean", {}).get("declarations") or []:
                declaration_link("paper_result", row["id"], ref)
        # Shared modules are not guessed from their directory name. A resolved common
        # declaration supplies an evidence-labelled navigation join, not equivalence.
        db.execute("""INSERT OR IGNORE INTO membership
            SELECT m.problem,'claim',a.sid,'shared_source_declaration_in_paper_ledger'
            FROM link a JOIN link b ON a.dk=b.dk AND a.did=b.did
            JOIN membership m ON m.kind=b.sk AND m.id=b.sid
            WHERE a.sk='claim' AND b.sk='paper_result'
              AND a.kind='source_declaration_reference' AND b.kind=a.kind""")
        dep = documents["dependency"]
        for i, row in enumerate(dep["nodes"]):
            node("dependency_node", str(row["node_id"]), row, "dependency", f"/nodes/{i}")
        for i, row in enumerate(dep["edges"]):
            src, dst, bits = row
            link("dependency_not_implication", "dependency_node", str(src), "dependency_node", str(dst),
                 {"bits": bits, "source_pointer": f"/edges/{i}"})
        atlas_by_id = {row["id"]: row for row in documents["declaration"]["declarations"]}
        for i, row in enumerate(documents["relation"]["rows"]):
            observation = native.attest(row)
            decorated = quarantined_relation(row, observation)
            certificate_row = atlas_by_id.get(observation.get("atlas_id"))
            if certificate_row is not None:
                decorated["certificate_signature"] = certificate_row["signature"]
                decorated["certificate_source"] = {"path": certificate_row["module"], "line": certificate_row["line"], "atlas_id": certificate_row["id"]}
                link("source_declaration_reference", "relation", row["id"], "declaration", certificate_row["id"], {"basis": "native_certificate_lookup_not_endpoint_binding"})
            node("relation", row["id"], decorated, "relation", f"/rows/{i}")
            if row.get("problem") is not None:
                member(str(row["problem"]), "relation", row["id"], "relation.problem")
        contrasts = documents["contrast"]["rows"]
        for i, row in enumerate(contrasts):
            node("contrast", row["id"], row, "contrast", f"/rows/{i}")
        for p in sorted(set(problem_for_target.values())):
            for match in native.triggered(contrasts, int(p)):
                member(p, "contrast", match["id"], "native_contrast_ledger.triggered")
        route_doc = documents["route"]
        for i, reader in enumerate(route_doc["readers"]):
            for j, row in enumerate(reader["routes"]):
                node("route", row["id"], row, "route", f"/readers/{i}/routes/{j}")
                # Keep synthesis as a first-class world; cross-world strings are NOT
                # filtered by equality with one problem number.
                for p in re.findall(r"\d+", str(row.get("world", ""))):
                    member(p, "route", row["id"], "explicit_route_world")
        reopened = route_doc.get("reopened", {})
        if not isinstance(reopened, dict):
            raise SubstrateError("expected replay_worlds.reopened object; adapt owner schema explicitly")
        for ident, row in reopened.items():
            node("route_reopening", ident, row, "route", "/reopened/" + ident.replace("~", "~0").replace("/", "~1"))
        for i, event in enumerate(events):
            node("event", event["event_sha"], event, "event", f"line:{i+1}")
        # Reject membership to missing records (e.g. stale problems.json registration).
        dangling = list(db.execute("SELECT DISTINCT m.kind,m.id FROM membership m LEFT JOIN node n ON n.kind=m.kind AND n.id=m.id WHERE n.id IS NULL"))
        if dangling:
            raise SubstrateError(f"dangling owner membership: {dangling[:5]}")
        pins = {
            "claims_formal_source": documents["claim"].get("release", {}).get("formal_source"),
            "paper_lean_pin": documents["paper_result"].get("lean_pin"),
            "dependency_formal_source": dep.get("formal_source"),
            "atlas_source_fingerprint": documents["declaration"].get("source_fingerprint"),
            "dependency_source_fingerprint": dep.get("source_fingerprint"),
        }
        unresolved = [r for r in resolutions if r["resolution"].get("state") != "found"]
        meta = {
            "schema": SCHEMA, "boundary": BOUNDARY,
            "compiler_sha256": digest(Path(__file__).read_bytes()),
            "snapshot_id": digest(canonical(before).encode()),
            "input_count": len(before), "counts": dict(sorted(counts.items())),
            "dependency_edge_count": len(dep["edges"]),
            "dependency_edge_legend": dep.get("edge_relation_bit_legend"),
            "native_resolution_gaps": unresolved,
            "source_reported_pins": pins,
            "relation_policy": "all_existing_text_endpoints_quarantined_pending_typed_replay",
            "current_argument_graph": "not_admitted_no_current_replay_receipt",
            "registered_obligation_coverage": "all_owner_rows_not_all_possible_missing_hypotheses",
            "dependency_owner_coverage": dep.get("coverage"),
            "journal_verification": "native_read_events_chain_validation_not_mathematical_acceptance",
        }
        after = snapshot(root)
        if before != after:
            raise SubstrateError("source changed during build; discard and rebuild from a stable checkout")
        db.executemany("INSERT INTO meta VALUES(?,?)", ((k, canonical(v)) for k, v in meta.items()))
        db.commit()
        if db.execute("PRAGMA integrity_check").fetchone()[0] != "ok":
            raise SubstrateError("SQLite integrity check failed")
        db.close()
        os.replace(temporary, destination)
        return meta
    except BaseException:
        db.close()
        Path(temporary).unlink(missing_ok=True)
        raise


class View:
    def __init__(self, root: Path, path: Path, *, verify_sources: bool = True):
        # verify_sources=False is an explicit unit-test seam; no public CLI bypass.
        self.root = root.resolve()
        if not path.is_file():
            raise SubstrateError("materialized view missing; run python3 scripts/corpus_substrate.py --build (no stale fallback)")
        self.db = sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True)
        self.db.execute("PRAGMA query_only=ON")
        self.meta = {k: decode(v.encode()) for k, v in self.db.execute("SELECT key,value FROM meta")}
        if self.meta.get("compiler_sha256") != digest(Path(__file__).read_bytes()):
            self.close()
            raise SubstrateError("compiler changed; rebuild the projection")
        if self.meta.get("schema") != SCHEMA:
            self.close()
            raise SubstrateError("unknown substrate schema")
        expected = {p: {"sha256": h, "bytes": n} for p, h, n in self.db.execute("SELECT path,sha256,bytes FROM source")}
        if digest(canonical(expected).encode()) != self.meta.get("snapshot_id"):
            self.close()
            raise SubstrateError("source manifest digest mismatch")
        if verify_sources and snapshot(self.root) != expected:
            self.close()
            raise SubstrateError("stale substrate: owner bytes or source inventory changed; rebuild")
        if verify_sources:
            try:
                self.verify_registered_rows()
            except BaseException:
                self.close()
                raise

    def verify_registered_rows(self) -> None:
        """Independent keyspace/payload check, not counts copied from producer metadata.

        This protects registered-result coverage even when a derived SQLite file is
        edited without changing its source manifest. The entire formal index is a
        disposable navigation cache, not an adversarially authenticated proof store.
        """
        claims = decode(safe_file(self.root, OWNER["claim"]).read_bytes())
        ledger = decode(safe_file(self.root, OWNER["paper_result"]).read_bytes())
        for kind, expected in (("claim", claims["claims"]),
                               ("obligation", claims["remaining_open_propositions"]),
                               ("paper_result", ledger["rows"])):
            originals = {r["id"]: r for r in expected}
            actual = {ident: decode(raw.encode()) for ident, raw in self.db.execute(
                "SELECT id,payload FROM node WHERE kind=?", (kind,))}
            if len(originals) != len(expected) or originals != actual:
                raise SubstrateError(f"{kind}: derived keyspace or payload differs from owner")
        registry = decode(safe_file(self.root, OWNER["relation"]).read_bytes())["rows"]
        actual_relations = self.rows("relation")
        if {r["id"] for r in registry} != {r["id"] for r in actual_relations}:
            raise SubstrateError("relation keyspace differs from owner")
        expected_relations = {r["id"]: r for r in registry}
        for r in actual_relations:
            decorated = r["record"]
            if (decorated.get("owner_row") != expected_relations[r["id"]]
                    or decorated.get("inference_eligible") is not False
                    or decorated.get("endpoint_binding") != "not_established_by_existing_checker"):
                raise SubstrateError("derived relation changed its owner data or quarantine policy")

    def close(self) -> None:
        self.db.close()

    def __enter__(self) -> "View":
        return self

    def __exit__(self, *_: Any) -> None:
        self.close()

    def rows(self, kind: str, problem: str | None = None) -> list[dict[str, Any]]:
        sql = "SELECT n.id,n.payload,n.source,n.pointer,s.sha256 FROM node n JOIN source s ON s.path=n.source WHERE n.kind=?"
        args: list[Any] = [kind]
        if problem is not None:
            sql += " AND EXISTS(SELECT 1 FROM membership m WHERE m.kind=n.kind AND m.id=n.id AND m.problem=?)"
            args.append(problem)
        sql += " ORDER BY n.id"
        return [{"id": ident, "record": decode(payload.encode()),
                 "source": {"path": source, "pointer": pointer, "sha256": sha}}
                for ident, payload, source, pointer, sha in self.db.execute(sql, args)]

    def node(self, kind: str, ident: str) -> dict[str, Any]:
        found = self.db.execute("SELECT payload,source,pointer FROM node WHERE kind=? AND id=?", (kind, ident)).fetchone()
        if found is None:
            raise SubstrateError(f"unknown {kind}: {ident}")
        row, source, pointer = found
        return {"id": ident, "record": decode(row.encode()), "source": {"path": source, "pointer": pointer,
            "sha256": self.db.execute("SELECT sha256 FROM source WHERE path=?", (source,)).fetchone()[0]}}

    def frontier(self, problem: str | int, limit: int = 8, cursor: str | None = None) -> dict[str, Any]:
        problem = str(problem)
        if not 1 <= limit <= 64:
            raise SubstrateError("page limit must be 1..64")
        p = self.node("problem", problem)
        target = p["record"]["claim_registration"]["programme_claim_id"]
        claims = [r for r in self.rows("claim", problem) if r["id"] != target]
        offset = 0
        if cursor:
            try:
                token = decode(cursor.encode())
                if token["snapshot"] != self.meta["snapshot_id"] or token["problem"] != problem:
                    raise SubstrateError("cursor belongs to a different snapshot or problem")
                offset = token["offset"]
                if type(offset) is not int or not 0 <= offset <= len(claims):
                    raise SubstrateError("invalid cursor offset")
            except (KeyError, TypeError, json.JSONDecodeError) as exc:
                raise SubstrateError("malformed cursor") from exc
        next_offset = offset + limit
        registered = self.rows("paper_result", problem)
        programme = self.node("claim", target)
        # Parent prose names results explicitly. Preserve ALL matching candidates
        # above pagination, including shared claims. This is navigation, not a
        # theorem-strength order or namespace-aware proof identity.
        text = programme["record"]["statement"]
        cited = []
        for candidate in self.rows("claim"):
            if candidate["id"] == target:
                continue
            names = [ref["name"] for ref in candidate["record"].get("declarations", [])]
            matches = sorted({n for n in names if re.search(r"(?<![\w.])" + re.escape(n.rsplit(".", 1)[-1]) + r"(?![\w.])", text)})
            if matches:
                cited.append(dict(candidate, navigation_matches=matches, match_boundary="literal_name_mention_not_logical_dominance"))
        relation_rows = self.rows("relation", problem)
        return {
            "kind": "source_bound_frontier", "schema": SCHEMA,
            "snapshot_id": self.meta["snapshot_id"], "problem": problem,
            "boundary": BOUNDARY,
            "programme": programme,
            "programme_cited_results": cited,
            "endpoint_contracts": [r for r in relation_rows if r["record"]["owner_row"].get("relation") == "endpoint_route"],
            "endpoint_obligation_boundary": "Certificate signatures are shown whole. No new registered-open node or discharged premise is inferred from endpoint prose.",
            "strongest_result": {"state": "not_established", "reason":
                "No validated goal/context-indexed dominance order is available. The programme statement is shown verbatim; status order is not strength."},
            "registered_open_obligations": self.rows("obligation", problem),
            "obligation_boundary": self.meta["registered_obligation_coverage"],
            "registered_results": claims[offset:next_offset],
            "result_page": {"offset": offset, "returned": len(claims[offset:next_offset]), "total": len(claims),
                "order": "identifier_not_strength", "next": canonical({"snapshot": self.meta["snapshot_id"], "problem": problem, "offset": next_offset}) if next_offset < len(claims) else None},
            "paper_result_coverage": {"count": len(registered), "status_counts": dict(collections.Counter(
                r["record"].get("comparator", {}).get("status", "unreported") for r in registered)),
                "drilldown": f"corpus_substrate.py --rows paper_result --problem {problem}"},
            "relations": relation_rows,
            "misreadings": self.rows("contrast", problem),
            "attempts": self.rows("route", problem),
            "cross_problem_drilldown": "corpus_substrate.py --cross-problem",
            "current_argument_graph": self.meta["current_argument_graph"],
            "global_registry": {"claims": self.meta["counts"]["claim"],
                "unassigned_claims": self.db.execute("SELECT count(*) FROM node n WHERE kind='claim' AND NOT EXISTS(SELECT 1 FROM membership m WHERE m.kind=n.kind AND m.id=n.id)").fetchone()[0],
                "rule": "unassigned does not mean irrelevant; every claim remains in the global register"},
            "journal": {"events": self.meta["counts"].get("event", 0), "verification": self.meta["journal_verification"],
                        "drilldown": "research_record.py status; corpus_substrate.py --rows event"},
        }

    def cross_problem(self) -> dict[str, Any]:
        # No LLM-derived analogy is inserted into the proof layer.
        routes = [r for r in self.rows("route") if not str(r["record"].get("world", "")).isdigit()]
        return {"kind": "recorded_cross_problem_routes", "snapshot_id": self.meta["snapshot_id"],
                "routes": routes, "reopenings": self.rows("route_reopening"),
                "evidence_class": "historical_route_record_not_transfer_proof",
                "boundary": "A recorded transfer idea, failed attempt, and checked instantiated theorem are distinct. No outcome or cost transports automatically."}

    def register(self) -> str:
        lines = ["# Complete registered-claim view", "", f"Snapshot: `{self.meta['snapshot_id']}`", "", BOUNDARY, ""]
        for row in self.rows("claim"):
            claim = row["record"]
            lines += [f"## {claim['id']}", "", f"Recorded status: {claim['status']}", "", claim["statement"], "",
                      f"Source: `{row['source']['path']}` `{row['source']['pointer']}` `{row['source']['sha256']}`", ""]
        return "\n".join(lines).rstrip() + "\n"


def check_generated(expected: str, actual: str) -> None:
    """Whole generated-file equality; a hidden marker or copied ID cannot pass."""
    if expected != actual:
        raise SubstrateError("generated summary differs from its complete registered source projection")


def render_frontier(packet: dict[str, Any]) -> str:
    lines = [f"Erdős #{packet['problem']} | source-bound frontier", f"Snapshot: {packet['snapshot_id']}", "",
             packet["boundary"], "", "Programme statement (verbatim, not a claim of unique maximal strength):",
             packet["programme"]["record"]["statement"], "", "Registered open obligations:"]
    for row in packet["registered_open_obligations"]:
        lines += [f"- {row['id']}: {row['record']['statement']}"]
    lines += ["", "Results explicitly named by the programme statement (not paginated):"]
    for row in packet["programme_cited_results"]:
        lines += [f"- {row['id']} [{row['record']['status']}]: {row['record']['statement']}"]
    lines += ["", "Endpoint certificate signatures (source-listed; typed replay required):"]
    for row in packet["endpoint_contracts"]:
        lines += [f"- {row['id']}: {row['record'].get('certificate_signature', 'signature unavailable')}"]
    lines += ["", "Registered results (identifier order, never strength order):"]
    for row in packet["registered_results"]:
        lines += [f"- {row['id']} [{row['record']['status']}]: {row['record']['statement']}"]
    lines += ["", "Known misreadings:"]
    for row in packet["misreadings"]:
        lines += [f"- {row['id']}: {row['record']['right_reading']}"]
    lines += ["", f"Relations: {len(packet['relations'])} navigation rows; existing endpoint text is quarantined.",
              f"Recorded attempts: {len(packet['attempts'])}; paper-ledger rows: {packet['paper_result_coverage']['count']}.",
              "Use JSON for complete source references, relation observations and attempt boundaries.",
              "Current argument graph: " + packet["current_argument_graph"],
              "Page: " + canonical(packet["result_page"])]
    return "\n".join(lines) + "\n"


def frontier_packet(root: Path, problem: str, limit: int = 8, cursor: str | None = None) -> dict[str, Any]:
    try:
        if (root / DEFAULT_DB).exists():
            with View(root, root / DEFAULT_DB) as view:
                return view.frontier(problem, limit, cursor)
        # A cold clone has no .lake cache. Keep the first read usable without
        # requiring a writable checkout or silently accepting stale owner bytes.
        with tempfile.TemporaryDirectory(prefix="plectis-frontier-") as directory:
            path = Path(directory) / "corpus.sqlite"
            build(root, path)
            with View(root, path) as view:
                return view.frontier(problem, limit, cursor)
    except sqlite3.Error as exc:
        raise SubstrateError(f"derived database cannot be read; rebuild it: {exc}") from exc


def refresh_register(root: Path, *, check: bool) -> None:
    """Rebuild from native sources, independently of any local SQLite cache."""
    with tempfile.TemporaryDirectory(prefix="plectis-register-") as directory:
        path = Path(directory) / "corpus.sqlite"
        build(root, path)
        with View(root, path) as view:
            rendered = view.register()
        target = root / "docs/reference/CORPUS_REGISTER.md"
        if check:
            check_generated(rendered, target.read_text(encoding="utf-8"))
        else:
            if target.is_symlink() or target.parent.is_symlink():
                raise SubstrateError("register output is a symlink")
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(rendered, encoding="utf-8")


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    p.add_argument("--database", type=Path)
    group = p.add_mutually_exclusive_group(required=True)
    group.add_argument("--build", action="store_true")
    group.add_argument("--write", action="store_true", help="regenerate the registered-claim projection from sources")
    group.add_argument("--check", action="store_true", help="independently check the registered-claim projection")
    group.add_argument("--frontier")
    group.add_argument("--rows", choices=("claim", "problem", "declaration", "dependency_node", "paper_result", "relation", "contrast", "event", "route", "obligation", "route_reopening"))
    group.add_argument("--node", nargs=2, metavar=("KIND", "ID"))
    group.add_argument("--cross-problem", action="store_true")
    group.add_argument("--render-register", type=Path)
    group.add_argument("--check-register", type=Path)
    group.add_argument("--metadata", action="store_true")
    p.add_argument("--problem")
    p.add_argument("--limit", type=int, default=8)
    p.add_argument("--cursor")
    p.add_argument("--format", choices=("json", "card"), default="json")
    args = p.parse_args()
    root = args.root.resolve()
    path = args.database or root / DEFAULT_DB
    try:
        if args.write or args.check:
            refresh_register(root, check=args.check)
            result = {"registered_projection": "equal" if args.check else "written"}
        elif args.build:
            result = build(root, path)
        else:
            with View(root, path) as view:
                if args.frontier:
                    result = view.frontier(args.frontier, args.limit, args.cursor)
                elif args.rows:
                    result = {"kind": "owner_rows", "snapshot_id": view.meta["snapshot_id"], "rows": view.rows(args.rows, args.problem)}
                elif args.node:
                    result = view.node(*args.node)
                elif args.cross_problem:
                    result = view.cross_problem()
                elif args.render_register:
                    target = args.render_register.resolve()
                    if target.is_relative_to(root) and target.relative_to(root).as_posix() not in GENERATED_FILES:
                        raise SubstrateError("in-repository register must use the declared generated output path")
                    if args.render_register.is_symlink():
                        raise SubstrateError("register output is a symlink")
                    args.render_register.parent.mkdir(parents=True, exist_ok=True)
                    args.render_register.write_text(view.register(), encoding="utf-8")
                    result = {"rendered": str(args.render_register)}
                elif args.check_register:
                    check_generated(view.register(), args.check_register.read_text(encoding="utf-8"))
                    result = {"registered_projection": "equal"}
                else:
                    result = view.meta
        if args.format == "card":
            if result.get("kind") != "source_bound_frontier":
                raise SubstrateError("card format is defined only for --frontier")
            print(render_frontier(result), end="")
        else:
            print(json.dumps(result, ensure_ascii=False, indent=2, allow_nan=False))
        return 0
    except (OSError, sqlite3.Error, ValueError, KeyError) as exc:
        print(f"corpus_substrate: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
