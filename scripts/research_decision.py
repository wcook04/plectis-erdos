#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Source-bound research decisions; an adapter, not a new claim/graph authority.

Reads the existing claim, contrast, relation, and research-record owners. Missing
optional inputs are explicit capabilities, not claims of absence in the live
repository. Selection by explicit claim links is deliberately NOT advertised as
complete semantic retrieval. The default command is read-only.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Iterable

import contrast_ledger
import relation_registry
import research_record

SCHEMA = "plectis-research-decision/1"
CLAIMS = "docs/claims.json"
RELATIONS = relation_registry.REGISTRY_PATH
CONTRASTS = "docs/research-commons/record/contrasts.json"
CAPABILITIES = {
    "route_memory": ("docs/problems.json", "docs/orientation.json",
                     "docs/research-commons/route-memory/route_memory.json"),
    "theory_experiment": ("docs/theory_lab.json", "docs/semantic_corpus.json.gz",
                          "docs/semantic/lab/benchmark_items.json"),
}


class DecisionError(ValueError):
    """An input is unsafe, inconsistent, stale, or exceeds its declared budget."""


def canonical(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":"), allow_nan=False).encode("utf-8")


def digest(value: Any) -> str:
    return hashlib.sha256(canonical(value)).hexdigest()


def safe_path(root: Path, relative: str) -> Path:
    if not isinstance(relative, str) or not relative or "\\" in relative:
        raise DecisionError("expected a nonempty POSIX repository-relative path")
    p = Path(relative)
    if p.is_absolute() or relative.startswith("~") or ".." in p.parts:
        raise DecisionError(f"unsafe path: {relative!r}")
    root = Path(root).resolve()
    current = root
    for part in p.parts:
        current = current / part
        if current.is_symlink():
            raise DecisionError(f"symlink input refused: {relative}")
    if current.exists() and not current.is_file():
        raise DecisionError(f"not a regular file: {relative}")
    return current


def snapshot(root: Path, paths: Iterable[str]) -> dict[str, Any]:
    files = {}
    for relative in sorted(set(paths)):
        p = safe_path(root, relative)
        files[relative] = hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
    return {"files": files, "digest": digest(files),
            "boundary": "content read-set; neither Git ancestry nor independent build attestation"}


def verify_snapshot(root: Path, expected: dict[str, Any]) -> None:
    if not isinstance(expected, dict) or not isinstance(expected.get("files"), dict):
        raise DecisionError("malformed snapshot")
    if digest(expected["files"]) != expected.get("digest"):
        raise DecisionError("snapshot digest mismatch")
    actual = snapshot(root, expected["files"])
    changed = [p for p, sha in expected["files"].items() if actual["files"][p] != sha]
    if changed:
        raise DecisionError("stale decision inputs: " + ", ".join(changed[:10]))


def _json(root: Path, relative: str) -> dict[str, Any]:
    p = safe_path(root, relative)
    if not p.exists():
        raise DecisionError(f"required source missing from this snapshot: {relative}")
    result = json.loads(p.read_text(encoding="utf-8"))
    if not isinstance(result, dict):
        raise DecisionError(f"expected JSON object: {relative}")
    return result


def _integrity_inputs(root: Path) -> set[str]:
    paths = {CLAIMS, RELATIONS, CONTRASTS, relation_registry.ATLAS_PATH,
             research_record.JOURNAL_PATH, "docs/problems.json", "docs/theory_lab.json",
             "lean-toolchain", "lakefile.toml", "lake-manifest.json",
             "scripts/research_decision.py", "scripts/relation_registry.py",
             "scripts/research_record.py", "scripts/contrast_ledger.py",
             ".github/workflows/lean-coverage-build.yml"}
    for required in CAPABILITIES.values():
        paths.update(required)
    # The native atlas/compilation-coverage check also reads source/import files.
    # Pin all supplied Lean sources rather than silently pretending four JSONs
    # capture the semantic environment. This costs hashes, not prompt text.
    for directory in ("lean", "scripts", ".github/workflows"):
        paths.update(p.relative_to(root).as_posix() for p in (root / directory).rglob("*")
                     if (p.is_file() or p.is_symlink()) and "__pycache__" not in p.parts
                     and p.suffix != ".pyc")
    return paths


def build(root: Path, problem: int, source_commit: str, byte_budget: int = 512_000) -> dict[str, Any]:
    root = Path(root).resolve()
    if isinstance(problem, bool) or not isinstance(problem, int) or problem <= 0:
        raise DecisionError("problem must be a positive integer")
    if not re.fullmatch(r"[0-9a-f]{40}", source_commit):
        raise DecisionError("source_commit must be an explicit full commit id")
    if not isinstance(byte_budget, int) or isinstance(byte_budget, bool) or byte_budget <= 0:
        raise DecisionError("byte_budget must be positive")
    stamp = snapshot(root, _integrity_inputs(root))
    claims = _json(root, CLAIMS)
    rows = claims.get("claims", [])
    by_id = {row["id"]: row for row in rows}
    if len(by_id) != len(rows):
        raise DecisionError("duplicate claim ids")
    programme_id = f"erdos_{problem}"
    if programme_id not in by_id:
        raise DecisionError(f"no programme claim: {programme_id}")
    programme = by_id[programme_id]
    open_ids = set(programme.get("remaining_open_proposition_ids", []))
    open_rows = [row for row in claims.get("remaining_open_propositions", [])
                 if row["id"] in open_ids or row.get("open_target_claim") == programme_id]
    open_ids.update(row["id"] for row in open_rows)
    selected = [row for row in rows if row["id"] == programme_id or
                open_ids.intersection(row.get("remaining_open_proposition_ids", []))]
    selected.sort(key=lambda row: row["id"])  # Lexical order makes NO strength claim.
    report = relation_registry.check(root)
    if not report["ok"]:
        raise DecisionError("relation owner rejected inputs: " + "; ".join(report["errors"][:5]))
    relations = [r for r in _json(root, RELATIONS)["rows"] if r.get("problem") == problem]
    contrast_rows = _json(root, CONTRASTS)["rows"]
    obligations = contrast_ledger.triggered(contrast_rows, problem=problem,
                   text="\n".join(str(c.get("statement", "")) for c in selected))
    journal = research_record.verify(root)
    if not journal["ok"]:
        raise DecisionError("research journal rejected: " + "; ".join(journal["errors"][:5]))
    capabilities = {}
    for name, paths in CAPABILITIES.items():
        missing = [p for p in paths if stamp["files"].get(p) is None]
        capabilities[name] = {"declared_inputs_present": not missing, "missing": missing,
                              "execution_tested": False}
    result = {
        "schema": SCHEMA, "source_commit": source_commit,
        "source_commit_authority": "caller-supplied snapshot label; content pinned separately",
        "problem": problem, "programme": programme, "claims": selected,
        "open_obligations": open_rows, "contrasts": obligations,
        "relations": relations,
        "relation_evidence": {"atlas_counts": report["counts"],
            "endpoint_mapping": "requires exact relation-binding replay; not established by atlas hash"},
        "record_head": journal["head"], "record_events": journal["events"],
        "capabilities": capabilities,
        "selection": {"basis": "programme id and explicit remaining-open linkage",
            "order": "claim id; not mathematical strength",
            "unselected_claim_count": len(rows) - len(selected),
            "semantic_completeness": "not established; unlinked/cross-programme results require retrieval"},
        "gates": {"unknown_is_novel": False, "equivalence_is_new_theorem": False,
            "operational_gain": "evaluate separately under fixed budget",
            "publication": "requires intended-meaning, source, kernel and literature review"},
        "snapshot": stamp,
    }
    verify_snapshot(root, stamp)  # Catch cooperative edits while owners were reading.
    if set(stamp["files"]) != _integrity_inputs(root):
        raise DecisionError("source inventory changed during decision compilation")
    result["decision_sha256"] = digest(result)
    if len(canonical(result)) > byte_budget:
        raise DecisionError("decision exceeds byte budget; split the task or raise the declared budget, "
                            "never silently drop obligations or source bindings")
    return result


def check_decision(root: Path, value: dict[str, Any]) -> None:
    if not isinstance(value, dict):
        raise DecisionError("decision must be a JSON object")
    body = {k: v for k, v in value.items() if k != "decision_sha256"}
    if value.get("schema") != SCHEMA or digest(body) != value.get("decision_sha256"):
        raise DecisionError("decision identity mismatch")
    verify_snapshot(root, value["snapshot"])
    if set(value["snapshot"]["files"]) != _integrity_inputs(Path(root).resolve()):
        raise DecisionError("stale source inventory: files added or removed")
    rebuilt = build(root, value["problem"], value["source_commit"],
                    byte_budget=max(512_000, len(canonical(value))))
    if rebuilt["decision_sha256"] != value["decision_sha256"]:
        raise DecisionError("decision projection differs from native sources; regenerate it")


def graph_check(path: Path, *, source_commit: str, lean_tree: str,
                assumptions: list[str], target: str | None = None) -> dict[str, Any]:
    """Reuse native Horn reasoning ONLY on an explicitly matching graph export.

    Both expected identities must come from a reviewed build/source manifest.
    A full current-root build/re-export remains Type A's responsibility.
    """
    if not re.fullmatch(r"[0-9a-f]{40}", source_commit) or not re.fullmatch(r"[0-9a-f]{40}", lean_tree):
        raise DecisionError("graph needs full expected source commit and Lean tree identities")
    raw = path.read_bytes()
    payload = json.loads(gzip.decompress(raw) if path.suffix == ".gz" else raw)
    source = payload.get("source", {})
    if source.get("source_revision") != source_commit or source.get("lean_tree") != lean_tree:
        raise DecisionError("graph source mismatch: historical/unknown graph is not a current oracle")
    import build_argument_continuations as graph_owner
    import argument_graph_frontier as frontier_owner
    graph = graph_owner.Graph.from_payload(payload)
    result = frontier_owner.Frontier(graph).check(assumptions, target=target)
    return {"graph_sha256": hashlib.sha256(raw).hexdigest(), "source": source,
            "result": result, "boundary": "recorded-edge derivation, not complete theorem search"}


def markdown(value: dict[str, Any]) -> str:
    """Compact view; full read-set is in JSON, not duplicated in a prompt."""
    lines = [f"# Research decision: Erdős #{value['problem']}",
             f"Decision: `{value['decision_sha256']}`", "",
             value["programme"]["statement"], "", "## Explicitly linked claims"]
    for row in value["claims"]:
        lines += [f"### {row['id']} — {row['status']}", row.get("statement", ""), ""]
    lines += ["## Surviving obligations"]
    lines += [f"- {row['id']}: {row['statement']}" for row in value["open_obligations"]]
    lines += ["", "## Mandatory distinctions"]
    lines += [f"- {r['id']}: {r['packet_obligation']}" for r in value["contrasts"]]
    lines += ["", "## Evidence limits", json.dumps(value["selection"], ensure_ascii=False),
              json.dumps(value["relation_evidence"], ensure_ascii=False),
              json.dumps(value["capabilities"], ensure_ascii=False),
              "A supplied commit label is not an ancestry check. Full source hashes are in JSON."]
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--problem", type=int, required=True)
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--byte-budget", type=int, default=512_000)
    parser.add_argument("--format", choices=("json", "markdown"), default="json")
    args = parser.parse_args()
    try:
        value = build(args.root, args.problem, args.source_commit, args.byte_budget)
        print(markdown(value) if args.format == "markdown" else
              json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True), end="\n")
    except (DecisionError, ValueError, OSError, KeyError) as exc:
        print(f"research_decision: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
