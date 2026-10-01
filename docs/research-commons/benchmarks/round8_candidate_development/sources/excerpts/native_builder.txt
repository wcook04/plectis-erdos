#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Build a source-bound *developmental* relation-classification benchmark.

This consumes the native authored registry and exact-predicate binding owner.
The eight disclosed rows are development examples, never a held-out or
confirmatory bank. The prompt file is separated from its answer key on disk.
No Lean subprocess is launched by this builder.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
from typing import Any

import relation_binding
import relation_registry
import run_kernel_probes

SCHEMA = "plectis-restatement-development/1"
RELATIONS = {
    "equivalent": "restatement",
    "endpoint_route": "conditional_route",
    "refuted": "local_refutation",
    "feasible": "local_feasibility",
}


class BenchmarkError(ValueError):
    """Refuse a stale, unbound, or overclaimed benchmark."""


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _canonical(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False, allow_nan=False).encode("utf-8")


def _source(root: Path, relative: str) -> tuple[bytes, str]:
    if not isinstance(relative, str) or not relative.startswith("lean/"):
        raise BenchmarkError("certificate source must be a checkout-local Lean file")
    path = PurePosixPath(relative)
    if path.is_absolute() or ".." in path.parts or str(path) != relative:
        raise BenchmarkError("unsafe certificate path")
    source = root / relative
    if source.is_symlink() or not source.is_file():
        raise BenchmarkError(f"missing or linked certificate source: {relative}")
    return source.read_bytes(), relative


def _certificate_line(source: bytes, declaration: str) -> int:
    name = declaration.rsplit(".", 1)[-1]
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", name):
        raise BenchmarkError("invalid certificate declaration")
    text = source.decode("utf-8")
    hits = list(re.finditer(rf"^theorem\s+{re.escape(name)}\s*:", text, re.M))
    if len(hits) != 1:
        raise BenchmarkError(f"certificate declaration not unique in source: {declaration}")
    return text.count("\n", 0, hits[0].start()) + 1


def _checked_replay(root: Path, source: str, manifest: dict[str, Any],
                    receipt: dict[str, Any]) -> dict[str, Any]:
    """Check a *locally trusted* relation_binding replay against current inputs.

    This validates source identity and receipt structure. It cannot authenticate
    the operator who supplied the JSON, nor substitute for a clean build.
    """
    if not isinstance(receipt, dict) or receipt.get("schema") != "plectis-relation-binding-result/1":
        raise BenchmarkError("wrong relation-binding receipt schema")
    if receipt.get("manifest") != manifest:
        raise BenchmarkError("relation-binding receipt is stale or has different obligations")
    result = receipt.get("probe_result")
    if not isinstance(result, dict):
        raise BenchmarkError("missing native kernel-probe result")
    expected = {r["declaration"] for r in manifest["obligations"]}
    printed = result.get("axioms_printed")
    if not isinstance(printed, dict) or not expected <= printed.keys():
        raise BenchmarkError("missing per-binding axiom report")
    for name in expected:
        axioms = printed[name]
        if (not isinstance(axioms, list) or not all(isinstance(a, str) for a in axioms)
                or set(axioms) - run_kernel_probes.STANDARD_AXIOMS):
            raise BenchmarkError(f"invalid axiom report for {name}")
    required_native = {"evidence_class": "compilation_probe", "exit_code": 0,
                       "timed_out": False, "compilation_accepted": True,
                       "accepted": True, "uses_sorry": False,
                       "axioms_declared": [], "nonstandard_axioms": [], "errors": []}
    if any(result.get(k) != v for k, v in required_native.items()):
        raise BenchmarkError("native probe did not cleanly accept every binding")
    checked = relation_binding.checked_result(root, source, manifest, result)
    if checked["state"] != "binding_in_invoked_environment" or receipt != checked:
        raise BenchmarkError("relation-binding receipt fails current owner replay checks")
    return {"state": "development_binding_replay_checked",
            "receipt_sha256": _sha(_canonical(receipt)),
            "boundary": "locally supplied receipt; invoked environment only, not clean-build or semantic review"}


def build(root: Path, *, binding_receipt: dict[str, Any] | None = None,
          trusted_local_replay: bool = False, seal_confirmatory: bool = False
          ) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    root = Path(root).resolve()
    source, binding = relation_binding.emit(root)
    rows = relation_registry.load_registry(root)["rows"]
    obligations = binding["obligations"]
    if len(rows) != len(obligations) or not rows:
        raise BenchmarkError("binding obligations do not cover authored rows")
    registry_path = root / relation_registry.REGISTRY_PATH
    registry_sha = _sha(registry_path.read_bytes())
    snapshot_files = binding["snapshot"]["files"]
    if snapshot_files.get(relation_registry.REGISTRY_PATH) != registry_sha:
        raise BenchmarkError("registry bytes differ from binding snapshot")
    if binding_receipt is not None and not trusted_local_replay:
        raise BenchmarkError("receipt requires explicit trusted-local-replay assertion")
    if trusted_local_replay and binding_receipt is None:
        raise BenchmarkError("trusted-local-replay assertion has no receipt")
    replay = ({"state": "development_unverified",
               "boundary": "exact binding source generated but not Lean-replayed"}
              if binding_receipt is None else
              _checked_replay(root, source, binding, binding_receipt))
    if seal_confirmatory:
        if binding_receipt is None:
            raise BenchmarkError("confirmatory sealing requires a current binding replay")
        raise BenchmarkError("disclosed development families cannot be sealed as confirmatory gold")

    prompts: list[dict[str, Any]] = []
    answers: list[dict[str, Any]] = []
    module_hashes: dict[str, str] = {}
    for index, (row, obligation) in enumerate(zip(rows, obligations, strict=True), 1):
        cert = row["certificate"]
        if (row["id"] != obligation["row_id"]
                or relation_binding.decision.digest(row) != obligation["row_sha256"]
                or cert["declaration"] != obligation["certificate"]):
            raise BenchmarkError(f"row/binding mismatch at item {index}")
        if row["relation"] not in RELATIONS:
            raise BenchmarkError(f"unhandled developmental relation: {row['relation']}")
        module, path = _source(root, cert["module"])
        module_hashes[path] = _sha(module)
        if snapshot_files.get(path) != module_hashes[path]:
            raise BenchmarkError(f"certificate bytes differ from binding snapshot: {path}")
        line = _certificate_line(module, cert["declaration"])
        task_id = f"relation_{index:02d}"
        family = f"erdos_{row['problem']}" if row.get("problem") is not None else "unassigned"
        prompts.append({"task_id": task_id, "family_id": family,
                        "context": row["context"], "left": row["left"], "right": row["right"],
                        "question": "Classify the strongest recorded relation under exactly this context; state its direction, any open input, and whether it alone supplies the target."})
        answers.append({"task_id": task_id, "family_id": family, "row_id": row["id"],
                        "row_sha256": obligation["row_sha256"], "relation": row["relation"],
                        "category": RELATIONS[row["relation"]], "certificate": cert["declaration"],
                        "certificate_source": f"{path}:{line}",
                        "certificate_source_sha256": module_hashes[path],
                        "scope": row["context"], "left": row["left"], "right": row["right"],
                        "boundary": row["note"], "novelty": "not_inferred",
                        "independent_result_count": "not_inferred"})
    prompt_doc = {"schema": SCHEMA, "split": "development", "tasks": prompts,
                  "instruction": "Answer from the frozen material you are given. Distinguish equivalence, one-way route, local refutation, feasibility, and unknown; do not infer novelty."}
    key_doc = {"schema": SCHEMA, "split": "development", "answers": answers,
               "authority_boundary": "registry/certificate source with binding replay state in control manifest; not an automatic novelty verdict"}
    manifest_doc = {"schema": SCHEMA, "split": "development", "gold_state": replay["state"],
                    "binding_replay": replay, "binding_source_sha256": binding["source_sha256"],
                    "binding_snapshot_sha256": binding["snapshot"]["digest"],
                    "registry_path": relation_registry.REGISTRY_PATH,
                    "registry_sha256": registry_sha,
                    "certificate_sources_sha256": dict(sorted(module_hashes.items())),
                    "prompts_sha256": _sha(_canonical(prompt_doc)),
                    "answer_key_sha256": _sha(_canonical(key_doc)),
                    "task_count": len(prompts),
                    "independent_families": sorted({p["family_id"] for p in prompts}),
                    "confirmatory_sealed": False,
                    "claim_boundary": "developmental relation classification only; no correctness-rate, novelty, or performance claim"}
    return prompt_doc, key_doc, manifest_doc


def write_bundle(out: Path, docs: tuple[dict[str, Any], dict[str, Any], dict[str, Any]]) -> None:
    participant = out / "participant"
    control = out / "control"
    if out.exists() and any(out.iterdir()):
        raise BenchmarkError("output directory must be empty; do not overwrite a frozen bank")
    participant.mkdir(parents=True, exist_ok=True)
    control.mkdir(parents=True, exist_ok=True)
    for path, document in ((participant / "prompts.json", docs[0]),
                           (control / "answer_key.json", docs[1]),
                           (control / "manifest.json", docs[2])):
        path.write_bytes(_canonical(document) + b"\n")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--binding-receipt", type=Path)
    parser.add_argument("--trusted-local-replay", action="store_true")
    parser.add_argument("--seal-confirmatory", action="store_true")
    args = parser.parse_args(argv)
    try:
        receipt = json.loads(args.binding_receipt.read_text()) if args.binding_receipt else None
        docs = build(args.root, binding_receipt=receipt,
                     trusted_local_replay=args.trusted_local_replay,
                     seal_confirmatory=args.seal_confirmatory)
        write_bundle(args.out, docs)
        print(json.dumps({"state": docs[2]["gold_state"], "tasks": docs[2]["task_count"],
                          "families": len(docs[2]["independent_families"]),
                          "confirmatory_sealed": False, "out": str(args.out)}))
        return 0
    except (BenchmarkError, OSError, ValueError, KeyError, TypeError,
            relation_binding.decision.DecisionError,
            relation_registry.RegistryError) as exc:
        print(f"restatement benchmark: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
