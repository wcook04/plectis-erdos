#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial checks for the exact Lean dependency-index check receipt."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MODULE_PATH = ROOT / "scripts" / "build_lean_dependency_index.py"
SPEC = importlib.util.spec_from_file_location(
    "build_lean_dependency_index",
    MODULE_PATH,
)
assert SPEC is not None and SPEC.loader is not None
builder = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(builder)


def sha256_text(content: str) -> str:
    return f"sha256:{hashlib.sha256(content.encode('utf-8')).hexdigest()}"


def check_exact_receipt_contract() -> None:
    input_fingerprint = "sha256:input"
    output_digest = "sha256:output"
    receipt = {
        "schema": builder.CHECK_RECEIPT_SCHEMA,
        "builder_schema": builder.SCHEMA,
        "input_fingerprint": input_fingerprint,
        "output_digest": output_digest,
    }
    assert builder.receipt_matches(
        receipt,
        input_fingerprint=input_fingerprint,
        output_digest=output_digest,
    )
    mutations = (
        ("schema", "wrong"),
        ("builder_schema", "wrong"),
        ("input_fingerprint", "sha256:changed"),
        ("output_digest", "sha256:changed"),
    )
    for field, value in mutations:
        changed = {**receipt, field: value}
        assert not builder.receipt_matches(
            changed,
            input_fingerprint=input_fingerprint,
            output_digest=output_digest,
        ), field


def check_live_input_surface() -> None:
    paths = builder.check_input_paths()
    relative = {path.relative_to(ROOT).as_posix() for path in paths}
    assert set(builder.CHECK_INPUT_FILES).issubset(relative)
    for library_root in builder.LEAN_ROOT_TARGETS:
        assert f"{library_root}.lean" in relative
        assert any(
            name.startswith(f"{library_root}/") and name.endswith(".lean")
            for name in relative
        )
    assert len(paths) == len(set(paths))
    assert "docs/claims.json" not in relative
    assert "scripts/query_corpus.py" not in relative
    semantic_identities = {
        identity for identity, _payload in builder.semantic_check_inputs()
    }
    assert semantic_identities == {
        "docs/claims.json::release.formal_source",
        "scripts/query_corpus.py::dependency_helpers",
    }
    assert builder.check_input_fingerprint().startswith("sha256:")


def check_cached_output_rejection() -> None:
    with tempfile.TemporaryDirectory() as directory:
        temporary_root = Path(directory)
        output = temporary_root / "index.json"
        receipt_path = temporary_root / "receipt.json"
        output.write_text('{"current":true}\n', encoding="utf-8")
        fingerprint = builder.check_input_fingerprint()
        receipt = {
            "schema": builder.CHECK_RECEIPT_SCHEMA,
            "builder_schema": builder.SCHEMA,
            "input_fingerprint": fingerprint,
            "output_digest": sha256_text(output.read_text(encoding="utf-8")),
        }
        receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
        assert builder.load_cached_check(
            root=ROOT,
            output=output,
            receipt_path=receipt_path,
        ) == receipt
        output.write_text('{"current":false}\n', encoding="utf-8")
        assert builder.load_cached_check(
            root=ROOT,
            output=output,
            receipt_path=receipt_path,
        ) is None


def check_receipt_uses_verified_snapshot() -> None:
    with tempfile.TemporaryDirectory() as directory:
        receipt_path = Path(directory) / "receipt.json"
        packet = {
            "source_fingerprint": "sha256:source",
            "coverage": {
                "source_resolved_node_count": 2,
                "source_resolved_direct_edge_count": 3,
            },
        }
        builder.write_check_receipt(
            '{"packet":true}\n',
            packet,
            input_fingerprint="sha256:verified-at-start",
            receipt_path=receipt_path,
        )
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        assert receipt["input_fingerprint"] == "sha256:verified-at-start"


def main() -> int:
    check_exact_receipt_contract()
    check_live_input_surface()
    check_cached_output_rejection()
    check_receipt_uses_verified_snapshot()
    print("lean dependency index cache: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
